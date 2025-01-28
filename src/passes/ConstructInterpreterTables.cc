
#include <stdint.h>

#include "ir/export-utils.h"
#include "ir/find_all.h"
#include "ir/lubs.h"
#include "ir/module-utils.h"
#include "ir/names.h"
#include "ir/utils.h"
#include "pass.h"
#include "wasm-type.h"
#include "wasm.h"

namespace wasm {

namespace {

struct TblInfo {
  int void_base;
  int double_base;
  int int_base;
  int float_base;

  std::vector<uint32_t> void_tbl;
  std::vector<uint32_t> double_tbl;
  std::vector<uint32_t> int_tbl;
  std::vector<uint32_t> float_tbl;

  std::vector<Expression*> void_resolved;
  std::vector<Expression*> double_resolved;
  std::vector<Expression*> int_resolved;
  std::vector<Expression*> float_resolved;

  int max_insn;
};

bool intervals_overlap(const std::pair<int, int>& a, const std::pair<int, int>& b) {
  return a.first < b.second && b.first < a.second;
}

void fill_range(int int_base, std::vector<uint32_t>& vector, int offset_val, const std::vector<char>& data) {
  // Look for overlapping region in data, then copy into vector
  if (intervals_overlap({int_base, int_base + 4 * vector.size()}, {offset_val, offset_val + data.size()})) {
    int delta = offset_val - int_base;
    char *copy_to = (char*)vector.data() + std::max(delta, 0);
    const char *copy_from = data.data() + std::max(-delta, 0);
    size_t copy_size = std::min(vector.size() * 4 - std::max(delta, 0), data.size() - std::max(-delta, 0));
    memcpy(copy_to, copy_from, copy_size);
  }
}

void fill_ranges(TblInfo& base, int offset_val, const std::vector<char>& data) {
  fill_range(base.int_base, base.int_tbl, offset_val, data);
  fill_range(base.float_base, base.float_tbl, offset_val, data);
  fill_range(base.double_base, base.double_tbl, offset_val, data);
  fill_range(base.void_base, base.void_tbl, offset_val, data);
}

void resolve_for(const std::vector<uint32_t>& tbl, std::vector<Expression*>& resolved, const std::vector<Expression*>& data) {
  for (size_t i = 0; i < tbl.size(); i++) {
    if (tbl[i] == 0) {
      resolved.push_back(nullptr);
      continue;
    }

    Expression *expr = data.at(tbl[i] - 1);
    std::cout << *expr << '\n';
    resolved.push_back(expr);
  }
}

void resolve_exprs(TblInfo& base, const std::vector<Expression*>& data) {
  resolve_for(base.void_tbl, base.void_resolved, data);
  resolve_for(base.double_tbl, base.double_resolved, data);
  resolve_for(base.int_tbl, base.int_resolved, data);
  resolve_for(base.float_tbl, base.float_resolved, data);
}

// Look for all call_indirect or return_call_indirect to one of the interpreter
// intrinsics
struct ConstructInterpreterTables : public Pass {
  void run(Module* module) override {
    TblInfo base;

    auto locate_info = [&] (int* tbl, const char* name) {
      Function *f = module->getFunction(name);
      if (!f) {
        Fatal() << "Missing " << name;
      }
      // Body should consist of a single i32.const insn containing the pointer
      // into .rodata
      Expression *body = f->body;
      if (!body->is<Const>() || body->type != Type::i32) {
        Fatal() << "Body of " << name << " should be a single i32.const";
      }
      *tbl = body->cast<Const>()->value.geti32();
    };

    locate_info(&base.void_base, "__interpreter_intrinsic_void_table_base");
    locate_info(&base.double_base, "__interpreter_intrinsic_double_table_base");
    locate_info(&base.int_base, "__interpreter_intrinsic_int_table_base");
    locate_info(&base.float_base, "__interpreter_intrinsic_float_table_base");

    locate_info(&base.max_insn, "__interpreter_intrinsic_max_insn");

    base.void_tbl.resize(base.max_insn);
    base.double_tbl.resize(base.max_insn);
    base.int_tbl.resize(base.max_insn);
    base.float_tbl.resize(base.max_insn);

    for (const auto& segment : module->dataSegments) {
      Expression *offset = segment->offset;
      if (!offset->is<Const>() || offset->type != Type::i32) {
        Fatal() << "Data segment offset should be a single i32.const";
      }

      int offset_val = offset->cast<Const>()->value.geti32();
      fill_ranges(base, offset_val, segment->data);
    }

    // Now look for the main list of elements
    if (module->elementSegments.size() != 1) {
      Fatal() << "Expected a single element segment";
    }

    if (module->elementSegments[0]->offset->cast<Const>()->value.geti32() != 1) {
      Fatal() << "Expected element segment offset to be 1";
    }

    resolve_exprs(base, module->elementSegments[0]->data);

    // Ok, now construct four typed function reference tables
    Builder builder(*module);

    // Use the types of nop_impl_void, nop_impl_double, nop_impl_int, nop_impl_float

    Function *void_tmpl = module->getFunction("nop_impl_void");
    Function *double_tmpl = module->getFunction("nop_impl_double");
    Function *int_tmpl = module->getFunction("nop_impl_int");
    Function *float_tmpl = module->getFunction("nop_impl_float");

    if (!void_tmpl || !double_tmpl || !int_tmpl || !float_tmpl) {
      Fatal() << "Missing one of the nop_impl functions";
    }

    auto make_tbl = [&] (const char* name, Function *tmpl, const std::vector<Expression*>& resolved) -> Name {
      Name tbl_name = name;
      std::unique_ptr<Table> tbl = builder.makeTable(
      tbl_name, Type(tmpl->type, NonNullable),
      base.max_insn, base.max_insn, Type::i32, resolved[0]);

      std::unique_ptr<ElementSegment> seg = builder.makeElementSegment(
        Names::getValidElementSegmentName(*module, Name::fromInt(0)),
        tbl->name, builder.makeConst(int32_t(0)), Type(tmpl->type, NonNullable));

      for (int i = 0; i < base.max_insn; i++) {
        Expression *expr = resolved.at(i);
        if (expr) {
          seg->data.push_back(expr);
        } else {
          seg->data.push_back(resolved.at(0));
        }
      }

      module->addTable(std::move(tbl));
      module->addElementSegment(std::move(seg));

      return name;
    };

    Name void_tbl = make_tbl("__interpreter_void_table", void_tmpl, base.void_resolved);
    Name double_tbl = make_tbl("__interpreter_double_table", double_tmpl, base.double_resolved);
    Name int_tbl = make_tbl("__interpreter_int_table", int_tmpl, base.int_resolved);
    Name float_tbl = make_tbl("__interpreter_float_table", float_tmpl, base.float_resolved);

    auto* runner = getPassRunner();

    struct RewriteCalls : WalkerPass<PostWalker<RewriteCalls>> {
      const Name& void_tbl;
     const Name& double_tbl;
     const Name& int_tbl;
     const Name& float_tbl;
     Function* void_tmpl;
     Function* double_tmpl;
     Function* int_tmpl;
     Function* float_tmpl;

      RewriteCalls(const Name& void_tbl,
                   const Name& double_tbl,
                   const Name& int_tbl,
                   const Name& float_tbl,
                   Function* void_tmpl,
                   Function* double_tmpl,
                   Function* int_tmpl,
                   Function* float_tmpl) : void_tbl(void_tbl),
                                            double_tbl(double_tbl),
                                            int_tbl(int_tbl),
                                            float_tbl(float_tbl),
                                            void_tmpl(void_tmpl),
                                            double_tmpl(double_tmpl),
                                            int_tmpl(int_tmpl),
                                            float_tmpl(float_tmpl) {}
      void visitCall(Call* call) {
        bool is_void = call->target == "__interpreter_intrinsic_next_void";
        bool is_double = call->target == "__interpreter_intrinsic_next_double";
        bool is_int = call->target == "__interpreter_intrinsic_next_int";
        bool is_float = call->target == "__interpreter_intrinsic_next_float";
        if (!is_void && !is_double && !is_int && !is_float) {
          return;
        }

        Expression* index = call->operands[call->operands.size() - 1];
        call->operands.pop_back();

        Name table = is_void     ? void_tbl
                     : is_double ? double_tbl
                     : is_int    ? int_tbl
                                 : float_tbl;
        HeapType type = is_void     ? void_tmpl->type
                        : is_double ? double_tmpl->type
                        : is_int    ? int_tmpl->type
                                    : float_tmpl->type;

        Builder builder(*getModule());
        // Check if current function contains "_impl_" and skip

        bool make_return = call->isReturn || getFunction()->name.str.find("_impl_") != std::string::npos;
        replaceCurrent(builder.makeCallIndirect(
          table, index, call->operands, type, make_return /* return */));
      }
    };

    RewriteCalls(void_tbl, double_tbl, int_tbl, float_tbl, void_tmpl, double_tmpl, int_tmpl, float_tmpl).run(runner, module);

    module->removeFunction("__interpreter_intrinsic_next_void");
    module->removeFunction("__interpreter_intrinsic_next_double");
    module->removeFunction("__interpreter_intrinsic_next_int");
    module->removeFunction("__interpreter_intrinsic_next_float");
  }
};

}

Pass* createConstructInterpreterTablesPass() {
  return new ConstructInterpreterTables();
}

}