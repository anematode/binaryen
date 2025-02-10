
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

    // Now interleave all of double_resolved, int_resolved, float_resolved into void_resolved,
    // in that order (reversed below since we're inserting 1 by 1)
    for (int i = 0; i < base.max_insn; ++i) {
      base.void_resolved.insert(base.void_resolved.begin() + i * 4 + 1,
        { base.double_resolved[i], base.int_resolved[i], base.float_resolved[i] });
    }

    // Ok, now construct four typed function reference tables, joined into one
    Builder builder(*module);

    // Use the types of nop_impl_void, nop_impl_double, nop_impl_int, nop_impl_float

    Function *void_tmpl = module->getFunction("nop_impl_void");

    if (!void_tmpl) {
      Fatal() << "Missing one of the nop_impl functions";
    }

    auto make_tbl = [&] (const char* name, Function *tmpl, const std::vector<Expression*>& resolved) -> Name {
      Name tbl_name = name;
      std::unique_ptr<Table> tbl = builder.makeTable(
      tbl_name, Type(tmpl->type, NonNullable),
      base.max_insn * 4, base.max_insn * 4, Type::i32, resolved[0]);

      std::unique_ptr<ElementSegment> seg = builder.makeElementSegment(
        Names::getValidElementSegmentName(*module, Name::fromInt(0)),
        tbl->name, builder.makeConst(int32_t(0)), Type(tmpl->type, NonNullable));

      for (int i = 0; i < base.max_insn * 4; i++) {
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

    auto* runner = getPassRunner();

    struct RewriteCalls : WalkerPass<PostWalker<RewriteCalls>> {
      const Name& void_tbl;
      Function* void_tmpl;
      int max_insn;

      std::array<Name, 5> intrinsics;

      RewriteCalls(const Name& void_tbl,
                   Function* void_tmpl,
                   int max_insn,
                   Importable* intrinsic_next_void,
                    Importable* intrinsic_next_double,
                    Importable* intrinsic_next_int,
                    Importable* intrinsic_next_float,
                    Importable* intrinsic_next_polymorphic
                   ) : void_tbl(void_tbl),
                                            void_tmpl(void_tmpl), max_insn(max_insn) {
        intrinsics[0] = intrinsic_next_void->name;
        intrinsics[1] = intrinsic_next_double->name;
        intrinsics[2] = intrinsic_next_int->name;
        intrinsics[3] = intrinsic_next_float->name;
        intrinsics[4] = intrinsic_next_polymorphic->name;
      }
      void visitReturn(Return* return_) {
        // If the contents are a return_call_indirect due to a visitCall pass,
        // replace it with the contents.
        if (return_->value && return_->value->is<CallIndirect>()) {
          CallIndirect *c = return_->value->cast<CallIndirect>();
          if (c->table == void_tbl && c->isReturn) {
            replaceCurrent(return_->value);
          }
        }
      }

      void visitCall(Call* call) {
        // Skip when in functions not containing "_impl_" in their name

        size_t index = std::find(intrinsics.begin(), intrinsics.end(), call->target) - intrinsics.begin();
        if (index == intrinsics.size()) { // not found
          return;
        }

        bool polymorphic = index == 4;

        // Two cases. In polymorphic case, compute the next instruction * 4 + instruction.tos_before. In
        // non-polymorphic case, add the known TOS.
        Expression* inst_pointer = call->operands[2];

        Builder builder(*getModule());

        // Tee to a local so that we don't recompute it (could have side effects).
        Index inst_local = builder.addVar(getFunction(), Type::BasicType::i32);
        int offsetof_kind = 0;
        int offsetof_tos_before = 2;

        call->operands[2] = builder.makeLocalTee(inst_local, inst_pointer, Type::BasicType::i32);

        Expression *get_inst = builder.makeLocalGet(inst_local, Type::BasicType::i32);


        auto memory = getModule()->memories[0]->name;
        Expression* kind = builder.makeLoad(1, false, offsetof_kind, 1,
          get_inst, Type::BasicType::i32, memory);

        Expression* tos_before = polymorphic ?
          (Expression*)builder.makeLoad(1, false, offsetof_tos_before, 1,
            get_inst, Type::BasicType::i32, memory) :
          (Expression*)builder.makeConst(Literal((int)index));

        // kind * 4 + tos_before
        Expression* indirect_index = builder.makeBinary(AddInt32, tos_before,
          builder.makeBinary(MulInt32, kind, builder.makeConst(Literal(4))));

        Name table = void_tbl;
        HeapType type = void_tmpl->type;

        bool make_return = getFunction()->name.str.find("_impl") != std::string::npos;
        replaceCurrent(builder.makeCallIndirect(
          table, indirect_index, call->operands, type, make_return));
      }
    };

    int max_insn = base.max_insn;
    Importable* intrinsic_next_void = module->getFunction("__interpreter_intrinsic_next_void");
    Importable* intrinsic_next_double = module->getFunction("__interpreter_intrinsic_next_double");
    Importable* intrinsic_next_float = module->getFunction("__interpreter_intrinsic_next_float");
    Importable* intrinsic_next_int = module->getFunction("__interpreter_intrinsic_next_int");
    Importable* intrinsic_next_polymorphic = module->getFunction("__interpreter_intrinsic_next_polymorphic");

    RewriteCalls(void_tbl, void_tmpl, max_insn, intrinsic_next_void,
      intrinsic_next_double, intrinsic_next_int, intrinsic_next_float,
      intrinsic_next_polymorphic).run(runner, module);

    for (int i = 0; i < (int)module->functions.size(); ++i) {
      auto &fn = module->functions[i];
      if (fn->base.startsWith("__interpreter_intrinsic")) {
        module->removeFunction(fn->name);
        --i;
      }
    }
  }
};

}

Pass* createConstructInterpreterTablesPass() {
  return new ConstructInterpreterTables();
}

}