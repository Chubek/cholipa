#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define MAX_CONST 256
#define INIT_STACK_SIZE 65536
#define MAX_AST_CHILD 128
#define MAX_ID_LENGTH 64

#define RAISE(msg, ...)                                                        \
  do {                                                                         \
    fprintf(stderr, msg, __VA_ARGS__);                                         \
    fprintf(stderr, "\n");                                                     \
    exit(EXIT_FAILURE);                                                        \
  } while (0)

typedef struct Operand operand_t;
typedef struct AST ast_node_t;
typedef struct Closure closure_t;
typedef struct Intrin intrin_t;
typedef struct Environ environ_t;
typedef uint32_t tag_t;

typedef enum {
  OP_LOAD_INT,
  OP_LOAD_REAL,
  OP_LOAD_STRING,

  OP_NEGATE,
  OP_BITNOT,
  OP_LENGTH,
  OP_COMPLEMENT,

  OP_ADD,
  OP_SUB,
  OP_MUL,
  OP_DIV,
  OP_MOD,
  OP_POW,

  OP_SHR,
  OP_SHL,
  OP_BITAND,
  OP_BITOR,
  OP_BITXOR,

  OP_DISJ,
  OP_CONJ,

  OP_EQ,
  OP_NE,
  OP_LT,
  OP_GT,
  OP_LE,
  OP_GE,

  OP_LOAD_VAR,
  OP_STORE_VAR,
  OP_DECLARE_VAR,

  OP_JMP,
  OP_JMPZ,
  OP_JMPNZ,

  OP_CALL,
  OP_TAILCALL,
  OP_RETURN,

  OP_INCR,
  OP_DECR,

  OP_INTRIN,
  OP_CLOSE_START,
  OP_CLOSE_END,

  OP_HALT,
} code_t;

struct Operand {
  enum OperandType {
    OPR_Integer,
    OPR_Real,
    OPR_String,
    OPR_Closure,
    OPR_Intrin,
  } type;

  union {
    intmax_t v_integer;
    long double v_real;
    const uint8_t *v_string;
    closure_t *v_closure;
    intrin_t *v_intrin;
  };

  ssize_t num_refs;
};

typedef struct Symbol {
  const char *name;
  operand_t *value;
  syminfo_t *info;
  struct Symbol *next;
} symbol_t;

typedef struct Symtable {
  Symbol **buckets;
  size_t size;
  size_t count;
} symtable_t;

typedef struct Environ {
  symtable_t *symbols_table;
  struct Environ *parent;
} environ_t;

typedef struct Variable {
  const char *name;
  operand_t *value;
} variable_t;

typedef struct Upvalue {
  Variable *on_stack;
  bool is_closed;
  struct Upvalue *next;
} upval_t;

typedef struct Function {
  const char *name;
  const char **params;
  size_t num_params;
  ast_node_t *body;
} function_t;

typedef struct UnaryOp {
  enum UnaryOperator {
    UNOP_Negate,
    UNOP_Complement,
    UNOP_BitNot,
    UNOP_Length,
  }
  operator;

  ast_node_t *operand;
} unaryop_t;

typedef struct BinaryOp {
  enum BinaryOperator {
    BINOP_Add,
    BINOP_Sub,
    BINOP_Mul,
    BINOP_Div,
    BINOP_Mod,
    BINOP_Pow,
    BINOP_Shr,
    BINOP_Shl,
    BINOP_Disj,
    BINOP_Conj,
    BINOP_BitAnd,
    BINOP_BitXor,
    BINOP_BitOr,
  }
  operator;

  bool is_inplace;
  ast_node_t *lhs;
  ast_node_t *rhs;
} binaryop_t;

typedef struct Label {
  const char *name;
  size_t line_no;
} label_t;

typedef struct AssignVal {
  const char **rhs;
  size_t num_rhs;
  ast_node_t **lhs;
  size_t num_lhs;
} assign_t;

typedef struct DeclareVal {
  const char **vars;
  size_t num_vars;
} decl_t;

typedef struct Closure {
  const char **params;
  size_t num_params;
  ast_node_t *body;
} closure_t;

typedef struct Call {
  const char *prefix_name;
  const ast_node_t **arguments;
  size_t num_args;
  bool is_tail;
} call_t;

typedef struct Loop {
  enum LoopKind {
    LOOP_For,
    LOOP_Repeat,
    LOOP_While,
    LOOP_Until,
  } kind;

  ast_node_t *start;
  ast_node_t *end;
  ast_node_t *step;
  ast_node_t *body;
} loop_t;

typedef struct Relop {
  enum RelOpKind {
    LT,
    LE,
    GT,
    GE,
    EQ,
    NE,
  }
  operator;

  ast_node_t *lexpr;
  ast_node_t *rexpr;
} relop_t;

typedef struct CondPair {
  ast_node_t *cond;
  ast_node_t *body;
} cond_pair_t;

typedef struct IfCond {
  cond_pair_t *main;
  cond_pair_t *elifs;
  ast_node_t *els;
  bool is_unless;
} if_cond_t;

typedef struct SwitchCond {
  ast_node_t *discrim;
  cond_pair_t *switches;
  ast_node_t *dfl_case;
} switch_cond_t;

typedef struct Cond {
  enum CondKind {
    COND_If,
    COND_Unless,
    COND_Switch,
  } kind;

  union {
    if_cond_t *v_if;
    switch_cond_t *v_switch;
  };
} cond_t;

struct AST {
  enum ASTKind {
    LEAF_Identifier,
    LEAF_String,
    LEAF_Integer,
    LEAF_Real,
    LEAF_UnaryOp,
    LEAF_BinaryOp,
    LEAF_RelOp,
    LEAF_AssignVal,
    LEAF_DeclareVal,
    LEAF_Label,
    LEAF_Goto,
    LEAF_Closure,
    LEAF_Function,
    LEAF_Call,
    LEAF_Loop,
    LEAF_Cond,
    LEAF_Argnum,
  } kind;

  union {
    function_t *v_function;
    closure_t *v_closure;
    cond_t *v_cond;
    loop_t *v_loop;
    call_t *v_call;
    label_t *v_label;
    binaryop_t *v_binop;
    unaryop_t *v_unrop;
    assign_t *v_assign;
    decl_t *v_delcl;
    relop_t *v_relop;
    size_t v_index;
    intmax_t v_integer;
    long double v_real;
    const char v_identifier[MAX_ID_LENGTH + 1];
    const uint8_t *v_string;
  };

  tag_t tag;
  bool visited;
  const struct AST *next;
  const struct AST *prev;
};

struct Closure {
  size_t address;
  environ_t *env;
};

typedef struct Region {
  size_t size;
  size_t used;
  char mem[];
} region_t;

region_t *new_region(size_t size) {
  region_t *reg = calloc(1, size);
  reg->size = size - (sizeof(size_t) * 2);
  reg->used = 0;
  return reg;
}

void *request_memory(region_t *reg, size_t size) {
  if (reg->size - reg->used < size)
    RAISE("Memory region exhausted (size: %lu)", reg->size);

  void *mem = (void *)reg->mem[reg->used];
  reg->used += size + 1;

  return mem;
}

void init_stacks(void) {
  Stack.operands =
      request_memory(curr_arena, INIT_STACK_SIZE * sizeof(operand_t));
  Stack.capacity = INIT_STACK_SIZE;
  Stack.pointer = 0;
  Stack.frame = 0;
  memset(&Stack.constants[0], 0, MAX_CONST * sizeof(operand_t));

  Tape.codes = request_memory(curr_arena, INIT_STACK_SIZE * sizeof(code_t));
  Tape.codes_num = 0;
  Tape.pointer = 0;
  Tape.capacity = INIT_STACK_SIZE;
}

void grow_operand_stack(void) {
  size_t new_size = Stack.capacity * 2;
  operand_t *new_scratch =
      request_memory(curr_arena, new_size * sizeof(operand_t));

  memmove(new_scratch, Stack.operands, Stack.capacity * sizeof(operand_t));
  free(Stack.operands);

  Stack.operands = new_scratch;
  Stack.capacity = new_size;
}

void grow_tape(void) {
  size_t new_size = Tape.capacity * 2;
  code_t *new_scratch = request_memory(curr_arena, new_size * sizeof(code_t));

  memmove(new_scratch, Tape.codes, Tape.capacity * sizeof(code_t));
  free(Tape.codes);

  Tape.codes = new_scratch;
  Tape.capacity = new_size;
}

void push_integer_operand(intmax_t value) {
  if (Stack.pointer == Stack.capacity - 1)
    grow_operand_stack();

  Stack.operands[Stack.pointer++] =
      (operand_t){.type = OPR_Integer, .v_integer = value};
}

intmax_t pop_integer_operand(void) {
  if (Stack.operands[Stack.pointer - 1].type != OPR_Integer)
    RAISE("Wrong value requested from stack", NULL);

  return Stack.operands[--Stack.pointer].v_integer;
}

void push_real_operand(long double value) {
  if (Stack.pointer == Stack.capacity - 1)
    grow_operand_stack();

  Stack.operands[Stack.pointer++] =
      (operand_t){.type = OPR_Real, .v_real = value};
}

long double pop_real_operand(void) {
  if (Stack.operands[Stack.pointer - 1].type != OPR_Real)
    RAISE("Wrong value requested from stack", NULL);

  return Stack.operands[--Stack.pointer].v_real;
}

void push_string_operand(const uint8_t *value) {
  if (Stack.pointer == Stack.capacity - 1)
    grow_operand_stack();

  Stack.operands[Stack.pointer++] =
      (operand_t){.type = OPR_String, .v_string = value};
}

const uint8_t *pop_string_operand(void) {
  if (Stack.operands[Stack.pointer - 1].type != OPR_String)
    RAISE("Wrong value requested from stack", NULL);

  return Stack.operands[--Stack.pointer].v_string;
}

void set_integer_const(intmax_t value, size_t index) {
  if (index >= MAX_CONST)
    RAISE("Constant out of range (max %d)", MAX_CONST);

  Stack.constants[index] = (operand_t){.type = OPR_Integer, .v_integer = value};
}

void set_real_const(long double value, size_t index) {
  if (index >= MAX_CONST)
    RAISE("Constant out of range (max %d)", MAX_CONST);

  Stack.constants[index] = (operand_t){.type = OPR_Real, .v_real = value};
}

void set_string_const(const uint8_t *value, size_t index) {
  if (index >= MAX_CONST)
    RAISE("Constant out of range (max %d)", MAX_CONST);

  Stack.constants[index] = (operand_t){.type = OPR_String, .v_string = value};
}

operand_t *get_const(size_t index) {
  if (index >= MAX_CONST)
    RAISE("Constant out of range (max %d)", MAX_CONST);

  return &Stack.constants[index];
}

void tape_write_code(code_t code) {
  if (Tape.codes_num + 1 == Tape.capacity)
    grow_tape();

  Tape.codes[Tape.codes_num++] = code;
}

code_t tape_read_code(void) { return Tape.codes[++Tape.pointer]; }

void tape_set_head(size_t head) { Tape.pointer = head; }

ast_node_t *ast_create_binaryop(ast_node_t *absyn, enum BinaryOperator operator,
                                bool is_inplace, ast_node_t *lhs,
                                ast_node_t *rhs) {
  ast_node_t *new_binop = request_memory(curr_arena, sizeof(ast_node_t));

  new_binop->kind = LEAF_BinaryOp;
  new_binop->v_binop = request_memory(curr_arena, sizeof(binaryop_t));
  new_binop->v_binop->operator= operator;
  new_binop->v_binop->is_inplace = is_inplace;
  new_binop->v_binop->lhs = lhs;
  new_binop->v_binop->rhs = rhs;

  ast_append_leaf(absyn, new_binop);

  return new_binop;
}

ast_node_t *ast_create_relop(ast_node_t *absyn, enum RelOpKind operator,
                             ast_node_t * lexpr, ast_node_t *rexpr) {
  ast_node_t *new_relop = request_memory(curr_arena, sizeof(ast_node_t));

  new_relop->kind = LEAF_RelOp;
  new_relop->v_relop = request_memory(curr_arena, sizeof(relop_t));
  new_relop->v_relop->operator= operator;
  new_relop->v_relop->lexpr = lexpr;
  new_relop->v_relop->rexpr = rexpr;

  ast_append_leaf(absyn, new_relop);

  return new_relop;
}

ast_node_t *ast_create_unaryop(ast_node_t *absyn, enum UnaryOperator operator,
                               ast_node_t * operand) {
  ast_node_t *new_unop = request_memory(curr_arena, sizeof(ast_node_t));

  new_unop->kind = LEAF_UnaryOp;
  new_unop->v_unrop = request_memory(curr_arena, sizeof(unaryop_t));
  new_unop->v_unrop->operator= operator;
  new_unop->v_unrop->operand = operand;

  ast_append_leaf(absyn, new_unop);

  return new_unop;
}

ast_node_t *ast_create_label(ast_node_t *absyn, const char *name,
                             size_t line_no) {
  ast_node_t *new_label = request_memory(curr_arena, sizeof(ast_node_t));

  new_label->kind = LEAF_Label;
  new_label->v_label = request_memory(curr_arena, sizeof(label_t));
  new_label->v_label->name = name;
  new_label->v_label->line_no = line_no;

  ast_append_leaf(absyn, new_label);

  return new_label;
}

ast_node_t *ast_create_function(ast_node_t *absyn, const char *name,
                                const char **params, size_t num_params,
                                ast_node_t *body) {
  ast_node_t *new_function = request_memory(curr_arena, sizeof(ast_node_t));

  new_function->kind = LEAF_Function;
  new_function->v_function = request_memory(curr_arena, sizeof(function_t));
  new_function->v_function->name = name;
  new_function->v_function->params = params;
  new_function->v_function->num_params = num_params;
  new_function->v_function->body = body;

  ast_append_leaf(absyn, new_function);

  return new_function;
}

cond_pair_t *create_cond_pair(ast_node_t *cond, ast_node_t *body) {
  cond_pair_t *pair = request_memory(curr_arena, sizeof(cond_pair_t));
  pair->cond = cond;
  pair->body = body;
  return pair;
}

ast_node_t *ast_create_if_cond(ast_node_t *absyn, cond_pair_t *main_cond,
                               cond_pair_t *elifs, ast_node_t *els,
                               bool is_unless) {
  ast_node_t *new_cond = request_memory(curr_arena, sizeof(ast_node_t));

  new_cond->kind = LEAF_Cond;
  new_cond->v_cond = request_memory(curr_arena, sizeof(cond_t));
  new_cond->v_cond->kind = COND_If;

  new_cond->v_cond->v_if = request_memory(curr_arena, sizeof(if_cond_t));
  new_cond->v_cond->v_if->main = main_cond;
  new_cond->v_cond->v_if->elifs = elifs;
  new_cond->v_cond->v_if->els = els;
  new_cond->v_cond->v_if->is_unless = is_unless;

  ast_append_leaf(absyn, new_cond);

  return new_cond;
}

ast_node_t *ast_create_switch_cond(ast_node_t *absyn, ast_node_t *discrim,
                                   cond_pair_t *switches,
                                   ast_node_t *dfl_case) {
  ast_node_t *new_cond = request_memory(curr_arena, sizeof(ast_node_t));

  new_cond->kind = LEAF_Cond;
  new_cond->v_cond = request_memory(curr_arena, sizeof(cond_t));
  new_cond->v_cond->kind = COND_Switch;

  new_cond->v_cond->v_switch =
      request_memory(curr_arena, sizeof(switch_cond_t));
  new_cond->v_cond->v_switch->discrim = discrim;
  new_cond->v_cond->v_switch->switches = switches;
  new_cond->v_cond->v_switch->dfl_case = dfl_case;

  ast_append_leaf(absyn, new_cond);

  return new_cond;
}

ast_node_t *ast_create_loop(ast_node_t *absyn, enum LoopKind kind,
                            ast_node_t *start, ast_node_t *end,
                            ast_node_t *step, ast_node_t *body) {
  ast_node_t *new_loop = request_memory(curr_arena, sizeof(ast_node_t));

  new_loop->kind = LEAF_Loop;
  new_loop->v_loop = request_memory(curr_arena, sizeof(loop_t));
  new_loop->v_loop->kind = kind;
  new_loop->v_loop->start = start;
  new_loop->v_loop->end = end;
  new_loop->v_loop->step = step;
  new_loop->v_loop->body = body;

  ast_append_leaf(absyn, new_loop);

  return new_loop;
}

ast_node_t *ast_create_call(ast_node_t *absyn, const char *prefix_name,
                            const ast_node_t **arguments, size_t num_args,
                            bool is_tail) {
  ast_node_t *new_call = request_memory(curr_arena, sizeof(ast_node_t));

  new_call->kind = LEAF_Call;
  new_call->v_call = request_memory(curr_arena, sizeof(call_t));
  new_call->v_call->prefix_name = prefix_name;
  new_call->v_call->arguments = arguments;
  new_call->v_call->num_args = num_args;
  new_call->v_call->is_tail = is_tail;

  ast_append_leaf(absyn, new_call);

  return new_call;
}

ast_node_t *ast_create_declare(ast_node_t *absyn, const char **vars,
                               size_t num_vars) {
  ast_node_t *new_declare = request_memory(curr_arena, sizeof(ast_node_t));

  new_declare->kind = LEAF_DeclareVal;
  new_declare->v_delcl = request_memory(curr_arena, sizeof(decl_t));
  new_declare->v_delcl->vars = vars;
  new_declare->v_delcl->num_vars = num_vars;

  ast_append_leaf(absyn, new_declare);

  return new_declare;
}

ast_node_t *ast_create_assign(ast_node_t *absyn, const char **rhs,
                              size_t num_rhs, ast_node_t **lhs,
                              size_t num_lhs) {
  ast_node_t *new_assign = request_memory(curr_arena, sizeof(ast_node_t));

  new_assign->kind = LEAF_AssignVal;
  new_assign->v_assign = request_memory(curr_arena, sizeof(assign_t));
  new_assign->rhs = rhs;
  new_assign->rhs_num = rhs_num;
  new_assign->lhs = lhs;
  new_assign->lhs_num = lhs_num;

  ast_append_leaf(absyn, new_assign);

  return new_assign;
}

ast_node_t *ast_create_integer(ast_node_t *absyn, intmax_t value) {
  ast_node_t *new_int = request_memory(curr_arena, sizeof(ast_node_t));

  new_int->kind = LEAF_Integer;
  new_int->v_integer = value;

  ast_append_leaf(absyn, new_int);

  return new_int;
}

ast_node_t *ast_create_real(ast_node_t *absyn, long double value) {
  ast_node_t *new_real = request_memory(curr_arena, sizeof(ast_node_t));

  new_real->kind = LEAF_Real;
  new_real->v_real = value;

  ast_append_leaf(absyn, new_real);

  return new_real;
}

ast_node_t *ast_create_real(ast_node_t *absyn, long double value) {
  ast_node_t *new_real = request_memory(curr_arena, sizeof(ast_node_t));

  new_real->kind = LEAF_Real;
  new_real->v_real = value;

  ast_append_leaf(absyn, new_real);

  return new_real;
}

void ast_append_leaf(ast_node_t *absyn, ast_node_t *new_leaf) {
  if (absyn == NULL) {
    return;
  }

  if (absyn->next == NULL) {
    absyn->next = new_leaf;
    new_leaf->prev = absyn;
  } else {
    ast_node_t *last = absyn;
    while (last->next != NULL) {
      last = last->next;
    }

    last->next = new_leaf;
    new_leaf->prev = last;
  }

  new_leaf->visited = false;
}
