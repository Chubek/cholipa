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
typedef int code_t;
typedef uint32_t tag_t;

struct Operand {
  enum OperandType {
    OP_Integer,
    OP_Real,
    OP_String,
  } type;

  union {
    intmax_t v_integer;
    long double v_real;
    const uint8_t *v_string;
  };

  ssize_t no_refs;
};

static struct {
  operand_t *operands;
  operand_t constants[MAX_CONST];
  size_t capacity;
  size_t pointer;
  size_t frame;
} Stack;

static struct {
  code_t *codes;
  size_t codes_num;
  size_t pointer;
  size_t capacity;
} Tape;

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
    relop_t *v_relop;
    size_t v_index;
    intmax_t v_integer;
    long double v_real;
    const char v_identifier[MAX_ID_LENGTH + 1];
    const uint8_t *v_string;
  };

  const tag_t tag;
  bool visited;
  const struct AST *next;
};

void init_stacks(void) {
  Stack.operands = calloc(INIT_STACK_SIZE, sizeof(operand_t));
  Stack.capacity = INIT_STACK_SIZE;
  Stack.pointer = 0;
  Stack.frame = 0;
  memset(&Stack.constants[0], 0, MAX_CONST * sizeof(operand_t));

  Tape.codes = calloc(INIT_STACK_SIZE, sizeof(code_t));
  Tape.codes_num = 0;
  Tape.pointer = 0;
  Tape.capacity = INIT_STACK_SIZE;
}

void destroy_stacks(void) {
  free(Tape.codes);
  free(Stack.operands);
}

void grow_operand_stack(void) {
  size_t new_size = Stack.capacity * 2;
  operand_t *new_scratch = calloc(new_size, sizeof(operand_t));

  memmove(new_scratch, Stack.operands, Stack.capacity * sizeof(operand_t));
  free(Stack.operands);

  Stack.operands = new_scratch;
  Stack.capacity = new_size;
}

void grow_tape(void) {
  size_t new_size = Tape.capacity * 2;
  code_t *new_scratch = calloc(new_size, sizeof(code_t));

  memmove(new_scratch, Tape.codes, Tape.capacity * sizeof(code_t));
  free(Tape.codes);

  Tape.codes = new_scratch;
  Tape.capacity = new_size;
}

void push_integer_operand(intmax_t value) {
  if (Stack.pointer == Stack.capacity - 1)
    grow_operand_stack();

  Stack.operands[Stack.pointer++] =
      (operand_t){.type = OP_Integer, .v_integer = value};
}

intmax_t pop_integer_operand(void) {
  if (Stack.operands[Stack.pointer - 1].type != OP_Integer)
    RAISE("Wrong value requested from stack", NULL);

  return Stack.operands[--Stack.pointer].v_integer;
}

void push_real_operand(long double value) {
  if (Stack.pointer == Stack.capacity - 1)
    grow_operand_stack();

  Stack.operands[Stack.pointer++] =
      (operand_t){.type = OP_Real, .v_real = value};
}

long double pop_real_operand(void) {
  if (Stack.operands[Stack.pointer - 1].type != OP_Real)
    RAISE("Wrong value requested from stack", NULL);

  return Stack.operands[--Stack.pointer].v_real;
}

void push_string_operand(const uint8_t *value) {
  if (Stack.pointer == Stack.capacity - 1)
    grow_operand_stack();

  Stack.operands[Stack.pointer++] =
      (operand_t){.type = OP_String, .v_string = value};
}

const uint8_t *pop_string_operand(void) {
  if (Stack.operands[Stack.pointer - 1].type != OP_String)
    RAISE("Wrong value requested from stack", NULL);

  return Stack.operands[--Stack.pointer].v_string;
}

void set_integer_const(intmax_t value, size_t index) {
  if (index >= MAX_CONST)
    RAISE("Constant out of range (max %d)", MAX_CONST);

  Stack.constants[index] = (operand_t){.type = OP_Integer, .v_integer = value};
}

void set_real_const(long double value, size_t index) {
  if (index >= MAX_CONST)
    RAISE("Constant out of range (max %d)", MAX_CONST);

  Stack.constants[index] = (operand_t){.type = OP_Real, .v_real = value};
}

void set_string_const(const char *value, size_t index) {
  if (index >= MAX_CONST)
    RAISE("Constant out of range (max %d)", MAX_CONST);

  Stack.constants[index] = (operand_t){.type = OP_String, .v_string = value};
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
