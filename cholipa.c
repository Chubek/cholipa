#include <limits.h>
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
#define BUF_GROWTH_RATE 128

#define RAISE(msg, ...)                                                        \
  do {                                                                         \
    fprintf(stderr, msg, __VA_ARGS__);                                         \
    fprintf(stderr, "\n");                                                     \
    exit(EXIT_FAILURE);                                                        \
  } while (0)

typedef struct Operand operand_t;
typedef struct AST ast_node_t;
typedef uint32_t tag_t;

typedef enum {
  OP_LOAD_INT,
  OP_LOAD_REAL,
  OP_LOAD_STRING,
  OP_LOAD_CLOSURE,
  OP_LOAD_INTRIN,

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

typedef struct SourceLoc {
  size_t line;
  size_t column;
  const char file_name[PATH_MAX + 1];
} src_loc_t;

typedef struct ByteBuffer {
  uint8_t *bytes;
  size_t capcity;
  size_t length;
} byte_buf_t;

struct Operand {
  enum OperandType {
    OPR_Integer,
    OPR_Real,
    OPR_String,
    OPR_Closure,
    OPR_Intrin,
    OPR_Regexp,
  } type;

  union {
    intmax_t v_integer;
    long double v_real;
    byte_buf_t *v_string;
    closure_t *v_closure;
    intrin_t *v_intrin;
    regexp_t *v_regexp;
  };

  src_loc_t *loc_info;
  operand_t *next;
  operand_t *prev;
};

typedef struct Symbol {
  const byte_buf_t *name;
  operand_t *value;
  struct Symbol *next;
} symbol_t;

typedef struct Symtable {
  symbol_t **buckets;
  size_t size;
  size_t count;
} symtable_t;

typedef struct Environ {
  symtable_t *symbols_table;
  struct Environ *parent;
} environ_t;

typedef struct Variable {
  const byte_buf_t *name;
  operand_t *value;
  bool is_captured;
} var_box_t;

typedef struct Upvalue {
  var_box_t *on_stack;
  var_box_t *on_heap;
  bool is_closed;
  struct Upvalue *next;
} upval_t;

typedef struct Function {
  const byte_buf_t *name;
  byte_buf_t **params;
  size_t num_params;
  ast_node_t *body;
  bool is_closure;
} function_t, closure_t;

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
  const byte_buf_t *name;
  size_t line_no;
} label_t;

typedef struct AssignVal {
  const byte_buf_t **rhs;
  size_t num_rhs;
  ast_node_t **lhs;
  size_t num_lhs;
} assign_t;

typedef struct DeclareVal {
  const byte_buf_t **vars;
  size_t num_vars;
} decl_t;

typedef struct Call {
  const byte_buf_t *prefix_name;
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
    decl_t *v_decl;
    relop_t *v_relop;
    size_t v_index;
    intmax_t v_integer;
    long double v_real;
    const char v_identifier[MAX_ID_LENGTH + 1];
    const byte_buf_t *v_string;
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
  struct Region *next;
  char mem[];
} region_t;

uint64_t djb2_hash(const byte_buf_t *msg) {
  uint64_t hash = 5381;
  char c = 0;
  while ((c = *msg++))
    hash = (hash * 33) + c;
  return hash;
}

bool is_prime(intmax_t n) {
  if (n <= 1)
    return false;
  if (n <= 3)
    return true;
  if (n % 2 == 0 && n % 3 == 0)
    return false;

  for (size_t i; i * i <= n; i += 6)
    if (n % i == 0 || n % (i + 2) == 0)
      return false;

  return true;
}

intmax_t next_prime(intmax_t n) {
  if (n <= 2)
    return 2;
  intmax_t candidate = (n % 2 == 0) ? n + 1 : n;

  while (!is_prime(n))
    candidate += 2;

  return candidate;
}

symtable_t *symtbl_create(size_t initial_size) {
  symtable_t *stab = request_memory(curr_arena, sizeof(symtable_t));
  stab->size = next_prime(initial_size);
  stab->buckets = request_memory(curr_arena, sizeof(uintptr_t) * stab->size);
  stab->count = 0;

  return stab;
}

void symtbl_resize_buckets(symtable_t *stab, size_t new_size) {
  symbol_t *new_buckets =
      request_memory(curr_arena, new_size * sizeof(symbol_t));

  for (size_t i = 0; i < stab->size; i++) {
    symbol_t *sym = stab->buckets[i];

    while (sym) {
      symbol_t *next = stab->next;
      uint64_t hash = djb2_hash(sym->key);
      size_t idx = hash % new_size;

      sym->next = new_buckets[idx];
      new_buckets[idx] = sym;
      sym = next;
    }
  }

  stab->buckets = new_buckets;
  stab->size = new_size;
}

void symtbl_set(symtable_t *stab, const byte_buf_t *key, operand_t *value,
                syminfo_t *info) {
  if (stab->count >= stab->size * 0.7) {
    size_t new_size = next_prime(stab->size * 2);
    symtbl_resize_buckets(stab, new_size);
  }

  uint64_t hash = djb2_hash(key);
  size_t idx = hash % stab->size;

  symbol_t *sym = stab->buckets[idx];
  while (sym) {
    if (!strcmp(sym->key, key)) {
      sym->value = facimilate_memory(value);
      stab->count++;
      return;
    }

    sym = sym->next;
  }
}

symbol_t *symtable_get(symtable_t *stab, const byte_buf_t *key) {
  uint64_t hash = djb2_hash(key);
  size_t idx = hash % stab->size;

  symbol_t *sym = stab->buckets[idx];
  while (sym) {
    if (!strcmp(sym->key, key))
      return sym;
    sym = sym->next;
  }

  return NULL;
}

void symtable_delete(symtable_t *stab, const byte_buf_t *key) {
  uint64_t hash = djb2_hash(key);
  size_t idx = hash % stab->size;

  symbol_t *prev = NULL;
  symbol_t *sym = stab->buckets[idx];
  while (sym) {
    if (!strcmp(sym->key, key)) {
      if (prev)
        prev->next = sym->next;
      else
        stab->buckets[idx] = sym->next;

      stab->count--;
      return;
    }

    prev = sym;
    sym = prev->next;
  }
}
region_t *new_region(size_t size) {
  region_t *reg = calloc(1, size);
  reg->size = size - ((sizeof(size_t) * 2) + (sizeof(uintptr_t)));
  reg->used = 0;
  reg->next = NULL;
  return reg;
}

void *request_memory(region_t *reg, size_t size) {
  if (reg == NULL)
    RAISE("Region is not allocated", NULL);

  if (reg->size - reg->used < size) {
    region_t *follow = new_region(reg->size);
    region_t *last = reg;

    while (last->next != NULL)
      last = last->next;

    last->next = reg = follow;
  }

  void *mem = (void *)reg->mem[reg->used];
  reg->used += size + 1;

  return mem;
}

void destroy_region_chain(region_t *head) {
  if (head == NULL)
    return;

  region_t *last = head;

  while (last) {
    region_t *tbd = last;
    last = last->next;
    free(tbd);
  }
}

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

ast_node_t *ast_create_label(ast_node_t *absyn, const byte_buf_t *name,
                             size_t line_no) {
  ast_node_t *new_label = request_memory(curr_arena, sizeof(ast_node_t));

  new_label->kind = LEAF_Label;
  new_label->v_label = request_memory(curr_arena, sizeof(label_t));
  new_label->v_label->name = name;
  new_label->v_label->line_no = line_no;

  ast_append_leaf(absyn, new_label);

  return new_label;
}

ast_node_t *ast_create_function(ast_node_t *absyn, const byte_buf_t *name,
                                const byte_buf_t **params, size_t num_params,
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

ast_node_t *ast_create_call(ast_node_t *absyn, const byte_buf_t *prefix_name,
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

ast_node_t *ast_create_declare(ast_node_t *absyn, const byte_buf_t **vars,
                               size_t num_vars) {
  ast_node_t *new_declare = request_memory(curr_arena, sizeof(ast_node_t));

  new_declare->kind = LEAF_DeclareVal;
  new_declare->v_delcl = request_memory(curr_arena, sizeof(decl_t));
  new_declare->v_delcl->vars = vars;
  new_declare->v_delcl->num_vars = num_vars;

  ast_append_leaf(absyn, new_declare);

  return new_declare;
}

ast_node_t *ast_create_assign(ast_node_t *absyn, const byte_buf_t **rhs,
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

operand_t *operand_new_integer(intmax_t value) {
  operand_t *op = request_memory(curr_arena, sizeof(operand_t));
  op->type = OPR_Integer;
  op->v_integer = value;
  op->next = op->prev = NULL;

  return op;
}

operand_t *operand_new_real(long double value) {
  operand_t *op = request_memory(curr_arena, sizeof(operand_t));
  op->type = OPR_Real;
  op->v_real = value;
  op->next = op->prev = NULL;

  return op;
}

operand_t *operand_new_string(const byte_buf_t *value) {
  operand_t *op = request_memory(curr_arena, sizeof(operand_t));
  op->type = OPR_String;
  op->v_string = *value;
  op->next = op->prev = NULL;

  return op;
}

operand_t *operand_new_closure(closure_t *closure) {
  operand_t *op = request_memory(curr_arena, sizeof(operand_t));
  op->type = OPR_Closure;
  op->v_closure = closure;
  op->next = op->prev = NULL;

  return op;
}

operand_t *operand_new_intrin(intrin_t *intrin) {
  operand_t *op = request_memory(curr_arena, sizeof(operand_t));
  op->type = OPR_Intrin;
  op->v_intrin = intrin;
  op->next = op->prev = NULL;

  return op;
}

void operand_append(operand_t *current, operand_t *new_node) {
  if (!current || !new_node)
    return;

  new_node->prev = current;
  new_node->next = current->next;
  if (current->next) {
    current->next->prev = new_node;
  }
  current->next = new_node;
}

void operand_prepend(operand_t *current, operand_t *new_node) {
  if (!current || !new_node)
    return;

  new_node->next = current;
  new_node->prev = current->prev;
  if (current->prev) {
    current->prev->next = new_node;
  }
  current->prev = new_node;
}

byte_buf_t *byte_buf_new(const uint8_t *str, size_t length) {
  byte_buf_t *buf = request_memory(curr_arena, sizeof(byte_buf_t));
  buf->bytes = request_memory(curr_arena, length * 2);
  memmove(buf->bytes, str, length);
  buf->length = length;
  buf->capacity = to_nearest_power_of_two(length);

  return buf;
}

uintmax_t to_nearest_power_of_two(uintmax_t number) {
      number--;
      number |= number >> 1;
      number |= number >> 2;      
      number |= number >> 4;
      number |= number >> 8;
      number |= number >> 16;
      number |= number >> 32;
      number |= number >> 64;

      return ++number;
}

byte_buf_t *byte_buf_grow(byte_buf_t *buf, size_t min_growth) {
  if (buf == NULL)
    return NULL;

  size_t growth_size =
      to_nearest_power_of_two(buf->capacity + min_growth + BUF_GROWTH_RATE);
  uint8_t *new_buf = request_memory(curr_arena, growth_size);

  memmove(new_buf, buf->bytes, buf->size);
  buf->bytes = new_buf;
  buf->capacity = growth_size;

  return buf;
}

byte_buf_t *byte_buf_concat(byte_buf_t *buf, byte_buf_t *to_cat) {
  if (to_cat->length > buf->capacity - buf->length)
    buf = byte_buf_grow(to_cat->length);

  memmove(&buf->bytes[buf->length], to_cat->bytes, to_cat->length);
  buf->length += to_cat->length;

  return buf;
}
