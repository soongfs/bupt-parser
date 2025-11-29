#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_PROD 9    /* 产生式个数 0..8 */
#define MAX_STATES 50 /* 状态最大数 */
#define MAX_ITEMS 100 /* 每个状态中项目最大数 */

/* 文法产生式:
   0: S -> E   (S 是增广文法的 E')
   1: E -> E+T
   2: E -> E-T
   3: E -> T
   4: T -> T*F
   5: T -> T/F
   6: T -> F
   7: F -> (E)
   8: F -> n
*/

char lhs_[MAX_PROD] = {'S', 'E', 'E', 'E', 'T', 'T', 'T', 'F', 'F'};
const char *rhs_[MAX_PROD] = {
    "E",   /* 0 */
    "E+T", /* 1 */
    "E-T", /* 2 */
    "T",   /* 3 */
    "T*F", /* 4 */
    "T/F", /* 5 */
    "F",   /* 6 */
    "(E)", /* 7 */
    "n"    /* 8 -> num，用 n 表示 */
};

int rhs_len(int p) { return (int)strlen(rhs_[p]); }

int is_nonterm(char c) { return c == 'S' || c == 'E' || c == 'T' || c == 'F'; }

/* 终结符顺序: + - * / ( ) n $ */
char terms[8] = {'+', '-', '*', '/', '(', ')', 'n', '$'};

int term_index(char c) {
    int i;
    for (i = 0; i < 8; i++)
        if (terms[i] == c)
            return i;
    return -1;
}

/* FIRST 集：
   对本文法所有非终结符 S,E,T,F：
   FIRST(S) = FIRST(E) = FIRST(T) = FIRST(F) = { '(', 'n' }
   没有 ε 产生式，因此 FIRST(βa) = FIRST(β 的第一个符号) 或 {a}
*/
int first_of_char(char X, char out[]) {
    int n = 0;
    if (is_nonterm(X)) {
        out[n++] = '(';
        out[n++] = 'n';
    } else {
        out[n++] = X;
    }
    return n;
}

/* LR(1) 项目 */
typedef struct {
    int prod;       /* 产生式编号 */
    int dot;        /* 点的位置 0..len */
    char lookahead; /* 展望符号（终结符或 $） */
} Item;

/* 项目集（状态） */
typedef struct {
    int count;
    Item items[MAX_ITEMS];
} State;

State states[MAX_STATES];
int state_count = 0;

int same_item(Item *a, Item *b) {
    return a->prod == b->prod && a->dot == b->dot &&
           a->lookahead == b->lookahead;
}

/* 向状态集合中加入项目（去重） */
void add_item(State *st, int prod, int dot, char la) {
    int i;
    for (i = 0; i < st->count; i++) {
        if (st->items[i].prod == prod && st->items[i].dot == dot &&
            st->items[i].lookahead == la)
            return;
    }
    st->items[st->count].prod = prod;
    st->items[st->count].dot = dot;
    st->items[st->count].lookahead = la;
    st->count++;
}

/* 闭包运算 closure(I) */
void closure(State *st) {
    int changed = 1;
    while (changed) {
        changed = 0;
        int i;
        for (i = 0; i < st->count; i++) {
            Item it = st->items[i];
            int p = it.prod;
            int d = it.dot;
            char la = it.lookahead;
            int len = rhs_len(p);

            if (d >= len)
                continue; /* 点在末尾 */
            char B = rhs_[p][d];
            if (!is_nonterm(B))
                continue; /* 点后不是非终结符 */

            /* 计算 FIRST(βa)，此处β是 dot 后 B 之后的串 */
            char lookset[8];
            int lkcount = 0;
            if (d + 1 < len) {
                char firstSym = rhs_[p][d + 1];
                lkcount = first_of_char(firstSym, lookset);
            } else {
                lookset[0] = la;
                lkcount = 1;
            }

            /* 对 B 的每个产生式 B->γ，加入 [B->·γ, b] */
            int q;
            for (q = 0; q < MAX_PROD; q++) {
                if (lhs_[q] == B) {
                    int k;
                    for (k = 0; k < lkcount; k++) {
                        int before = st->count;
                        add_item(st, q, 0, lookset[k]);
                        if (st->count > before)
                            changed = 1;
                    }
                }
            }
        }
    }
}

/* 为了比较状态，需要对项目排序 */
int cmp_item(const void *a, const void *b) {
    const Item *ia = (const Item *)a;
    const Item *ib = (const Item *)b;
    if (ia->prod != ib->prod)
        return ia->prod - ib->prod;
    if (ia->dot != ib->dot)
        return ia->dot - ib->dot;
    return (int)ia->lookahead - (int)ib->lookahead;
}

void sort_state(State *st) {
    qsort(st->items, st->count, sizeof(Item), cmp_item);
}

int equal_state(State *a, State *b) {
    int i;
    if (a->count != b->count)
        return 0;
    for (i = 0; i < a->count; i++)
        if (!same_item(&a->items[i], &b->items[i]))
            return 0;
    return 1;
}

/* 所有可能出现在 goto 中的文法符号 */
char symbols_all[12] = {'+', '-', '*', '/', '(', ')',
                        'n', '$', 'E', 'T', 'F', 'S'};
int sym_count = 12;

int sym_index(char c) {
    int i;
    for (i = 0; i < sym_count; i++)
        if (symbols_all[i] == c)
            return i;
    return -1;
}

/* DFA 转移：trans[状态][符号] = 目标状态 */
int trans[MAX_STATES][12];

/* goto(I, X) */
void goto_state_func(State *from, char X, State *to) {
    int i;
    to->count = 0;
    for (i = 0; i < from->count; i++) {
        Item it = from->items[i];
        int p = it.prod;
        int d = it.dot;
        char la = it.lookahead;
        int len = rhs_len(p);

        if (d < len && rhs_[p][d] == X) {
            add_item(to, p, d + 1, la);
        }
    }
    if (to->count > 0) {
        closure(to);
    }
}

/* 构造 LR(1) 项目集族 C 及 trans 转移表 */
void build_canonical_collection() {
    int i, j;
    for (i = 0; i < MAX_STATES; i++)
        for (j = 0; j < 12; j++)
            trans[i][j] = -1;

    /* 初始项目集 I0 = closure({ [S->·E, $] }) */
    State I0;
    I0.count = 0;
    add_item(&I0, 0, 0, '$');
    closure(&I0);
    sort_state(&I0);

    states[0] = I0;
    state_count = 1;

    /* 类似构造 NFA 的可达状态，一边遍历一边扩展 */
    for (i = 0; i < state_count; i++) {
        int si;
        for (si = 0; si < sym_count; si++) {
            char X = symbols_all[si];
            State J;
            goto_state_func(&states[i], X, &J);
            if (J.count == 0)
                continue;

            sort_state(&J);

            int found = -1;
            for (j = 0; j < state_count; j++) {
                if (equal_state(&states[j], &J)) {
                    found = j;
                    break;
                }
            }
            if (found == -1) {
                found = state_count;
                states[state_count] = J;
                state_count++;
            }
            trans[i][sym_index(X)] = found;
        }
    }
}

/* ACTION / GOTO 表 */

typedef struct {
    int type; /* 0:error, 1:shift, 2:reduce, 3:accept */
    int val;  /* shift 用作目标状态，reduce 用作产生式编号 */
} Action;

Action action_tbl[MAX_STATES][8]; /* 8 个终结符列: + - * / ( ) n $   */
int goto_tbl[MAX_STATES][3];      /* 3 个非终结符列: E,T,F           */

int nt_index(char c) {
    if (c == 'E')
        return 0;
    if (c == 'T')
        return 1;
    if (c == 'F')
        return 2;
    return -1;
}

/* 构造 LR(1) 分析表 */
void build_parsing_table() {
    int i, t;

    /* 初始化为 error / -1 */
    for (i = 0; i < MAX_STATES; i++) {
        for (t = 0; t < 8; t++) {
            action_tbl[i][t].type = 0;
            action_tbl[i][t].val = -1;
        }
        for (t = 0; t < 3; t++)
            goto_tbl[i][t] = -1;
    }

    /* 根据 DFA 转移设置 shift 动作 */
    for (i = 0; i < state_count; i++) {
        for (t = 0; t < 8; t++) {
            char a = terms[t];
            int sidx = sym_index(a);
            int j = trans[i][sidx];
            if (j != -1) {
                action_tbl[i][t].type = 1; /* shift */
                action_tbl[i][t].val = j;  /* 目标状态 */
            }
        }
    }

    /* 设置 GOTO 表 (E,T,F) */
    for (i = 0; i < state_count; i++) {
        char nts[3] = {'E', 'T', 'F'};
        int ni;
        for (ni = 0; ni < 3; ni++) {
            char A = nts[ni];
            int j = trans[i][sym_index(A)];
            if (j != -1)
                goto_tbl[i][ni] = j;
        }
    }

    /* 根据项目集设置 reduce / accept 动作 */
    for (i = 0; i < state_count; i++) {
        int k;
        for (k = 0; k < states[i].count; k++) {
            Item it = states[i].items[k];
            int p = it.prod;
            int d = it.dot;
            char la = it.lookahead;
            int len = rhs_len(p);

            if (d == len) { /* 点在产生式末尾 */
                if (lhs_[p] == 'S' && la == '$') {
                    /* [S->E·, $] => accept */
                    int col = term_index('$');
                    action_tbl[i][col].type = 3; /* accept */
                    action_tbl[i][col].val = 0;
                } else {
                    /* 归约 A->β，展望符号为 la */
                    int col = term_index(la);
                    if (col >= 0) {
                        action_tbl[i][col].type = 2; /* reduce */
                        action_tbl[i][col].val = p;  /* 产生式编号 */
                    }
                }
            }
        }
    }
}

/* 主程序：LR(1) 分析过程（算法 4.3） */
int main() {
    char input_raw[1024];

    if (!fgets(input_raw, sizeof(input_raw), stdin))
        return 0;

    int len = (int)strlen(input_raw);
    while (len > 0 &&
           (input_raw[len - 1] == '\n' || input_raw[len - 1] == '\r')) {
        input_raw[--len] = '\0';
    }

    /* 构造 LR(1) 项目集族与分析表 */
    build_canonical_collection();
    build_parsing_table();

    /* 在输入串末尾加上 $ */
    char input[1024];
    strcpy(input, input_raw);
    input[len] = '$';
    input[len + 1] = '\0';

    /* 状态栈（不单独维护符号栈） */
    int state_stack[1024];
    int top = 0;
    state_stack[0] = 0; /* 初始状态 */

    int ip = 0; /* 输入指针 */

    while (1) {
        int s = state_stack[top];
        char a = input[ip];
        int col = term_index(a);
        if (col < 0) {
            printf("error\n");
            break;
        }

        Action act = action_tbl[s][col];

        if (act.type == 1) {
            /* shift */
            printf("shift\n");
            top++;
            state_stack[top] = act.val;
            ip++;
        } else if (act.type == 2) {
            /* reduce by 产生式 p */
            int p = act.val;
            printf("%d\n", p);

            int rlen = rhs_len(p);
            top -= rlen; /* 弹出 |β| 个状态 */

            if (top < 0) {
                printf("error\n");
                break;
            }

            char A = lhs_[p]; /* 产生式左部 */
            int nt = nt_index(A);
            if (nt < 0) {
                printf("error\n");
                break;
            }

            int s2 = state_stack[top];
            int next = goto_tbl[s2][nt];
            if (next < 0) {
                printf("error\n");
                break;
            }

            top++;
            state_stack[top] = next;
        } else if (act.type == 3) {
            /* accept */
            printf("accept\n");
            break;
        } else {
            /* error */
            printf("error\n");
            break;
        }
    }

    return 0;
}
