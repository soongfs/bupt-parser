#include <algorithm>
#include <iostream>
#include <string>
#include <vector>

#define TERM_COUNT                                                             \
    7 // 文法中的 7 个终结符，再加 1 个 '$' 列，下面用 TERM_COUNT+1

// 非终结符
enum non_term { E, A, B, T, F, NT_COUNT };

// FIRST/FOLLOW 使用的集合类型
using symbol_set = std::vector<char>;

// FIRST[A] / FOLLOW[A]
std::vector<symbol_set> FIRST(NT_COUNT);
std::vector<symbol_set> FOLLOW(NT_COUNT);

// 往集合里加一个符号（避免重复）
void add_to_set(symbol_set &s, char ch) {
    if (std::find(s.begin(), s.end(), ch) == s.end()) {
        s.push_back(ch);
    }
}

// FIRST / FOLLOW
void init_first_follow() {
    add_to_set(FIRST[E], '(');
    add_to_set(FIRST[E], 'n');

    add_to_set(FIRST[A], '+');
    add_to_set(FIRST[A], '-');
    add_to_set(FIRST[A], 'e'); // epsilon

    add_to_set(FIRST[B], '*');
    add_to_set(FIRST[B], '/');
    add_to_set(FIRST[B], 'e'); // epsilon

    add_to_set(FIRST[T], '(');
    add_to_set(FIRST[T], 'n');

    add_to_set(FIRST[F], '(');
    add_to_set(FIRST[F], 'n');

    add_to_set(FOLLOW[E], '$');
    add_to_set(FOLLOW[E], ')');

    add_to_set(FOLLOW[A], '$');
    add_to_set(FOLLOW[A], ')');

    add_to_set(FOLLOW[B], '$');
    add_to_set(FOLLOW[B], ')');
    add_to_set(FOLLOW[B], '+');
    add_to_set(FOLLOW[B], '-');

    add_to_set(FOLLOW[T], '$');
    add_to_set(FOLLOW[T], ')');
    add_to_set(FOLLOW[T], '+');
    add_to_set(FOLLOW[T], '-');

    add_to_set(FOLLOW[F], '$');
    add_to_set(FOLLOW[F], ')');
    add_to_set(FOLLOW[F], '+');
    add_to_set(FOLLOW[F], '-');
    add_to_set(FOLLOW[F], '*');
    add_to_set(FOLLOW[F], '/');
}

// 产生式结构：lhs -> rhs
struct Production {
    non_term lhs;
    std::string rhs; // 右部符号串，E/A/B/T/F
                     // 代表非终结符，其它字符代表终结符，'e' 表示 ε
};

// 按编号 1~10 列出产生式，下标 0 对应编号 1
std::vector<Production> prods = {
    {E, "TA"},  // 1: E -> T A
    {A, "+TA"}, // 2: A -> + T A
    {A, "-TA"}, // 3: A -> - T A
    {A, "e"},   // 4: A -> ε
    {T, "FB"},  // 5: T -> F B
    {B, "*FB"}, // 6: B -> * F B
    {B, "/FB"}, // 7: B -> / F B
    {B, "e"},   // 8: B -> ε
    {F, "(E)"}, // 9: F -> ( E )
    {F, "n"}    // 10: F -> num (用 'n' 表示)
};

// 判断字符是否为非终结符
bool is_non_term_char(char c) {
    return c == 'E' || c == 'A' || c == 'B' || c == 'T' || c == 'F';
}

// 将非终结符字符映射到枚举 non_term
non_term to_non_term(char c) {
    switch (c) {
    case 'E':
        return E;
    case 'A':
        return A;
    case 'B':
        return B;
    case 'T':
        return T;
    case 'F':
        return F;
    default:
        return E; // 不会走到这里
    }
}

// 把终结符字符映射到分析表的列号（0..7）
// 我们的 8 列依次对应： + - * / ( ) n $
int term_index(char ch) {
    switch (ch) {
    case '+':
        return 0;
    case '-':
        return 1;
    case '*':
        return 2;
    case '/':
        return 3;
    case '(':
        return 4;
    case ')':
        return 5;
    case 'n':
        return 6;
    case '$':
        return 7;
    default:
        return -1; // 非法终结符
    }
}

// 计算 FIRST(α)，α 为符号串右部
symbol_set first_of_alpha(const std::string &alpha) {
    symbol_set result;

    // α = ε
    if (alpha.size() == 1 && alpha[0] == 'e') {
        add_to_set(result, 'e');
        return result;
    }

    bool all_can_epsilon = true;

    for (std::size_t i = 0; i < alpha.size(); ++i) {
        char X = alpha[i];

        if (!is_non_term_char(X)) {
            // 终结符
            if (X != 'e') {
                add_to_set(result, X);
            } else {
                add_to_set(result, 'e');
            }
            all_can_epsilon = false;
            break;
        } else {
            // 非终结符
            non_term nt = to_non_term(X);
            bool has_epsilon = false;
            for (char c : FIRST[nt]) {
                if (c == 'e') {
                    has_epsilon = true;
                } else {
                    add_to_set(result, c);
                }
            }
            if (!has_epsilon) {
                all_can_epsilon = false;
                break;
            }
            // 否则继续看下一个符号
        }
    }

    if (all_can_epsilon) {
        add_to_set(result, 'e');
    }

    return result;
}

// 预测分析表：M[非终结符][终结符列] = 产生式编号 (1..10)，0 表示出错表项
std::vector<std::vector<int>> M(NT_COUNT, std::vector<int>(TERM_COUNT + 1, 0));

// 算法 4.2：构造预测分析表
void build_ll_table() {
    // 已经初始化为 0（错误表项）

    // 对文法每个产生式 A -> α
    for (std::size_t p = 0; p < prods.size(); ++p) {
        non_term A = prods[p].lhs;
        const std::string &alpha = prods[p].rhs;
        int prod_no = static_cast<int>(p) + 1; // 编号 1..10

        symbol_set firstAlpha = first_of_alpha(alpha);
        bool has_epsilon = false;

        // 对每个 a ∈ FIRST(α)
        for (char a : firstAlpha) {
            if (a == 'e') {
                has_epsilon = true;
                continue;
            }
            int col = term_index(a);
            if (col < 0)
                continue; // 非法终结符防御

            M[A][col] = prod_no; // M[A, a] = 该产生式编号
        }

        // 如果 ε ∈ FIRST(α)，则对每个 b ∈ FOLLOW(A)，M[A, b] = 该产生式编号
        if (has_epsilon) {
            for (char b : FOLLOW[A]) {
                int col = term_index(b);
                if (col < 0)
                    continue;
                M[A][col] = prod_no;
            }
        }
    }
}

int main() {
    // 读入一行表达式
    std::string input;
    if (!std::getline(std::cin, input)) {
        return 0;
    }

    // 初始化 FIRST / FOLLOW 并构造预测分析表
    init_first_follow();
    build_ll_table();

    // 在输入串末尾加上 $
    input.push_back('$');

    // 分析栈：左端为栈底，用字符串表示
    std::string st;
    st.push_back('$');
    st.push_back('E'); // 开始符号

    // 输入指针
    std::size_t ip = 0;

    while (true) {
        // 记录当前栈和输入串，用于输出
        std::string stack_snapshot = st;
        std::string input_snapshot = input.substr(ip);

        char X = st.back(); // 栈顶符号
        char a = input[ip]; // 当前输入符号

        std::string action;

        // 情况 1：X 和 a 都是 $，接受
        if (X == '$' && a == '$') {
            action = "accept";
            std::cout << stack_snapshot << '\t' << input_snapshot << '\t'
                      << action << '\n';
            break;
        }

        // 情况 2：栈顶是终结符且等于当前输入符号 => match
        if (!is_non_term_char(X) && X == a && X != '$') {
            action = "match";
            // 执行动作
            st.pop_back();
            ++ip;

            std::cout << stack_snapshot << '\t' << input_snapshot << '\t'
                      << action << '\n';
            continue;
        }

        // 情况 3：栈顶是终结符 / $ 但和输入不匹配 => error
        if (!is_non_term_char(X)) {
            action = "error";
            std::cout << stack_snapshot << '\t' << input_snapshot << '\t'
                      << action << '\n';
            break;
        }

        // 情况 4：栈顶是非终结符，用预测分析表
        non_term A = to_non_term(X);
        int col = term_index(a);

        if (col < 0 || M[A][col] == 0) {
            // 表项未定义 => error
            action = "error";
            std::cout << stack_snapshot << '\t' << input_snapshot << '\t'
                      << action << '\n';
            break;
        } else {
            // 查到产生式编号
            int prod_no = M[A][col];
            const Production &prod = prods[prod_no - 1];

            action = std::to_string(prod_no);

            // 弹出栈顶非终结符
            st.pop_back();

            // 将产生式右部逆序压栈（ε 不压栈）
            if (!(prod.rhs.size() == 1 && prod.rhs[0] == 'e')) {
                for (int i = static_cast<int>(prod.rhs.size()) - 1; i >= 0;
                     --i) {
                    st.push_back(prod.rhs[i]);
                }
            }

            std::cout << stack_snapshot << '\t' << input_snapshot << '\t'
                      << action << '\n';
            continue;
        }
    }

    return 0;
}
