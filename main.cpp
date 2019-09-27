#include <iostream>
#include <string>
#include <vector>
#include <algorithm>
#include <set>
#include <map>
#include <stack>
#include <memory>
#include <iterator>

using namespace std;

struct Tree 
{
    vector<unsigned> m_priorities;
    string m_str;
    unique_ptr<Tree> mp_left;
    unique_ptr<Tree> mp_right;

    Tree(const string& str, const vector<unsigned>& priorities) : m_str(str), m_priorities(priorities), mp_left(nullptr), mp_right(nullptr) {}

    void Parse() 
    {
        if (m_priorities.empty()) return;

        unsigned imin = distance(min_element(m_priorities.rbegin(), m_priorities.rend(), [](const auto& l, const auto& r) { return l < r; }), m_priorities.rend()) - 1;

        string new_str;
        unsigned sub_ind = 0;
        unsigned count = 0;
        for (unsigned i = 0; i < m_str.size(); ++i)
            if (!isalpha(m_str[i]) && count++ == imin) 
            {
                sub_ind = i;
                new_str = m_str[i];
                break;
            }

        if (!m_str.substr(0, sub_ind).empty()) 
        {
            mp_left.reset(new Tree(m_str.substr(0, sub_ind), vector<unsigned>(m_priorities.begin(), m_priorities.begin() + imin)));
            mp_left->Parse();
        }
        if (!m_str.substr(sub_ind + 1, m_str.size() - sub_ind - 1).empty()) 
        {
            mp_right.reset(new Tree(m_str.substr(sub_ind + 1, m_str.size() - sub_ind - 1), vector<unsigned>(m_priorities.begin() + imin + 1, m_priorities.end())));
            mp_right->Parse();
        }

        m_str = new_str;
    }
};

void InsertDotsInplace(string& str) // worst way to write if (str[i-1] != '|')
{
    unsigned i = 0;
    while (i < str.size() - 1) {
        if (((str[i] != '|' && str[i] != '(' && str[i] != ')') &&
            (isalpha(str[i + 1]) || str[i + 1] == '(')) ||
            (str[i] == ')' && (isalpha(str[i + 1]) || str[i + 1] == '(')) ||
            (str[i + 1] == '(' && isalpha(str[i]))) {
            str.insert(i + 1, ".");
            ++i;
        }
        ++i;
    }
}

constexpr char     EPS =     '~';
constexpr unsigned X   =     ~0U;
#define            NOP      { X }

struct NFA
{
    map<char, vector<vector<unsigned>>> state_table;
    unsigned start, end, size;
};

void PrintNFA(const NFA& nfa)
{
    cout << "Start state is " << nfa.start << endl;
    cout << "End state is " << nfa.end << endl;

    for (const auto& it_row : nfa.state_table)
    {
        const auto& input = it_row.first;
        const auto& row = it_row.second;

        cout << input << ": ";
        for (unsigned i = 0; i < row.size(); ++i)
        {
            cout << i << " -> { ";
            for (const auto& el : row[i])
            {
                if (el == X)
                    cout << "X ";
                else
                    cout << el << " ";
            }
            cout << "}, ";
        }
        cout << '\n';
    }
}

NFA MakeSimpleNFA(char c)
{
    NFA simple_NFA{};
    simple_NFA.start = 0;
    simple_NFA.end = 1;
    simple_NFA.size = 2;

    vector<vector<unsigned>> simple_transition_row = { { X, 1 }, NOP };
    simple_NFA.state_table[c] = simple_transition_row;
    simple_NFA.state_table[EPS].assign(simple_NFA.size, NOP);

    return simple_NFA;
}

void AppendInplace(NFA& dest, const NFA& src)
{
    auto old_size = dest.size;
    auto new_size = old_size + src.size;

    set<char> alphabet;
    auto get_char = [](const auto& it_row) { return it_row.first; };
    transform(dest.state_table.begin(), dest.state_table.end(), inserter(alphabet, alphabet.end()), get_char);
    transform(src.state_table.begin(), src.state_table.end(), inserter(alphabet, alphabet.end()), get_char);

    for (const auto& c : alphabet)
    {
        auto& dest_row = dest.state_table[c];
        dest_row.resize(new_size, NOP);

        const auto& it_trans_from_c = src.state_table.find(c);
        if (it_trans_from_c != src.state_table.end())
        {
            const auto& src_row = it_trans_from_c->second;
            copy(src_row.begin(), src_row.end(), dest_row.begin() + old_size);
            for_each(dest_row.begin() + old_size, dest_row.end(), [=](auto& vec)
            {
                for (auto& el : vec) el += el != X ? old_size : 0;
            });
        }

        if (c == EPS)
            dest_row[dest.end].push_back(old_size + src.start);
    }

    dest.end = old_size + src.end;
    dest.size = new_size;
}

void OrInplace(NFA& dest, const NFA& src) // 60% copypast of Append
{
    unsigned old_size = dest.size;
    unsigned new_size = old_size + src.size + 2;

    set<char> alphabet;
    for (const auto& it_row : dest.state_table)
    {
        alphabet.insert(it_row.first);
    }
    for (const auto& it_row : src.state_table)
    {
        alphabet.insert(it_row.first);
    }

    for (const auto& input : alphabet)
    {
        auto& dest_row = dest.state_table[input];
        dest_row.resize(new_size, NOP);

        if (src.state_table.count(input))
        {
            const auto& src_row = src.state_table.at(input);
            vector<vector<unsigned>> updated_src_row = src_row;
            transform(updated_src_row.begin(), updated_src_row.end(), updated_src_row.begin(), [=](auto& vec)
            {
                for (auto& el : vec) el != X ? el += old_size : el; return vec;
            });
            copy(updated_src_row.begin(), updated_src_row.end(), dest_row.begin() + old_size);
        }

        rotate(dest_row.rbegin(), dest_row.rbegin() + 1, dest_row.rend()); // Rotate right
        transform(dest_row.begin(), dest_row.end(), dest_row.begin(), [=](auto& vec)
        {
            for (auto& el : vec) el != X ? el += 1 : el; return vec;
        });

        if (input == EPS)
        {
            dest_row[0].push_back(dest.start + 1);
            dest_row[0].push_back(old_size + src.start + 1);
            dest_row[dest.end + 1].push_back(new_size - 1);
            dest_row[old_size + src.end + 1].push_back(new_size - 1);
        }
    }

    dest.start = 0;
    dest.end = new_size - 1;
    dest.size = new_size;
}

void StarInplace(NFA& dest)
{
    for (auto& it_row : dest.state_table)
    {
        auto& row = it_row.second;

        row.insert(row.begin(), NOP);
        row.insert(row.end(), NOP);
        for_each(row.begin(), row.end(), [=](auto& vec)
        {
            for (auto& el : vec) el += el != X ? 1 : 0;
        });

        if (it_row.first == EPS)
        {
            row[dest.end + 1].push_back(dest.start + 1); // F -e-> S
            row[dest.end + 1].push_back(row.size() - 1); // F -e-> NF
            row[0].push_back(dest.start + 1); // NS -e-> S
            row[dest.start = 0].push_back(dest.end = row.size() - 1); // NS -e-> NF
        }
    }

    dest.size += 2;
}

void PlusInplace(NFA& dest)
{
    dest.state_table[EPS][dest.end].push_back(dest.start);
}

NFA BuildFromParseTree(const Tree* t)
{
    auto token = t->m_str[0];
    if (isalpha(token))
        return MakeSimpleNFA(token);

    NFA left, right;
    if (t->mp_left) left = BuildFromParseTree(t->mp_left.get());
    if (t->mp_right) right = BuildFromParseTree(t->mp_right.get());

    switch (token)
    {
    case '|': OrInplace(left, right); break;
    case '*': StarInplace(left); break;
    case '.': AppendInplace(left, right); break;
    case '+': PlusInplace(left); break;
    }

    return left;
}

set<unsigned> EpsClosure(const NFA& N, const vector<unsigned>& states) 
{ 
    set<unsigned> eps_closure(states.begin(), states.end());
    stack<unsigned, vector<unsigned>> S(states);
    
    while (!S.empty()) 
    {
        auto state = S.top(); S.pop();

        for (const auto& dest : N.state_table.at(EPS)[state])
            if (dest != X && eps_closure.insert(dest).second)
                S.push(dest);
    }

    return eps_closure;
}

struct DFA {
    unsigned start_state;
    vector<unsigned> end_states;
    map<char, map<unsigned, unsigned>> transition_table;
};

DFA MakeDFA(const NFA& N)
{
    DFA dfa{};

    set<char> alphabet;
    for (const auto& p : N.state_table)
        if (p.first != EPS)
            alphabet.insert(p.first);

    map<set<unsigned>, unsigned> state_translation_from_set;
    map<unsigned, set<unsigned>> state_translation_from_label;
    unsigned label;

    stack<unsigned> unmarked_states;

    set<unsigned> start_states = EpsClosure(N, { N.start });
    label = state_translation_from_set[start_states] = state_translation_from_set.size();
    state_translation_from_label[label] = start_states;
    unmarked_states.push(label);

    while (!unmarked_states.empty())
    {
        auto state = unmarked_states.top(); unmarked_states.pop();

        const auto& state_set = state_translation_from_label[state];
        if (find_if(state_set.begin(), state_set.end(), [&](const auto& p){ return N.end == p; }) != state_set.end())
            dfa.end_states.push_back(state);

        for (const auto& c : alphabet)
        {
            vector<unsigned> moves;
            const auto& transitions_by_c = N.state_table.at(c);
            for (const auto& state : state_set)
            {
                const auto& destinations = transitions_by_c[state];
                copy_if(destinations.begin(), destinations.end(), back_inserter(moves), [](const auto& el) { return el != X; });
            }
            
            const auto U = EpsClosure(N, moves);

            const auto& it_translation_from_U = state_translation_from_set.find(U);
            if (it_translation_from_U == state_translation_from_set.end())
            {
                dfa.transition_table[c][state] = label = state_translation_from_set[U] = state_translation_from_set.size();
                state_translation_from_label[label] = U;
                unmarked_states.push(label);
            }
            else
                dfa.transition_table[c][state] = it_translation_from_U->second;
        }
    }

    return dfa;
}

void printDFA(const DFA& D)
{
    cout << "Start state is " << D.start_state << endl;

    cout << "End states are: ";
    for (const auto& a : D.end_states) 
        cout << a << ' ';
    cout << endl;

    for (const auto& it_row : D.transition_table)
    {
        const auto& input = it_row.first;
        const auto& row = it_row.second;

        cout << input << ": ";
        for (const auto& it_column : row)
            cout << it_column.first << " -> " << it_column.second << ", ";
        cout << endl;
    }
}

bool MatchInput(const DFA& dfa, const string& input)
{
    bool is_matching = false;
    auto current_state = dfa.start_state;

    for (const auto& c : input)
    {
        const auto& it_trans_from_c = dfa.transition_table.find(c);
        if (it_trans_from_c != dfa.transition_table.end())
            current_state = it_trans_from_c->second.at(current_state);
        else
            return false;
    }

    if (find(dfa.end_states.begin(), dfa.end_states.end(), current_state) != dfa.end_states.end())
        is_matching = true;

    return is_matching;
}

NFA MakeNFA(string regexpr)
{
    vector<unsigned> priorities;
    unsigned p = 0;

    InsertDotsInplace(regexpr);

    for (unsigned i = 0; i < regexpr.size(); ++i)
        switch (regexpr[i])
        {
        case '(': ++p; break;
        case ')': --p; break;

        case '+':                                         //high
        case '*': priorities.push_back(3 + p * 3); break; //high
        case '|': priorities.push_back(2 + p * 3); break; //medium
        case '.': priorities.push_back(1 + p * 3); break; //low
        }

    regexpr.erase(remove_if(regexpr.begin(), regexpr.end(), [](const auto& c) {return c == '(' || c == ')'; }), regexpr.end()); //rm -rf brackets

    Tree root(regexpr, priorities); root.Parse();
    return BuildFromParseTree(&root);
}

int Repl() // GOTO YAY
{
read_regexpr:
    string str;
    cout << "Give me your regexpr\n";
    getline(cin, str);
    if (str.length() == 0) goto read_regexpr; //handle incorrect input here

    DFA my_dfa = MakeDFA(MakeNFA(str));
    printDFA(my_dfa);

match_input:
    cout << "Give me your string\n";
    getline(cin, str); 

    if (str == "~") goto read_regexpr;
    else
    {
        if (MatchInput(my_dfa, str)) cout << "Yes\n";
        else cout << "No\n";

        goto match_input;
    }

    return 0;
}

int main() 
{
    return Repl();
}
