#include <iostream>
#include <string>
#include <vector>
#include <iomanip>
#include <algorithm>
#include <set>
#include <map>
#include <stack>
#include <memory>

using namespace std;

struct Tree {
    vector<int> vec;
    string s;
    unique_ptr<Tree> l;
    unique_ptr<Tree> r;

    Tree(string s_, vector<int> vec_) : s(s_), vec(vec_), l(nullptr), r(nullptr) {}

    void parse() {
        if (vec.empty()) return;

        int imin =
            distance
            (
                min_element
                (
                    vec.rbegin(), vec.rend(),
                    [](const auto & l, const auto & r) { return l < r; }
                ),
                vec.rend()
            ) - 1;

        string new_str;
        int sub_ind = -1;
        int count = -1;
        for (int i = 0; i < s.size(); ++i)
            if (!isalpha(s[i]) && ++count == imin) {
                sub_ind = i;
                new_str = s[i];
                break;
            }

        vector<int> vec_l(vec.begin(), vec.begin() + imin);
        if (!s.substr(0, sub_ind).empty()) 
        {
            l.reset(new Tree(s.substr(0, sub_ind), vec_l));
            l->parse();
        }

        vector<int> vec_r(vec.begin() + imin + 1, vec.end());
        if (!s.substr(sub_ind + 1, s.size() - sub_ind - 1).empty()) 
        {
            r.reset(new Tree(s.substr(sub_ind + 1, s.size() - sub_ind - 1), vec_r));
            r->parse();
        }

        s = new_str;
    }

    //void print(Tree* p)
    //{
    //    if (p != nullptr) {
    //        if (p->l) print(p->l);
    //        if (p->r) print(p->r);
    //        cout << p->s << endl;
    //    }
    //}
};


void InsertDotsInplace(string& str) // worst way to write if (str[i-1] != '|')
{
    int i = 0;
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

constexpr char EPS = '~';
const vector<unsigned> NOP = { ~0U };

struct NSA
{
    map<char, vector<vector<unsigned>>> state_table;
    unsigned start, end, size;
};

void PrintNSA(const NSA& nsa)
{
    cout << "Start state is " << nsa.start << endl;
    cout << "End state is " << nsa.end << endl;

    for (const auto& it_row : nsa.state_table)
    {
        auto& input = it_row.first;
        auto& row = it_row.second;

        cout << input << ": ";
        for (unsigned i = 0; i < row.size(); ++i)
        {
            cout << i << " -> { ";
            for (const auto& el : row[i])
            {
                if (el == ~0U)
                    cout << "NO ";
                else
                    cout << el << " ";
            }
            cout << "}, ";
        }

        cout << '\n';
    }
}

NSA MakeSimpleNSA(char c)
{
    NSA simple_NSA{};
    simple_NSA.start = 0;
    simple_NSA.end = 1;
    simple_NSA.size = 2;

    vector<vector<unsigned>> simple_transition_row = { { 1 }, NOP }; // from 0 to 1, from 1 to 1 (SAME means S -> S)
    simple_NSA.state_table[c] = simple_transition_row;
    //simple_NSA.state_table.emplace(EPS, simple_NSA.size, SAME);
    simple_NSA.state_table[EPS] = vector<vector<unsigned>>(simple_NSA.size, NOP);

    return simple_NSA;
}

void AppendInplace(NSA& dest, const NSA& src)
{
    unsigned old_size = dest.size;
    unsigned new_size = old_size + src.size;

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
        auto& dest_row = dest.state_table[input]; // Automatically creates one if it doesn't exist
        dest_row.resize(new_size, NOP);

        if (src.state_table.count(input))
        {
            const auto& src_row = src.state_table.at(input);
            //vector<vector<unsigned>> updated_src_row = src_row;
            copy(src_row.begin(), src_row.end(), dest_row.begin() + old_size);
            transform(dest_row.begin() + old_size, dest_row.end(), dest_row.begin() + old_size, [=](const auto & vec)
            {
                vector<unsigned> new_vec;
                for (auto& el : vec) new_vec.push_back(el != ~0 ? el + old_size : el);
                return new_vec;
            });
        }

        if (input == EPS)
        {
            dest_row[dest.end].push_back(old_size + src.start);
        }
    }

    dest.end = old_size + src.end;
    dest.size = new_size;
}

void OrInplace(NSA& dest, const NSA& src)
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
        auto& dest_row = dest.state_table[input]; // Automatically creates one if it doesn't exist
        dest_row.resize(new_size, NOP);

        if (src.state_table.count(input))
        {
            const auto& src_row = src.state_table.at(input);
            vector<vector<unsigned>> updated_src_row = src_row;
            transform(updated_src_row.begin(), updated_src_row.end(), updated_src_row.begin(), [=](const auto & vec)
            {
                vector<unsigned> new_vec;
                for (auto& el : vec) new_vec.push_back(el != ~0 ? el + old_size : el);
                return new_vec;
            });
            copy(updated_src_row.begin(), updated_src_row.end(), dest_row.begin() + old_size);
        }

        rotate(dest_row.rbegin(), dest_row.rbegin() + 1, dest_row.rend()); // Rotate right
        transform(dest_row.begin(), dest_row.end(), dest_row.begin(), [=](auto & vec)
        {
            vector<unsigned> new_vec;
            for (auto& el : vec) new_vec.push_back(el != ~0 ? el + 1 : el);
            return new_vec;
        });
        //dest_row.front() = SAME;

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

void StarInplace(NSA& dest)
{
    auto& eps_transitions = dest.state_table[EPS];
    eps_transitions[dest.start].push_back(dest.end);
    eps_transitions[dest.end].push_back(dest.start);
}

void PlusInplace(NSA& dest)
{
    dest.state_table[EPS][dest.end].push_back(dest.start);
}

NSA BuildFromParseTree(const Tree* t)
{
    char token = t->s[0];
    if (isalpha(token))
    {
        NSA simple = MakeSimpleNSA(token);
        return simple;
    }

    NSA left, right;
    if (t->l) left = BuildFromParseTree(t->l.get());
    if (t->r) right = BuildFromParseTree(t->r.get());

    switch (token)
    {
    case '|': OrInplace(left, right); break;
    case '*': StarInplace(left); break;
    case '.': AppendInplace(left, right); break;
    case '+': PlusInplace(left); break;
    }

    //cout << token << endl;
    //PrintNSA(left);

    return left;
}

set<unsigned> eps_closure(const NSA& N, const vector<unsigned>& states) 
{ 
    set<unsigned> eps_clos(states.begin(), states.end());
    stack<unsigned, vector<unsigned>> S(states);
    unsigned num;
    
    //for (const auto& a : states)
    //{
    //    if (a != ~0U)
    //    {
    //        S.push(a);
    //        eps_clos.insert(a);
    //    }
    //}

    while (!S.empty()) 
    {
        num = S.top();
        S.pop();

        for (const auto& a : N.state_table.at(EPS)[num])
        {
            if (a != ~0U && !eps_clos.count(a))
            {
                eps_clos.insert(a);
                S.push(a);
            }
        }
    }

    return eps_clos;
}

struct DFA {
    vector<unsigned> ends;
    //map<pair<vector<unsigned>, vector<unsigned>>, char> trans_table; //form,to,with
    map<char, map<unsigned, unsigned>> transition_table;
    unsigned start;
    set<char> alphabet;
};

//DFA make_dfa(const NSA& N) {
//    DFA out;
//    map<vector<unsigned>, unsigned> my_map;
//    vector<unsigned> starts = eps_closure(N, { N.start });
//
//    vector<vector<unsigned>> marked({ starts });
//    my_map[starts] = my_map.size();
//    out.start = 0;
//
//    while (!marked.empty()) {
//        vector<unsigned> T = marked.back();
//        marked.pop_back();
//        if (find(T.begin(), T.end(), N.end) != T.end()) {
//            out.ends.push_back(my_map.size());
//        }
//
//        set<char> alphabet;
//        for (auto& a : N.state_table)
//            alphabet.insert(a.first);
//
//        for (auto& a : alphabet) {
//            set<unsigned> newT;
//            for (auto& t : T) {
//                for (auto& tt : N.state_table.at(a).at(t)) {
//                    newT.insert(tt);
//                }
//            }
//
//            vector<unsigned>unique_move_T;
//            for (auto& t : newT) {
//                if (t != ~0U)
//                    unique_move_T.push_back(t);
//            }
//
//            vector<unsigned> U = eps_closure(N, unique_move_T);
//
//            if (my_map.find(U) == my_map.end()) {
//                my_map[U] = my_map.size();
//                marked.push_back(U);
//            }
//
//            out.trans_table[{T, U}] = a;
//        }
//
//    }
//    return out;
//}

DFA MakeDFA(const NSA& N)
{
    DFA dfa{};

    set<char> alphabet;
    for (const auto& p : N.state_table)
        if (p.first != EPS)
            alphabet.insert(p.first);

    dfa.alphabet = alphabet;

    map<set<unsigned>, unsigned> state_translation_from_set;
    map<unsigned, set<unsigned>> state_translation_from_label;
    unsigned label;

    std::vector<unsigned> unmarked_states;

    set<unsigned> start_states = eps_closure(N, { N.start });
    label = state_translation_from_set[start_states] = state_translation_from_set.size();
    state_translation_from_label[label] = start_states;
    unmarked_states.push_back(label);

    while (!unmarked_states.empty())
    {
        unsigned state = unmarked_states.back(); unmarked_states.pop_back();

        const auto& state_set = state_translation_from_label[state];
        if (find_if(state_set.begin(), state_set.end(), [&](const auto& p){ return N.end == p; }) != state_set.end())
        {
            dfa.ends.push_back(state);
        }

        for (char c : alphabet)
        {
            vector<unsigned> moves;
            for (const auto& state : state_set)
            {
                const auto& transitions = N.state_table.at(c)[state];
                for (const auto& t : transitions)
                    if (t != ~0U)
                        moves.push_back(t);

                //moves.insert(moves.end(), transitions.begin(), transitions.end());
            }
            
            const auto U = eps_closure(N, moves);

            if (!state_translation_from_set.count(U))
            {
                label = state_translation_from_set[U] = state_translation_from_set.size();
                state_translation_from_label[label] = U;
                unmarked_states.push_back(label);
            }

            dfa.transition_table[c][state] = state_translation_from_set[U];
        }
    }

    return dfa;
}

void printDFA(const DFA& D)
{
    cout << "Start state is " << D.start << endl;

    cout << "End states are: ";
    for (auto& a : D.ends) {
        cout << a << ' ';
    }
    cout << endl;

    for (const auto& it_row : D.transition_table)
    {
        auto& input = it_row.first;
        auto& row = it_row.second;

        cout << input << ": ";
        for (const auto& it_column : row)
        {
            cout << it_column.first << " -> " << it_column.second << ", ";
        }
        cout << endl;
    }
}

bool MatchInput(const DFA& dfa, const string& input)
{
    auto current_state = dfa.start;

    for (const auto& c : input)
    {
        if (dfa.alphabet.count(c))
            current_state = dfa.transition_table.at(c).at(current_state);
        else
            return false;
    }
    if (find(dfa.ends.begin(), dfa.ends.end(), current_state) != dfa.ends.end())
        return true;
    else
        return false;
}

NSA MakeNSA(const string& input)
{
    string str = input;
    vector<int> vec;
    int prior = 0;
    int i = 0;

    InsertDotsInplace(str);

    for (int i = 0; i < str.size(); ++i) 
    {
        switch (str[i]) 
        {
        case '(': {++prior; break; }
        case ')': {--prior; break; }
        case '+': {vec.push_back(3 + prior * 3); break; } //high
        case '*': {vec.push_back(3 + prior * 3); break; } //high
        case '|': {vec.push_back(2 + prior * 3); break; } //medium
        case '.': {vec.push_back(1 + prior * 3); break; } //low
        default: break;
        }
        //if (prior < 0) {
        //    cout << "Invalid in da house" << endl;
        //    return -1;
        //}
    }

    str.erase(remove_if(str.begin(), str.end(), [](const auto & c) {return c == '(' || c == ')'; }), str.end());

    Tree tree(str, vec);
    tree.parse();
    return BuildFromParseTree(&tree);
}

void Repl()
{
read_regexpr:
    string str;
    string ws;
    cout << "Give me your regexpr\n";
    getline(cin, str);
    if (str.length() == 0) goto read_regexpr;

    NSA my_nsa = MakeNSA(str);
    //PrintNSA(my_nsa);
    DFA my_dfa = MakeDFA(my_nsa);
    printDFA(my_dfa);

match_input:
    cout << "Give me your string\n";
    getline(cin, str);

    if (str == "~") goto read_regexpr;
    else
    {
        if (MatchInput(my_dfa, str))
            cout << "Yes\n";
        else
            cout << "No\n";

        goto match_input;
    }
}

int main() 
{
    Repl();

    return 0;
}