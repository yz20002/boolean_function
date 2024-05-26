#include <algorithm>
#include <atomic>
#include <iostream>
#include <fstream>
#include <numeric>
#include <stdlib.h>
#include <vector>
#include <time.h>

#include "ortools/base/logging.h"
#include "ortools/sat/cp_model.h"
#include "ortools/sat/cp_model.pb.h"
#include "ortools/sat/cp_model_solver.h"
#include "ortools/sat/model.h"
#include "ortools/sat/sat_parameters.pb.h"
#include "ortools/util/sorted_interval_list.h"
#include "ortools/util/time_limit.h"

using std::atomic;
using std::cout;
using std::min;
using std::vector;
using std::unordered_map;
using std::map;
using std::ostream;
using std::ofstream;

// binomiālkoeficients
int64_t comb(int n, int k) {
    return
        (k > n) ? 0 :
        (k == 0 || k == n) ? 1 :
        (k == 1 || k == n - 1) ? n :
        (k + k < n) ?
        (comb(n - 1, k - 1) * n) / k :
        (comb(n - 1, k) * n) / (n - k);
}

template <typename Type>
void print(ostream& stream, const vector<Type>& arr, int line) {
    for (size_t i = 0; i < arr.size(); ++i) {
        stream << arr[i] << ' ';
    }
    for (int i = 0; i < line; ++i) {
        stream << '\n';
    }
}

// polinomu dalīšana
template <typename Type>
bool dividePolynomialByPolynomial(vector<Type>& iNumerator, const vector<Type>& iDenominator)
{
    size_t dN(iNumerator.size() - 1), dD(iDenominator.size() - 1);

    bool zero = true;
    for (size_t i = 0; i <= dD; ++i) {
        if (iDenominator[i]) {
            zero = false;
            break;
        }
    }
    if (zero) {
        return false;
    }

    zero = true;
    for (size_t i = 0; i <= dN; ++i) {
        if (iNumerator[i]) {
            zero = false;
            break;
        }
    }
    if (zero) {
        return true;
    }

    if (dN < dD) {
        return false;
    }
    if (dD == 0 && iDenominator[0] == 1) {
        return true;
    }
    if (dD == 0 && iDenominator[0] != 0) {
        return false;
    }

    vector<Type> iWorking(iNumerator), iQuotient;

    size_t i;
    Type iTemp;

    while (dN >= dD)
    {
        if (iWorking[dN] % iDenominator[dD] != 0) {
            return false;
        }

        iTemp = iWorking[dN] / iDenominator[dD];
        iQuotient.insert(iQuotient.begin(), iTemp);

        for (i = 0; i <= dD; ++i) {
            iWorking[dN - i] -= iTemp * iDenominator[dD - i];
        }
        dN--;
        while (iWorking[dN] == 0 && dN >= 1 && dN >= dD) {
            iQuotient.insert(iQuotient.begin(), 0);
            dN--;
        }
    }

    for (i = 0; i <= dN; ++i)
    {
        if (iWorking[i] != 0)
            return false;
    }

    iNumerator = iQuotient;

    return true;
}

// funkcija atrod visus ai un bk koeficientus
struct BooleanFunction {
    const int N;
    int n, d, log;
    const bool special_14_5, opt;
    vector<int64_t> max_bk, min_bk;
    vector<vector<int>> solutions_ai;
    vector<vector<int64_t>> bk_coeffs;
    vector<bool> ci_results;
    ofstream file;

    BooleanFunction(int variables, int degree, int logging, bool special, bool optimization) : N(variables), n(variables), max_bk(variables + 1), min_bk(variables + 1), d(degree), log(logging), special_14_5(special), opt(optimization) {}

    void PrintMaxMin() {
        cout << "MAX: ";
        file << "MAX: ";
        for (size_t i = 0; i < max_bk.size(); ++i) {
            cout << max_bk[i] << ' ';
            file << max_bk[i] << ' ';
        }
        cout << '\n';
        file << '\n';
        cout << "MIN: ";
        file << "MIN: ";
        for (size_t i = 0; i < min_bk.size(); ++i) {
            cout << min_bk[i] << ' ';
            file << min_bk[i] << ' ';
        }
        cout << '\n';
        file << '\n';
    }

    void PrintBinMaxMin(const vector<int64_t>& bin_coef) {
        cout << '\n' << "n: " << n << '\t' << "d: " << d << '\n';
        file << '\n' << "n: " << n << '\t' << "d: " << d << '\n';
        cout << "BIN: ";
        file << "BIN: ";
        for (size_t i = 0; i < bin_coef.size(); ++i) {
            cout << bin_coef[i] << ' ';
            file << bin_coef[i] << ' ';
        }
        cout << '\n';
        file << '\n';
        PrintMaxMin();
    }

    struct Statistic;

    // koka struktūra priekš polinomiem un to sadalījumiem
    struct Polynomial {
        vector<int64_t> coef_bk;
        vector<Statistic*> stat_l;
        Statistic* elem_r;

        Polynomial(Statistic* root, const vector<int64_t>& bk) : elem_r(root), coef_bk(bk) {}

        Statistic* AddStat_l(Statistic* stat) {
            stat_l.push_back(stat);
            return stat;
        }

        bool CheckStat_l() {
            return stat_l.size();
        }

        bool RemoveStat_l(Statistic* stat) {
            if (find(stat_l.begin(), stat_l.end(), stat) == stat_l.end()) {
                cout << "ERROR" << ' ' << stat_l.size() << '\n';
            }
            else {
                stat_l.erase(find(stat_l.begin(), stat_l.end(), stat));

                return stat_l.size();
            }
            return false;
        }

        bool RemoveStat_l_index(Statistic* stat, int index) {
            stat_l.erase(stat_l.begin() + index);
        }

        void RemoveAll() {
            if (!stat_l[0]->poly_0->stat_l.size()) {
                while (stat_l.size()) {
                    stat_l[0]->elem_r = nullptr;
                    stat_l.erase(stat_l.begin());
                }
                return;
            }

            while (stat_l.size()) {
                stat_l[0]->poly_0->RemoveAll();
                stat_l[0]->poly_1->RemoveAll();

                stat_l.erase(stat_l.begin());
            }
        }
    };

    // koka struktūra priekš polinomiem un to sadalījumiem
    struct Statistic {
        bool status;
        Polynomial* poly_0, * poly_1, * elem_r;

        Statistic(Polynomial* root, const vector<int64_t>& coef_0, const vector<int64_t>& coef_1) : elem_r(root), poly_0(new Polynomial(this, coef_0)), poly_1(new Polynomial(this, coef_1)), status(false) {}

        bool CheckStatistic() {
            return poly_0->stat_l.size() && poly_1->stat_l.size();
        }

        bool RemoveLevel() {
            Statistic* del = this;
            Polynomial* root = elem_r;

            elem_r = nullptr;

            while (!root->RemoveStat_l(del) && root->elem_r && !root->elem_r->CheckStatistic()) {
                del = root->elem_r;

                if (del->poly_0 == root) {
                    del->poly_1->RemoveAll();
                }
                else {
                    del->poly_0->RemoveAll();
                }

                root = del->elem_r;
            }

            if (!root->elem_r && !root->stat_l.size()) {
                return true;
            }

            return false;
        }

        bool RemoveFullLevel() {
            Statistic* del = this;
            Polynomial* root = elem_r;

            elem_r = nullptr;

            while (!root->RemoveStat_l(del) && root->elem_r) {
                del = root->elem_r;

                if (del->poly_0 == root) {
                    del->poly_1->RemoveAll();
                    del->poly_1->elem_r = nullptr;
                }
                else {
                    del->poly_0->RemoveAll();
                    del->poly_0->elem_r = nullptr;
                }

                root = del->elem_r;
            }

            if (!root->elem_r && !root->stat_l.size()) {
                return true;
            }

            return false;
        }
    };

    // lineārās programmēšanas funkcija
    void SearchForAllSolutions(const vector<vector<int64_t>>& bk_expr, int deg) {
        operations_research::sat::CpModelBuilder cp_model;
        vector<operations_research::sat::IntVar> ai(deg + 1);
        for (int i = 0; i < deg + 1; ++i) {
            ai[i] = cp_model.operations_research::sat::CpModelBuilder::NewIntVar(operations_research::Domain(-4097, 4096)).WithName("a" + i);
        }

        if (n != N) {
            for (int i = 0; i < n + 1; ++i) {
                cp_model.AddLinearConstraint(operations_research::sat::LinearExpr::WeightedSum(ai, bk_expr[i]), operations_research::Domain(min_bk[i], max_bk[i]));
            }
        }
        else {
            // n = 14, d = 5 īpaša statistika
            if (special_14_5) {
                cp_model.AddEquality(operations_research::sat::LinearExpr::WeightedSum(ai, bk_expr[0]), 0);
                cp_model.AddEquality(operations_research::sat::LinearExpr::WeightedSum(ai, bk_expr[1]), 14);
                cp_model.AddEquality(operations_research::sat::LinearExpr::WeightedSum(ai, bk_expr[2]), 91);
                for (int i = 3; i < n - 2; ++i) {
                    cp_model.AddLinearConstraint(operations_research::sat::LinearExpr::WeightedSum(ai, bk_expr[i]), operations_research::Domain(0, max_bk[i]));
                }
                cp_model.AddEquality(operations_research::sat::LinearExpr::WeightedSum(ai, bk_expr[n - 2]), 0);
                cp_model.AddEquality(operations_research::sat::LinearExpr::WeightedSum(ai, bk_expr[n - 1]), 0);
                cp_model.AddEquality(operations_research::sat::LinearExpr::WeightedSum(ai, bk_expr[n]), 1);
            }
            else {
                cp_model.AddEquality(operations_research::sat::LinearExpr::WeightedSum(ai, bk_expr[0]), 0);
                cp_model.AddEquality(operations_research::sat::LinearExpr::WeightedSum(ai, bk_expr[1]), n);

                for (int i = 2; i < n + 1; ++i) {
                    cp_model.AddLinearConstraint(operations_research::sat::LinearExpr::WeightedSum(ai, bk_expr[i]), operations_research::Domain(0, max_bk[i]));
                }
            }
        }

        operations_research::sat::Model model;

        vector<int> solution(deg + 1);
        int num_solutions = 0;
        solutions_ai.clear();
        model.Add(operations_research::sat::NewFeasibleSolutionObserver([&](const operations_research::sat::CpSolverResponse& r) {
            ++num_solutions;
            //LOG(INFO) << "Solution " << num_solutions;
            for (int i = 0; i < deg + 1; ++i) {
                //LOG(INFO) << "  a" << i << " = " << operations_research::sat::SolutionIntegerValue(r, ai[i]);
                solution[i] = operations_research::sat::SolutionIntegerValue(r, ai[i]);
            }
            solutions_ai.push_back(solution);
            //LOG(INFO) << '\n';
            }));

        operations_research::sat::SatParameters parameters;
        parameters.set_enumerate_all_solutions(true);
        parameters.set_num_workers(1);
        parameters.set_cp_model_presolve(false);

        model.Add(operations_research::sat::NewSatParameters(parameters));
        const operations_research::sat::CpSolverResponse response = operations_research::sat::SolveCpModel(cp_model.Build(), &model);

        LOG(INFO) << "Risinajumu skaits: " << num_solutions;
    }

    void GetAllCoefficients() {
        int binom_deg = n - d;
        vector<int64_t> binom((binom_deg >= 1) ? binom_deg + 1 : 1);

        for (int i = 0; i < binom_deg + 1; ++i) {
            binom[i] = comb(binom_deg, i);
        }

        vector<vector<int64_t>> bk_expr(n + 1, vector<int64_t>((binom_deg <= 0) ? n + 1 : d + 1));

        if (binom_deg >= 1) {
            bk_expr[0][0] = 1;

            int max_mon = min(d, binom_deg);
            for (int i = 1; i < max_mon; ++i) {
                for (int j = 0; j < i + 1; ++j) {
                    bk_expr[i][j] = binom[i - j];
                }
            }

            if (binom_deg > d) {
                for (int i = max_mon; i < n - max_mon + 1; ++i) {
                    for (int j = 0; j < max_mon + 1; ++j) {
                        bk_expr[i][j] = binom[i - j];
                    }
                }
            }
            else {
                for (int i = max_mon; i < n - max_mon + 1; ++i) {
                    for (int j = 0; j < max_mon + 1; ++j) {
                        bk_expr[i][i - max_mon + j] = binom[j];
                    }
                }
            }

            for (int i = n - max_mon + 1; i < n; ++i) {
                for (int j = 0; j < n - i + 1; ++j) {
                    bk_expr[i][d - (n - i - j)] = binom[j];
                }
            }

            bk_expr[n][d] = 1;
        }
        else {
            for (int i = 0; i < n + 1; ++i) {
                bk_expr[i][i] = 1;
            }
        }

        SearchForAllSolutions(bk_expr, (binom_deg >= 0) ? d : n);

        vector<int64_t> poly_coef(n + 1, 0);
        int64_t temp;
        bk_coeffs.resize(solutions_ai.size());
        if (n != N) {
            for (size_t i = 0; i < solutions_ai.size(); ++i) {
                for (int j = 0; j < n + 1; ++j) {
                    temp = 0;
                    for (size_t k = 0; k < solutions_ai[i].size(); k++) {
                        temp += solutions_ai[i][k] * bk_expr[j][k];
                    }
                    poly_coef[j] = temp;
                }

                bk_coeffs[i] = poly_coef;
            }
        }
        else {
            // optimizācijai - aprēķina maks.un min.nākamā līmeņa bk vērtības
            max_bk.pop_back();
            min_bk.pop_back();
            vector<int64_t> bin_coef(n);

            for (int k = 0; k < n; ++k) {
                max_bk[k] = 0;
                min_bk[k] = comb(n, k);
                bin_coef[k] = comb(n - 1, k);
            }

            bool b0_0 = false;
            for (size_t i = 0; i < solutions_ai.size(); ++i) {
                temp = 0;
                for (size_t j = 0; j < solutions_ai[i].size(); j++) {
                    temp += solutions_ai[i][j] * bk_expr[0][j];
                }
                poly_coef[0] = temp;


                if (poly_coef[0] == 1) {
                    max_bk[0] = 1;
                }
                else {
                    b0_0 = true;
                }

                for (int j = 1; j < n; ++j) {
                    temp = 0;
                    for (size_t k = 0; k < solutions_ai[i].size(); k++) {
                        temp += solutions_ai[i][k] * bk_expr[j][k];
                    }
                    poly_coef[j] = temp;

                    if (poly_coef[j] > max_bk[j]) {
                        max_bk[j] = poly_coef[j];
                    }
                    if (poly_coef[j] < min_bk[j]) {
                        min_bk[j] = poly_coef[j];
                    }
                }

                temp = 0;
                for (size_t j = 0; j < solutions_ai[i].size(); j++) {
                    temp += solutions_ai[i][j] * bk_expr[n][j];
                }
                poly_coef[n] = temp;

                bk_coeffs[i] = poly_coef;
            }

            if (b0_0) {
                min_bk[0] = 0;
            }
            else {
                min_bk[0] = 1;
            }

            for (int i = 1; i < n; ++i) {
                min_bk[i] -= bin_coef[i - 1];
                if (min_bk[i] < 0) {
                    min_bk[i] = 0;
                }
                if (max_bk[i] > bin_coef[i]) {
                    max_bk[i] = bin_coef[i];
                }
            }
        }
    }

    // lineārās programmēšanas funkcija ci vienādojumu sistēmai
    void CheckAllSolutions(const vector<int64_t>& bk_coef, const vector<vector<int64_t>>& bk_coeffs_0, const vector<vector<int64_t>>& bk_coeffs_1) {
        int64_t deg = bk_coef.size() - 1;
        size_t ci_count = bk_coeffs_0.size();
        vector<int64_t> ci_expr(ci_count, 1);

        ci_results.resize(ci_count);

        operations_research::sat::CpModelBuilder cp_model;
        vector<operations_research::sat::IntVar> ci(ci_count);
        for (size_t i = 0; i < ci_count; ++i) {
            ci_results[i] = false;
            ci[i] = cp_model.operations_research::sat::CpModelBuilder::NewIntVar(operations_research::Domain(0, 4096)).WithName("c" + i);
        }

        // ci
        cp_model.AddEquality(operations_research::sat::LinearExpr::WeightedSum(ci, ci_expr), deg);

        for (int i = 0; i < deg; ++i) {
            // 0
            for (size_t j = 0; j < ci_count; ++j) {
                ci_expr[j] = bk_coeffs_0[j][i];
            }
            cp_model.AddEquality(operations_research::sat::LinearExpr::WeightedSum(ci, ci_expr), (deg - i) * bk_coef[i]);

            // 1
            for (size_t j = 0; j < ci_count; ++j) {
                ci_expr[j] = bk_coeffs_1[j][i];
            }
            cp_model.AddEquality(operations_research::sat::LinearExpr::WeightedSum(ci, ci_expr), (i + 1) * bk_coef[i + 1]);
        }

        operations_research::sat::Model model;

        operations_research::sat::SatParameters parameters;
        parameters.set_enumerate_all_solutions(true);
        parameters.set_num_workers(1);
        parameters.set_cp_model_presolve(false);

        model.Add(operations_research::sat::NewSatParameters(parameters));

        atomic<bool> stopped(false);

        model.GetOrCreate<operations_research::TimeLimit>()->RegisterExternalBooleanAsLimit(&stopped);

        model.Add(operations_research::sat::NewFeasibleSolutionObserver([&](const operations_research::sat::CpSolverResponse& r) {
            if (ci_count > 10) {
                for (int j = 0; j < ci_count; ++j) {
                    ci_results[j] = true;
                }
                stopped = true;
            }

            for (int i = 0; i < ci_count; ++i) {
                //LOG(INFO) << "  c" << i << " = " << operations_research::sat::SolutionIntegerValue(r, ci[i]);

                if (operations_research::sat::SolutionIntegerValue(r, ci[i])) {
                    ci_results[i] = true;
                }
            }
            //LOG(INFO) << '\n';

            if (all_of(ci_results.begin(), ci_results.end(), [](bool i) {return i; })) {
                stopped = true;
            }

            }));

        const operations_research::sat::CpSolverResponse response = SolveCpModel(cp_model.Build(), &model);
    }

    // galvenā funckija
    void FindRepresentingPolynomial() {
        clock_t time_start = clock();
        double time_diff;

        file.open("out_" + std::to_string(n) + "_" + std::to_string(d) + ".txt");

        // Sākums: atrod 0. un 1. līmeni un pārbauda tos
        for (int k = 0; k < n + 1; ++k) {
            max_bk[k] = comb(n, k);
        }

        cout << "n: " << n << '\t' << "d: " << d << '\n';
        file << "n: " << n << '\t' << "d: " << d << '\n';
        PrintMaxMin();

        // atrod 0. limeni
        GetAllCoefficients();

        vector<Polynomial*>* roots = new vector<Polynomial*>;
        for (size_t i = 0; i < bk_coeffs.size(); ++i) {
            roots->push_back(new Polynomial(nullptr, bk_coeffs[i]));
        }

        file << '\n' << "Roots: " << roots->size() << "\n\n";
        cout << '\n' << "Roots: " << roots->size() << '\n';
        for (size_t i = 0; i < roots->size(); ++i) {
            print(file, (*roots)[i]->coef_bk, 1);
        }

        if (roots->size() == 0) {
            cout << '\n' << "NO ROOTS" << '\n';
            file << '\n' << "NO ROOTS" << '\n';

            file.close();
            return;
        }

        time_diff = double(clock() - time_start) / double(CLOCKS_PER_SEC);
        cout << "Izpildes laiks : " << time_diff / 60 << " min." << '\n';

        vector<int64_t> bin_coef(n);
        for (int k = 0; k < n; ++k) {
            bin_coef[k] = comb(n - 1, k);
        }

        n--;

        PrintBinMaxMin(bin_coef);

        // atrod 1. līmeņa ar bn = 0 iespējamās vērtības
        GetAllCoefficients();

        map<vector<int64_t>, vector<Statistic*>> bk_index;
        Statistic* bk_stat;
        vector<vector<Statistic*>> full_bk_level, level;
        vector<Statistic*> poly_level, stats, bk_stats;
        vector<int64_t> binom;
        vector<vector<int64_t>> bk_level_0, bk_level_1, bin_exp(2);

        for (int i = 1; i > -1; i--) {
            if (N - i - d + 1 <= 0) {
                bin_exp[1 - i] = { 1 };
            }
            else {
                binom.resize(N - i - d + 1);
                for (int k = 0; k < N - i - d + 1; ++k) {
                    binom[k] = comb(N - i - d, k);
                    bin_exp[1 - i] = binom;
                }
            }
        }

        vector<int64_t> bk(n + 1), bk_0(n + 1), bk_1(n + 1);
        int it_h = -1, it_l = -1;
        int64_t end_h = roots->size() - 1, end_l = bk_coeffs.size() - 1;

        // mēgiņa sadalīt katru 0. līmeņa statistiku(atņem no 0. līmeņa 1. līmeņa statistikas ar bn = 0)
        while (it_h < end_h) {
            ++it_h;
            bk = (*roots)[it_h]->coef_bk;

            if (log == 1) {
                print(file, bk, 2);
            }

            if (opt && bk_index.find(bk) != bk_index.end()) {
                if (bk_index[bk].size()) {
                    poly_level.clear();
                    for (size_t l = 0; l < bk_index[bk].size(); ++l) {
                        bk_stat = (*roots)[it_h]->AddStat_l(new Statistic((*roots)[it_h], bk_index[bk][l]->poly_0->coef_bk, bk_index[bk][l]->poly_1->coef_bk));
                        poly_level.push_back(bk_stat);
                        full_bk_level.push_back({ bk_stat });
                    }
                    level.push_back(poly_level);
                    continue;
                }
                else {
                    roots->erase(find(roots->begin(), roots->end(), (*roots)[it_h]));
                    end_h--;
                    it_h--;
                    continue;
                }
            }

            bk_level_0.clear();
            bk_level_1.clear();

            int last_i = 0;
            bool cont = false;

            it_l = -1;
            while (it_l < end_l) {
                ++it_l;
                bk_0 = bk_coeffs[it_l];
                if (last_i) {
                    if (bk_0[last_i] > bk[last_i]) {
                        continue;
                    }
                    if (bk[last_i] - bk_0[last_i] > bin_coef[last_i - 1]) {
                        continue;
                    }
                }

                if (bk_0[0] != bk[0]) {
                    continue;
                }

                for (int i = 1; i < n + 1; ++i) {
                    if (bk_0[i] > bk[i]) {
                        cont = true;
                        last_i = i;
                        break;
                    }

                    if (bk[i] - bk_0[i] > bin_coef[i - 1]) {
                        cont = true;
                        last_i = i;
                        break;
                    }

                    bk_1[i - 1] = bk[i] - bk_0[i];
                }

                if (cont) {
                    cont = false;
                    continue;
                }

                last_i = 0;
                bk_1[n] = bk[n + 1];

                vector<vector<int64_t>> p;
                p.resize(2);

                // p0
                p[0] = bk_0;
                std::reverse(p[0].begin(), p[0].end());
                if (!dividePolynomialByPolynomial(p[0], bin_exp[0])) {
                    continue;
                }

                // p1 - p0
                p[1] = bk_1;
                p[0] = bk_0;
                for (int i = 0; i < n + 1; ++i) {
                    p[1][i] -= p[0][i];
                }
                std::reverse(p[1].begin(), p[1].end());
                if (!dividePolynomialByPolynomial(p[1], bin_exp[1])) {
                    continue;
                }

                bk_level_0.push_back(bk_0);
                bk_level_1.push_back(bk_1);

                if (log == 1) {
                    print(file, bk_0, 1);
                    file << '\t';
                    print(file, bk_1, 1);
                }
            }

            if (bk_level_0.size()) {
                // pārbauda ci vienādojumu sistēmu
                CheckAllSolutions(bk, bk_level_0, bk_level_1);

                if (any_of(ci_results.begin(), ci_results.end(), [](bool j) {return j; })) {
                    poly_level.clear();

                    for (size_t k = 0; k < ci_results.size(); ++k) {
                        if (ci_results[k]) {
                            // n = 14, d = 5 īpaša statistika
                            if (special_14_5) {
                                if (bk_level_0[k][3] == 182) {
                                    bk_stat = (*roots)[it_h]->AddStat_l(new Statistic((*roots)[it_h], bk_level_0[k], bk_level_1[k]));
                                    poly_level.push_back(bk_stat);
                                    full_bk_level.push_back({ bk_stat });
                                }
                            }
                            else {
                                bk_stat = (*roots)[it_h]->AddStat_l(new Statistic((*roots)[it_h], bk_level_0[k], bk_level_1[k]));
                                poly_level.push_back(bk_stat);
                                full_bk_level.push_back({ bk_stat });
                            }
                        }
                    }

                    if (opt) {
                        bk_index[bk] = poly_level;
                    }

                    level.push_back(poly_level);
                }
                else {
                    if (opt) {
                        bk_index[bk] = {};
                    }

                    roots->erase(find(roots->begin(), roots->end(), (*roots)[it_h]));
                    end_h--;
                    it_h--;
                }
            }
            else {
                if (opt) {
                    bk_index[bk] = {};
                }

                roots->erase(find(roots->begin(), roots->end(), (*roots)[it_h]));
                end_h--;
                it_h--;
            }

            if (log == 1) {
                file << "\n\n";
            }
        }

        time_diff = double(clock() - time_start) / double(CLOCKS_PER_SEC);
        cout << "Izpildes laiks : " << time_diff / 60 << " min." << '\n';

        cout << '\n' << "LIM 1" << "\n\n";
        file << '\n' << "LIM 1" << "\n\n";

        size_t count = 0;
        cout << "Full level: ";
        file << "Full level: ";
        for (size_t i = 0; i < level.size(); ++i) {
            count += level[i].size();
        }
        cout << count << "\n\n";
        file << count << "\n\n";
        for (size_t i = 0; i < roots->size(); ++i) {
            print(file, (*roots)[i]->coef_bk, 1);
            for (size_t j = 0; j < (*roots)[i]->stat_l.size(); ++j) {
                file << '\n';
                print(file, (*roots)[i]->stat_l[j]->poly_0->coef_bk, 1);
                file << '\t';
                print(file, (*roots)[i]->stat_l[j]->poly_1->coef_bk, 0);
            }
            file << "\n\n\n";
        }


        vector<Statistic*> s;
        vector<vector<int64_t>> p;
        vector<size_t> l_size;
        vector<vector<Statistic*>> new_level, new_full_bk_level;
        vector<bool> min_ok(n + 2), max_ok(n + 2);

        // cikls 2., 3., ... līmeņa sadalījumiem
        int lim = 2;
        while (n > 0 && count) {
            new_level.clear();
            new_full_bk_level.clear();

            max_bk.pop_back();
            min_bk.pop_back();
            bin_coef.pop_back();
            min_ok.pop_back();
            max_ok.pop_back();

            for (int k = 0; k < n; ++k) {
                max_bk[k] = 0;
                min_bk[k] = comb(n, k);
                bin_coef[k] = comb(n - 1, k);

                min_ok[k] = false;
                max_ok[k] = false;
            }

            if (N - lim - d + 1 <= 0) {
                bin_exp.insert(bin_exp.begin(), { 1 });
            }
            else {
                binom.resize(N - lim - d + 1);
                for (int k = 0; k < N - lim - d + 1; ++k) {
                    binom[k] = comb(N - lim - d, k);
                }
                bin_exp.insert(bin_exp.begin(), binom);
            }

            bool b0_0 = false;
            vector<int64_t> bk_0, bk_1;
            vector<bool> min_ok(n + 1), max_ok(n + 1);

            // optimizācijai - aprēķina maks.un min.nākamā līmeņa bk vērtības
            // meklē tikai bk0 vērtības
            for (size_t i = 0; i < level.size(); ++i) {
                bool cont;
                for (size_t j = 0; j < level[i].size(); ++j) {
                    bk_0 = level[i][j]->poly_0->coef_bk;
                    bk_1 = level[i][j]->poly_1->coef_bk;

                    int64_t num;

                    cont = false;
                    for (int k = 0; k < n; ++k) {
                        if (min_ok[k] && max_ok[k]) {
                            continue;
                        }

                        // bk_0
                        num = bk_0[k];
                        if (num > max_bk[k]) {
                            max_bk[k] = num;
                            cont = true;
                        }
                        if (num < min_bk[k]) {
                            min_bk[k] = num;
                            cont = true;
                        }
                        // bk_1
                        num = bk_1[k];
                        if (num > max_bk[k]) {
                            max_bk[k] = num;
                            cont = true;
                        }
                        if (num < min_bk[k]) {
                            min_bk[k] = num;
                            cont = true;
                        }
                    }

                    if (j % 32 == 0 && cont) {
                        cont = false;
                        if (min_bk[0] == 0) {
                            min_ok[0] = true;
                            cont = true;
                        }
                        if (max_bk[0] == 1) {
                            max_ok[0] = true;
                            cont = true;
                        }
                        for (int k = 1; k < n; ++k) {
                            if (min_bk[k] < bin_coef[k - 1]) {
                                min_ok[k] = true;
                                cont = true;
                            }
                            if (max_bk[k] >= bin_coef[k]) {
                                max_ok[k] = true;
                                cont = true;
                            }
                        }

                        if (cont) {
                            for (int k = 0; k < n; ++k) {
                                if (!(min_ok[k] && max_ok[k])) {
                                    cont = false;
                                    break;
                                }
                            }
                            if (cont) {
                                break;
                            }
                        }
                    }
                }
            }

            for (int k = 1; k < n; ++k) {
                min_bk[k] -= bin_coef[k - 1];
                if (min_bk[k] < 0) {
                    min_bk[k] = 0;
                }
                if (max_bk[k] > bin_coef[k]) {
                    max_bk[k] = bin_coef[k];
                }
            }

            n--;

            PrintBinMaxMin(bin_coef);

            // atrod nākamā līmeņa ar bn = 0 iespējamās vērtības
            GetAllCoefficients();

            if (opt) {
                bk_index.clear();
            }

            for (size_t i = 0; i < level.size(); ++i) {
                poly_level.clear();
                bk_level_0.clear();
                bk_level_1.clear();

                bool check = false;
                bk_1 = vector<int64_t>(n + 1, 0);

                // mēgiņa sadalīt katru k.līmeņa statistiku(atņem no k.līmeņa k + 1. līmeņa statistikas ar bn = 0)
                for (size_t j = 0; j < level[i].size(); ++j) {
                    bool cont = false;
                    stats.clear();
                    if (check) {
                        if (check = (level[i][j]->elem_r == nullptr) ? true : false) {
                            continue;
                        }
                    }

                    Polynomial* poly = level[i][j]->poly_0;
                    for (int k = 0; k < 2; ++k) {
                        if (k == 1) {
                            poly = level[i][j]->poly_1;
                        }
                        bk = poly->coef_bk;

                        if (log == 1) {
                            file << '\n';
                            print(file, bk, 2);
                        }

                        if (opt && bk_index.find(bk) != bk_index.end()) {
                            if (bk_index[bk].size()) {
                                for (size_t l = 0; l < bk_index[bk].size(); ++l) {
                                    stats.push_back(poly->AddStat_l(new Statistic(poly, bk_index[bk][l]->poly_0->coef_bk, bk_index[bk][l]->poly_1->coef_bk)));
                                }
                                continue;
                            }
                            else {
                                level[i][j]->RemoveFullLevel();
                                stats.clear();
                                check = true;
                                break;
                            }
                        }

                        bk_level_0.clear();
                        bk_level_1.clear();

                        int last_m = 0;
                        for (size_t l = 0; l < bk_coeffs.size(); ++l) {
                            bk_0 = bk_coeffs[l];
                            if (last_m) {
                                if (bk_0[last_m] > bk[last_m]) {
                                    continue;
                                }
                                if (bk[last_m] - bk_0[last_m] > bin_coef[last_m - 1]) {
                                    continue;
                                }
                            }

                            if (bk_0[0] != bk[0]) {
                                continue;
                            }

                            for (int m = 1; m < n + 1; ++m) {
                                if (bk_0[m] > bk[m]) {
                                    cont = true;
                                    last_m = m;
                                    break;
                                }
                                if (bk[m] - bk_0[m] > bin_coef[m - 1]) {
                                    cont = true;
                                    last_m = m;
                                    break;
                                }

                                bk_1[m - 1] = bk[m] - bk_0[m];
                            }

                            if (cont) {
                                cont = false;
                                continue;
                            }

                            last_m = 0;
                            bk_1[n] = bk[n + 1];

                            bk_level_0.push_back(bk_0);
                            bk_level_1.push_back(bk_1);

                            if (log == 1) {
                                print(file, bk_0, 1);
                                file << '\t';
                                print(file, bk_1, 1);
                            }
                        }

                        if (bk_level_0.size()) {
                            // pārbauda ci vienādojumu sistēmu
                            CheckAllSolutions(bk, bk_level_0, bk_level_1);

                            if (any_of(ci_results.begin(), ci_results.end(), [](bool l) {return l; })) {
                                bk_stats.clear();

                                for (size_t m = 0; m < ci_results.size(); ++m) {
                                    if (ci_results[m]) {
                                        bk_stat = poly->AddStat_l(new Statistic(poly, bk_level_0[m], bk_level_1[m]));
                                        bk_stats.push_back(bk_stat);

                                        stats.push_back(bk_stat);
                                    }
                                }

                                if (opt) {
                                    bk_index[bk] = bk_stats;
                                }
                            }
                            else {
                                if (opt) {
                                    bk_index[bk] = {};
                                }

                                level[i][j]->RemoveFullLevel();
                                stats.clear();
                                check = true;
                                break;
                            }
                        }
                        else {
                            if (opt) {
                                bk_index[bk] = {};
                            }

                            level[i][j]->RemoveFullLevel();
                            stats.clear();
                            check = true;
                            break;
                        }
                    }

                    if (stats.size()) {
                        poly_level.reserve(poly_level.size() + stats.size());
                        poly_level.insert(poly_level.end(), stats.begin(), stats.end());
                    }
                }

                new_level.push_back(poly_level);
            }

            time_diff = double(clock() - time_start) / double(CLOCKS_PER_SEC);
            cout << "Izpildes laiks : " << time_diff / 60 << " min." << '\n';

            vector<vector<int>> p0_count;
            int A = 0, B = 0, C = 0, D = 0, E = 0, F = 0, G = 0, H = 0, I = 0, J = 0, K = 0, L = 0, M = 0, N = 0, O = 0, P = 0, Q = 0, R = 0, S = 0, T = 0, U = 0, V = 0, W = 0, X = 0, Y = 0, Z = 0, Z1 = 0, Z2 = 0, Z3 = 0, Z4 = 0;

            bool cont;
            it_h = 0;
            end_h = full_bk_level.size();
            cout << '\n' << "LIM " << lim << '\n';
            file << '\n' << "LIM " << lim << '\n';
            // sadalījuma līmeņa pārbaude
            while (it_h < end_h) {
                poly_level = full_bk_level[it_h];
                cont = false;

                for (size_t i = 0; i < poly_level.size(); ++i) {
                    if (poly_level[i]->elem_r == nullptr) {
                        cont = true;
                        break;
                    }
                    else if (!poly_level[i]->CheckStatistic()) {
                        cont = true;
                        break;
                    }
                }

                if (cont) {
                    ++it_h;
                    continue;
                }

                cout << it_h << ' ' << end_h << '\n';

                if (lim == 2) {
                    p.resize(4);
                    s.resize(2);
                    l_size.resize(2);

                    l_size[0] = poly_level[0]->poly_0->stat_l.size();
                    l_size[1] = poly_level[0]->poly_1->stat_l.size();

                    for (size_t l0 = 0; l0 < l_size[0]; ++l0) {
                        s[0] = poly_level[0]->poly_0->stat_l[l0];

                        for (size_t l1 = 0; l1 < l_size[1]; ++l1) {
                            s[1] = poly_level[0]->poly_1->stat_l[l1];

                            // p10 - p00
                            p[1] = s[1]->poly_0->coef_bk;
                            p[0] = s[0]->poly_0->coef_bk;
                            for (int i = 0; i < n + 1; ++i) {
                                p[1][i] -= p[0][i];
                            }
                            std::reverse(p[1].begin(), p[1].end());
                            if (!dividePolynomialByPolynomial(p[1], bin_exp[1])) {
                                ++B;
                                continue;
                            }

                            if (special_14_5) {
                                s[1]->status = true;
                                s[0]->status = true;

                                new_full_bk_level.push_back({ s[0], s[1] });
                                continue;
                            }

                            // p01 - p00
                            p[1] = s[0]->poly_1->coef_bk;
                            p[0] = s[0]->poly_0->coef_bk;
                            for (int i = 0; i < n + 1; ++i) {
                                p[1][i] -= p[0][i];
                            }
                            std::reverse(p[1].begin(), p[1].end());
                            if (!dividePolynomialByPolynomial(p[1], bin_exp[1])) {
                                ++A;
                                continue;
                            }

                            // p11 - p10 - p01 + p00
                            p[3] = s[1]->poly_1->coef_bk;
                            p[2] = s[1]->poly_0->coef_bk;
                            p[1] = s[0]->poly_1->coef_bk;
                            p[0] = s[0]->poly_0->coef_bk;
                            for (int i = 0; i < n + 1; ++i) {
                                p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                            }
                            std::reverse(p[3].begin(), p[3].end());
                            if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                ++C;
                                continue;
                            }

                            s[1]->status = true;
                            s[0]->status = true;

                            new_full_bk_level.push_back({ s[0], s[1] });
                        }
                    }
                }
                else if (lim == 3) {
                    p.resize(8);
                    s.resize(4);
                    l_size.resize(4);

                    l_size[0] = poly_level[0]->poly_0->stat_l.size();
                    l_size[1] = poly_level[0]->poly_1->stat_l.size();
                    l_size[2] = poly_level[1]->poly_0->stat_l.size();
                    l_size[3] = poly_level[1]->poly_1->stat_l.size();

                    for (size_t l0 = 0; l0 < l_size[0]; ++l0) {
                        s[0] = poly_level[0]->poly_0->stat_l[l0];

                        for (size_t l1 = 0; l1 < l_size[1]; ++l1) {
                            s[1] = poly_level[0]->poly_1->stat_l[l1];

                            // p010 - p000
                            p[1] = s[1]->poly_0->coef_bk;
                            p[0] = s[0]->poly_0->coef_bk;
                            for (int i = 0; i < n + 1; ++i) {
                                p[1][i] -= p[0][i];
                            }
                            std::reverse(p[1].begin(), p[1].end());
                            if (!dividePolynomialByPolynomial(p[1], bin_exp[1])) {
                                ++B;
                                continue;
                            }

                            for (size_t l2 = 0; l2 < l_size[2]; ++l2) {
                                s[2] = poly_level[1]->poly_0->stat_l[l2];

                                // p100 - p000
                                p[1] = s[2]->poly_0->coef_bk;
                                p[0] = s[0]->poly_0->coef_bk;
                                for (int i = 0; i < n + 1; ++i) {
                                    p[1][i] -= p[0][i];
                                }
                                std::reverse(p[1].begin(), p[1].end());
                                if (!dividePolynomialByPolynomial(p[1], bin_exp[1])) {
                                    ++C;
                                    continue;
                                }

                                for (size_t l3 = 0; l3 < l_size[3]; ++l3) {
                                    s[3] = poly_level[1]->poly_1->stat_l[l3];

                                    // p110 - p100 - p010 + p000
                                    p[3] = s[3]->poly_0->coef_bk;
                                    p[2] = s[2]->poly_0->coef_bk;
                                    p[1] = s[1]->poly_0->coef_bk;
                                    p[0] = s[0]->poly_0->coef_bk;
                                    for (int i = 0; i < n + 1; ++i) {
                                        p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                    }
                                    std::reverse(p[3].begin(), p[3].end());
                                    if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                        ++E;
                                        continue;
                                    }

                                    if (special_14_5) {
                                        s[3]->status = true;
                                        s[2]->status = true;
                                        s[1]->status = true;
                                        s[0]->status = true;

                                        new_full_bk_level.push_back({ s[0], s[1], s[2], s[3] });
                                        continue;
                                    }

                                    // p001 - p000
                                    p[1] = s[0]->poly_1->coef_bk;
                                    p[0] = s[0]->poly_0->coef_bk;
                                    for (int i = 0; i < n + 1; ++i) {
                                        p[1][i] -= p[0][i];
                                    }
                                    std::reverse(p[1].begin(), p[1].end());
                                    if (!dividePolynomialByPolynomial(p[1], bin_exp[1])) {
                                        ++A;
                                        continue;
                                    }

                                    // p101 - p100 - p001 + p000
                                    p[3] = s[2]->poly_1->coef_bk;
                                    p[2] = s[2]->poly_0->coef_bk;
                                    p[1] = s[0]->poly_1->coef_bk;
                                    p[0] = s[0]->poly_0->coef_bk;
                                    for (int i = 0; i < n + 1; ++i) {
                                        p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                    }
                                    std::reverse(p[3].begin(), p[3].end());
                                    if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                        ++D;
                                        continue;
                                    }

                                    // p011 - p010 - p001 + p000;
                                    p[3] = s[1]->poly_1->coef_bk;
                                    p[2] = s[1]->poly_0->coef_bk;
                                    p[1] = s[0]->poly_1->coef_bk;
                                    p[0] = s[0]->poly_0->coef_bk;
                                    for (int i = 0; i < n + 1; ++i) {
                                        p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                    }
                                    std::reverse(p[3].begin(), p[3].end());
                                    if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                        ++F;
                                        continue;
                                    }

                                    // p111 - p110 - p101 - p011 + p100 + p010 + p001 - p000;
                                    p[7] = s[3]->poly_1->coef_bk;
                                    p[6] = s[3]->poly_0->coef_bk;
                                    p[5] = s[2]->poly_1->coef_bk;
                                    p[4] = s[1]->poly_1->coef_bk;
                                    p[3] = s[2]->poly_0->coef_bk;
                                    p[2] = s[1]->poly_0->coef_bk;
                                    p[1] = s[0]->poly_1->coef_bk;
                                    p[0] = s[0]->poly_0->coef_bk;
                                    for (int i = 0; i < n + 1; ++i) {
                                        p[7][i] = p[7][i] - p[6][i] - p[5][i] - p[4][i] + p[3][i] + p[2][i] + p[1][i] - p[0][i];
                                    }
                                    std::reverse(p[7].begin(), p[7].end());
                                    if (!dividePolynomialByPolynomial(p[7], bin_exp[3])) {
                                        ++G;
                                        continue;
                                    }

                                    s[3]->status = true;
                                    s[2]->status = true;
                                    s[1]->status = true;
                                    s[0]->status = true;

                                    new_full_bk_level.push_back({ s[0], s[1], s[2], s[3] });
                                }
                            }
                        }
                    }
                }
                else if (lim == 4) {
                    p.resize(16);
                    s.resize(8);
                    l_size.resize(8);

                    l_size[0] = poly_level[0]->poly_0->stat_l.size();
                    l_size[1] = poly_level[0]->poly_1->stat_l.size();
                    l_size[2] = poly_level[1]->poly_0->stat_l.size();
                    l_size[3] = poly_level[2]->poly_0->stat_l.size();
                    l_size[4] = poly_level[1]->poly_1->stat_l.size();
                    l_size[5] = poly_level[2]->poly_1->stat_l.size();
                    l_size[6] = poly_level[3]->poly_0->stat_l.size();
                    l_size[7] = poly_level[3]->poly_1->stat_l.size();

                    // pārbauda 4. līmeni
                    // p000.
                    for (size_t l0 = 0; l0 < l_size[0]; ++l0) {
                        s[0] = poly_level[0]->poly_0->stat_l[l0];

                        // p001.
                        for (size_t l1 = 0; l1 < l_size[1]; ++l1) {
                            s[1] = poly_level[0]->poly_1->stat_l[l1];

                            // p010.
                            for (size_t l2 = 0; l2 < l_size[2]; ++l2) {
                                s[2] = poly_level[1]->poly_0->stat_l[l2];

                                // p100.
                                for (size_t l3 = 0; l3 < l_size[3]; ++l3) {
                                    s[3] = poly_level[2]->poly_0->stat_l[l3];

                                    // p011.
                                    for (size_t l4 = 0; l4 < l_size[4]; ++l4) {
                                        s[4] = poly_level[1]->poly_1->stat_l[l4];

                                        // p0110 - p0100 - p0010 + p0000
                                        p[3] = s[4]->poly_0->coef_bk;
                                        p[2] = s[2]->poly_0->coef_bk;
                                        p[1] = s[1]->poly_0->coef_bk;
                                        p[0] = s[0]->poly_0->coef_bk;
                                        for (int i = 0; i < n + 1; ++i) {
                                            p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                        }
                                        std::reverse(p[3].begin(), p[3].end());
                                        if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                            ++H;
                                            continue;
                                        }

                                        // p101.
                                        for (size_t l5 = 0; l5 < l_size[5]; ++l5) {
                                            s[5] = poly_level[2]->poly_1->stat_l[l5];

                                            // p1010 - p1000 - p0010 + p0000
                                            p[3] = s[5]->poly_0->coef_bk;
                                            p[2] = s[3]->poly_0->coef_bk;
                                            p[1] = s[1]->poly_0->coef_bk;
                                            p[0] = s[0]->poly_0->coef_bk;
                                            for (int i = 0; i < n + 1; ++i) {
                                                p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                            }
                                            std::reverse(p[3].begin(), p[3].end());
                                            if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                                ++J;
                                                continue;
                                            }

                                            // p1000 - p0000
                                            p[1] = s[3]->poly_0->coef_bk;
                                            p[0] = s[0]->poly_0->coef_bk;
                                            for (int i = 0; i < n + 1; ++i) {
                                                p[1][i] -= p[0][i];
                                            }
                                            std::reverse(p[1].begin(), p[1].end());
                                            if (!dividePolynomialByPolynomial(p[1], bin_exp[1])) {
                                                ++F;
                                                continue;
                                            }

                                            // p110.
                                            for (size_t l6 = 0; l6 < l_size[6]; ++l6) {
                                                s[6] = poly_level[3]->poly_0->stat_l[l6];

                                                // p1100 - p1000 - p0100 + p0000
                                                p[3] = s[6]->poly_0->coef_bk;
                                                p[2] = s[3]->poly_0->coef_bk;
                                                p[1] = s[2]->poly_0->coef_bk;
                                                p[0] = s[0]->poly_0->coef_bk;
                                                for (int i = 0; i < n + 1; ++i) {
                                                    p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                                }
                                                std::reverse(p[3].begin(), p[3].end());
                                                if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                                    ++L;
                                                    continue;
                                                }

                                                // p0100 - p0000
                                                p[1] = s[2]->poly_0->coef_bk;
                                                p[0] = s[0]->poly_0->coef_bk;
                                                for (size_t i = 0; i < p[1].size(); ++i) {
                                                    p[1][i] -= p[0][i];
                                                }
                                                std::reverse(p[1].begin(), p[1].end());
                                                if (!dividePolynomialByPolynomial(p[1], bin_exp[1])) {
                                                    ++D;
                                                    continue;
                                                }

                                                // p0010 - p0000
                                                p[1] = s[1]->poly_0->coef_bk;
                                                p[0] = s[0]->poly_0->coef_bk;
                                                for (int i = 0; i < n + 1; ++i) {
                                                    p[1][i] -= p[0][i];
                                                }
                                                std::reverse(p[1].begin(), p[1].end());
                                                if (!dividePolynomialByPolynomial(p[1], bin_exp[1])) {
                                                    ++B;
                                                    continue;
                                                }

                                                // p111.
                                                for (size_t l7 = 0; l7 < l_size[7]; ++l7) {
                                                    s[7] = poly_level[3]->poly_1->stat_l[l7];

                                                    // p1110 - p1100 - p1010 - p0110 + p1000 + p0100 + p0010 - p0000
                                                    p[7] = s[7]->poly_0->coef_bk;
                                                    p[6] = s[6]->poly_0->coef_bk;
                                                    p[5] = s[5]->poly_0->coef_bk;
                                                    p[4] = s[4]->poly_0->coef_bk;
                                                    p[3] = s[3]->poly_0->coef_bk;
                                                    p[2] = s[2]->poly_0->coef_bk;
                                                    p[1] = s[1]->poly_0->coef_bk;
                                                    p[0] = s[0]->poly_0->coef_bk;
                                                    for (int i = 0; i < n + 1; ++i) {
                                                        p[7][i] = p[7][i] - p[6][i] - p[5][i] - p[4][i] + p[3][i] + p[2][i] + p[1][i] - p[0][i];
                                                    }
                                                    std::reverse(p[7].begin(), p[7].end());
                                                    if (!dividePolynomialByPolynomial(p[7], bin_exp[3])) {
                                                        ++N;
                                                        continue;
                                                    }

                                                    // p0111 - p0110 - p0101 - p0011 + p0100 + p0010 + p0001 - p0000
                                                    p[7] = s[4]->poly_1->coef_bk;
                                                    p[6] = s[4]->poly_0->coef_bk;
                                                    p[5] = s[2]->poly_1->coef_bk;
                                                    p[4] = s[1]->poly_1->coef_bk;
                                                    p[3] = s[2]->poly_0->coef_bk;
                                                    p[2] = s[1]->poly_0->coef_bk;
                                                    p[1] = s[0]->poly_1->coef_bk;
                                                    p[0] = s[0]->poly_0->coef_bk;
                                                    for (int i = 0; i < n + 1; ++i) {
                                                        p[7][i] = p[7][i] - p[6][i] - p[5][i] - p[4][i] + p[3][i] + p[2][i] + p[1][i] - p[0][i];
                                                    }
                                                    std::reverse(p[7].begin(), p[7].end());
                                                    if (!dividePolynomialByPolynomial(p[7], bin_exp[3])) {
                                                        ++I;
                                                        continue;
                                                    }

                                                    // p1011 - p1010 - p1001 - p0011 + p1000 + p0010 + p0001 - p0000
                                                    p[7] = s[5]->poly_1->coef_bk;
                                                    p[6] = s[5]->poly_0->coef_bk;
                                                    p[5] = s[3]->poly_1->coef_bk;
                                                    p[4] = s[1]->poly_1->coef_bk;
                                                    p[3] = s[3]->poly_0->coef_bk;
                                                    p[2] = s[1]->poly_0->coef_bk;
                                                    p[1] = s[0]->poly_1->coef_bk;
                                                    p[0] = s[0]->poly_0->coef_bk;
                                                    for (int i = 0; i < n + 1; ++i) {
                                                        p[7][i] = p[7][i] - p[6][i] - p[5][i] - p[4][i] + p[3][i] + p[2][i] + p[1][i] - p[0][i];
                                                    }
                                                    std::reverse(p[7].begin(), p[7].end());
                                                    if (!dividePolynomialByPolynomial(p[7], bin_exp[3])) {
                                                        ++K;
                                                        continue;
                                                    }

                                                    // p1101 - p1100 - p1001 - p0101 + p1000 + p0100 + p0001 - p0000
                                                    p[7] = s[6]->poly_1->coef_bk;
                                                    p[6] = s[6]->poly_0->coef_bk;
                                                    p[5] = s[3]->poly_1->coef_bk;
                                                    p[4] = s[2]->poly_1->coef_bk;
                                                    p[3] = s[3]->poly_0->coef_bk;
                                                    p[2] = s[2]->poly_0->coef_bk;
                                                    p[1] = s[0]->poly_1->coef_bk;
                                                    p[0] = s[0]->poly_0->coef_bk;
                                                    for (int i = 0; i < n + 1; ++i) {
                                                        p[7][i] = p[7][i] - p[6][i] - p[5][i] - p[4][i] + p[3][i] + p[2][i] + p[1][i] - p[0][i];
                                                    }
                                                    std::reverse(p[7].begin(), p[7].end());
                                                    if (!dividePolynomialByPolynomial(p[7], bin_exp[3])) {
                                                        ++M;
                                                        continue;
                                                    }

                                                    // p1001 - p1000 - p0001 + p0000
                                                    p[3] = s[3]->poly_1->coef_bk;
                                                    p[2] = s[3]->poly_0->coef_bk;
                                                    p[1] = s[0]->poly_1->coef_bk;
                                                    p[0] = s[0]->poly_0->coef_bk;
                                                    for (int i = 0; i < n + 1; ++i) {
                                                        p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                                    }
                                                    std::reverse(p[3].begin(), p[3].end());
                                                    if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                                        ++G;
                                                        continue;
                                                    }

                                                    // p0011 - p0010 - p0001 + p0000
                                                    p[3] = s[1]->poly_1->coef_bk;
                                                    p[2] = s[1]->poly_0->coef_bk;
                                                    p[1] = s[0]->poly_1->coef_bk;
                                                    p[0] = s[0]->poly_0->coef_bk;
                                                    for (int i = 0; i < n + 1; ++i) {
                                                        p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                                    }
                                                    std::reverse(p[3].begin(), p[3].end());
                                                    if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                                        ++C;
                                                        continue;
                                                    }

                                                    // p0101 - p0100 - p0001 + p0000
                                                    p[3] = s[2]->poly_1->coef_bk;
                                                    p[2] = s[2]->poly_0->coef_bk;
                                                    p[1] = s[0]->poly_1->coef_bk;
                                                    p[0] = s[0]->poly_0->coef_bk;
                                                    for (int i = 0; i < n + 1; ++i) {
                                                        p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                                    }
                                                    std::reverse(p[3].begin(), p[3].end());
                                                    if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                                        ++E;
                                                        continue;
                                                    }

                                                    // p0001 - p0000
                                                    p[1] = s[0]->poly_1->coef_bk;
                                                    p[0] = s[0]->poly_0->coef_bk;
                                                    for (int i = 0; i < n + 1; ++i) {
                                                        p[1][i] -= p[0][i];
                                                    }
                                                    std::reverse(p[1].begin(), p[1].end());
                                                    if (!dividePolynomialByPolynomial(p[1], bin_exp[1])) {
                                                        ++A;
                                                        continue;
                                                    }

                                                    /*
                                                    p1111
                                                    - p1110 - p1101 - p1011 - p0111
                                                    + p1100 + p1010 + p1001 + p0110 + p0101 + p0011
                                                    - p1000 - p0100 - p0010 - p0001
                                                    + p0000
                                                    */
                                                    p[15] = s[7]->poly_1->coef_bk;
                                                    p[14] = s[7]->poly_0->coef_bk;
                                                    p[13] = s[6]->poly_1->coef_bk;
                                                    p[12] = s[5]->poly_1->coef_bk;
                                                    p[11] = s[4]->poly_1->coef_bk;
                                                    p[10] = s[6]->poly_0->coef_bk;
                                                    p[9] = s[5]->poly_0->coef_bk;
                                                    p[8] = s[3]->poly_1->coef_bk;
                                                    p[7] = s[4]->poly_0->coef_bk;
                                                    p[6] = s[2]->poly_1->coef_bk;
                                                    p[5] = s[1]->poly_1->coef_bk;
                                                    p[4] = s[3]->poly_0->coef_bk;
                                                    p[3] = s[2]->poly_0->coef_bk;
                                                    p[2] = s[1]->poly_0->coef_bk;
                                                    p[1] = s[0]->poly_1->coef_bk;
                                                    p[0] = s[0]->poly_0->coef_bk;
                                                    for (int i = 0; i < n + 1; ++i) {
                                                        p[15][i] = p[15][i]
                                                            - p[14][i] - p[13][i] - p[12][i] - p[11][i]
                                                            + p[10][i] + p[9][i] + p[8][i] + p[7][i] + p[6][i] + p[5][i]
                                                            - p[4][i] - p[3][i] - p[2][i] - p[1][i]
                                                            + p[0][i];
                                                    }
                                                    std::reverse(p[15].begin(), p[15].end());
                                                    if (!dividePolynomialByPolynomial(p[15], bin_exp[4])) {
                                                        ++O;
                                                        continue;
                                                    }

                                                    s[7]->status = true;
                                                    s[6]->status = true;
                                                    s[5]->status = true;
                                                    s[4]->status = true;
                                                    s[3]->status = true;
                                                    s[2]->status = true;
                                                    s[1]->status = true;
                                                    s[0]->status = true;

                                                    new_full_bk_level.push_back({ s[0], s[1], s[2], s[4], s[3], s[5], s[6], s[7] });
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                else if (lim == 5) {
                    p.resize(32);
                    s.resize(16);
                    l_size.resize(16);

                    l_size[0] = poly_level[0]->poly_0->stat_l.size();
                    l_size[1] = poly_level[0]->poly_1->stat_l.size();
                    l_size[2] = poly_level[1]->poly_0->stat_l.size();
                    l_size[3] = poly_level[2]->poly_0->stat_l.size();
                    l_size[4] = poly_level[4]->poly_0->stat_l.size();
                    l_size[5] = poly_level[1]->poly_1->stat_l.size();
                    l_size[6] = poly_level[2]->poly_1->stat_l.size();
                    l_size[7] = poly_level[3]->poly_0->stat_l.size();
                    l_size[8] = poly_level[4]->poly_1->stat_l.size();
                    l_size[9] = poly_level[5]->poly_0->stat_l.size();
                    l_size[10] = poly_level[6]->poly_0->stat_l.size();
                    l_size[11] = poly_level[3]->poly_1->stat_l.size();
                    l_size[12] = poly_level[5]->poly_1->stat_l.size();
                    l_size[13] = poly_level[6]->poly_1->stat_l.size();
                    l_size[14] = poly_level[7]->poly_0->stat_l.size();
                    l_size[15] = poly_level[7]->poly_1->stat_l.size();

                    // pārbauda 5. līmeni
                    // p0000.
                    for (size_t l0 = 0; l0 < l_size[0]; ++l0) {
                        s[0] = poly_level[0]->poly_0->stat_l[l0];

                        // p00001 - p00000
                        p[1] = s[0]->poly_1->coef_bk;
                        p[0] = s[0]->poly_0->coef_bk;
                        for (int i = 0; i < n + 1; ++i) {
                            p[1][i] -= p[0][i];
                        }
                        std::reverse(p[1].begin(), p[1].end());
                        if (!dividePolynomialByPolynomial(p[1], bin_exp[1])) {
                            ++A;
                            continue;
                        }

                        // p0001.
                        for (size_t l1 = 0; l1 < l_size[1]; ++l1) {
                            s[1] = poly_level[0]->poly_1->stat_l[l1];

                            // p00010 - p00000
                            p[1] = s[1]->poly_0->coef_bk;
                            p[0] = s[0]->poly_0->coef_bk;
                            for (int i = 0; i < n + 1; ++i) {
                                p[1][i] -= p[0][i];
                            }
                            std::reverse(p[1].begin(), p[1].end());
                            if (!dividePolynomialByPolynomial(p[1], bin_exp[1])) {
                                ++B;
                                continue;
                            }

                            // p00011 - p00010 - p00001 + p00000
                            p[3] = s[1]->poly_1->coef_bk;
                            p[2] = s[1]->poly_0->coef_bk;
                            p[1] = s[0]->poly_1->coef_bk;
                            p[0] = s[0]->poly_0->coef_bk;
                            for (int i = 0; i < n + 1; ++i) {
                                p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                            }
                            std::reverse(p[3].begin(), p[3].end());
                            if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                ++C;
                                continue;
                            }

                            // p0010.
                            for (size_t l2 = 0; l2 < l_size[2]; ++l2) {
                                s[2] = poly_level[1]->poly_0->stat_l[l2];

                                // p00100 - p00000
                                p[1] = s[2]->poly_0->coef_bk;
                                p[0] = s[0]->poly_0->coef_bk;
                                for (int i = 0; i < n + 1; ++i) {
                                    p[1][i] -= p[0][i];
                                }
                                std::reverse(p[1].begin(), p[1].end());
                                if (!dividePolynomialByPolynomial(p[1], bin_exp[1])) {
                                    ++D;
                                    continue;
                                }

                                // p00101 - p00100 - p00001 + p00000
                                p[3] = s[2]->poly_1->coef_bk;
                                p[2] = s[2]->poly_0->coef_bk;
                                p[1] = s[0]->poly_1->coef_bk;
                                p[0] = s[0]->poly_0->coef_bk;
                                for (int i = 0; i < n + 1; ++i) {
                                    p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                }
                                std::reverse(p[3].begin(), p[3].end());
                                if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                    ++E;
                                    continue;
                                }

                                // p0100.
                                for (size_t l3 = 0; l3 < l_size[3]; ++l3) {
                                    s[3] = poly_level[2]->poly_0->stat_l[l3];

                                    // p01000 - p00000
                                    p[1] = s[3]->poly_0->coef_bk;
                                    p[0] = s[0]->poly_0->coef_bk;
                                    for (int i = 0; i < n + 1; ++i) {
                                        p[1][i] -= p[0][i];
                                    }
                                    std::reverse(p[1].begin(), p[1].end());
                                    if (!dividePolynomialByPolynomial(p[1], bin_exp[1])) {
                                        ++F;
                                        continue;
                                    }

                                    // p01001 - p01000 - p00001 + p00000
                                    p[3] = s[3]->poly_1->coef_bk;
                                    p[2] = s[3]->poly_0->coef_bk;
                                    p[1] = s[0]->poly_1->coef_bk;
                                    p[0] = s[0]->poly_0->coef_bk;
                                    for (int i = 0; i < n + 1; ++i) {
                                        p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                    }
                                    std::reverse(p[3].begin(), p[3].end());
                                    if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                        ++G;
                                        continue;
                                    }

                                    // p1000.
                                    for (size_t l4 = 0; l4 < l_size[4]; ++l4) {
                                        s[4] = poly_level[4]->poly_0->stat_l[l4];

                                        // p10000 - p00000
                                        p[1] = s[4]->poly_0->coef_bk;
                                        p[0] = s[0]->poly_0->coef_bk;
                                        for (int i = 0; i < n + 1; ++i) {
                                            p[1][i] -= p[0][i];
                                        }
                                        std::reverse(p[1].begin(), p[1].end());
                                        if (!dividePolynomialByPolynomial(p[1], bin_exp[1])) {
                                            ++H;
                                            continue;
                                        }

                                        // p10001 - p10000 - p00001 + p00000
                                        p[3] = s[4]->poly_1->coef_bk;
                                        p[2] = s[4]->poly_0->coef_bk;
                                        p[1] = s[0]->poly_1->coef_bk;
                                        p[0] = s[0]->poly_0->coef_bk;
                                        for (int i = 0; i < n + 1; ++i) {
                                            p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                        }
                                        std::reverse(p[3].begin(), p[3].end());
                                        if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                            ++I;
                                            continue;
                                        }

                                        // p0011.
                                        for (size_t l5 = 0; l5 < l_size[5]; ++l5) {
                                            s[5] = poly_level[1]->poly_1->stat_l[l5];

                                            // p00110 - p00100 - p00010 + p00000
                                            p[3] = s[5]->poly_0->coef_bk;
                                            p[2] = s[2]->poly_0->coef_bk;
                                            p[1] = s[1]->poly_1->coef_bk;
                                            p[0] = s[0]->poly_0->coef_bk;
                                            for (int i = 0; i < n + 1; ++i) {
                                                p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                            }
                                            std::reverse(p[3].begin(), p[3].end());
                                            if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                                ++J;
                                                continue;
                                            }

                                            // p00111 - p00110 - p00101 - p00011 + p00100 + p00010 + p00001 - p00000
                                            p[7] = s[5]->poly_1->coef_bk;
                                            p[6] = s[5]->poly_0->coef_bk;
                                            p[5] = s[2]->poly_1->coef_bk;
                                            p[4] = s[1]->poly_1->coef_bk;
                                            p[3] = s[2]->poly_0->coef_bk;
                                            p[2] = s[1]->poly_0->coef_bk;
                                            p[1] = s[0]->poly_1->coef_bk;
                                            p[0] = s[0]->poly_0->coef_bk;
                                            for (int i = 0; i < n + 1; ++i) {
                                                p[7][i] = p[7][i] - p[6][i] - p[5][i] - p[4][i] + p[3][i] + p[2][i] + p[1][i] - p[0][i];
                                            }
                                            std::reverse(p[7].begin(), p[7].end());
                                            if (!dividePolynomialByPolynomial(p[7], bin_exp[3])) {
                                                ++K;
                                                continue;
                                            }

                                            // p0101.
                                            for (size_t l6 = 0; l6 < l_size[6]; ++l6) {
                                                s[6] = poly_level[2]->poly_1->stat_l[l6];

                                                // p01010 - p01000 - p00010 + p00000
                                                p[3] = s[6]->poly_0->coef_bk;
                                                p[2] = s[3]->poly_0->coef_bk;
                                                p[1] = s[1]->poly_1->coef_bk;
                                                p[0] = s[0]->poly_0->coef_bk;
                                                for (int i = 0; i < n + 1; ++i) {
                                                    p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                                }
                                                std::reverse(p[3].begin(), p[3].end());
                                                if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                                    ++L;
                                                    continue;
                                                }

                                                // p01011 - p01010 - p01001 - p00011 + p01000 + p00010 + p00001 - p00000
                                                p[7] = s[6]->poly_1->coef_bk;
                                                p[6] = s[6]->poly_0->coef_bk;
                                                p[5] = s[3]->poly_1->coef_bk;
                                                p[4] = s[1]->poly_1->coef_bk;
                                                p[3] = s[3]->poly_0->coef_bk;
                                                p[2] = s[1]->poly_0->coef_bk;
                                                p[1] = s[0]->poly_1->coef_bk;
                                                p[0] = s[0]->poly_0->coef_bk;
                                                for (int i = 0; i < n + 1; ++i) {
                                                    p[7][i] = p[7][i] - p[6][i] - p[5][i] - p[4][i] + p[3][i] + p[2][i] + p[1][i] - p[0][i];
                                                }
                                                std::reverse(p[7].begin(), p[7].end());
                                                if (!dividePolynomialByPolynomial(p[7], bin_exp[3])) {
                                                    ++M;
                                                    continue;
                                                }

                                                // p0110.
                                                for (size_t l7 = 0; l7 < l_size[7]; ++l7) {
                                                    s[7] = poly_level[3]->poly_0->stat_l[l7];

                                                    // p01100 - p01000 - p00100 + p00000
                                                    p[3] = s[7]->poly_0->coef_bk;
                                                    p[2] = s[3]->poly_0->coef_bk;
                                                    p[1] = s[2]->poly_1->coef_bk;
                                                    p[0] = s[0]->poly_0->coef_bk;
                                                    for (int i = 0; i < n + 1; ++i) {
                                                        p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                                    }
                                                    std::reverse(p[3].begin(), p[3].end());
                                                    if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                                        ++N;
                                                        continue;
                                                    }

                                                    // p01101 - p01100 - p01001 - p00101 + p01000 + p00100 + p00001 - p00000
                                                    p[7] = s[7]->poly_1->coef_bk;
                                                    p[6] = s[7]->poly_0->coef_bk;
                                                    p[5] = s[3]->poly_1->coef_bk;
                                                    p[4] = s[2]->poly_1->coef_bk;
                                                    p[3] = s[3]->poly_0->coef_bk;
                                                    p[2] = s[2]->poly_0->coef_bk;
                                                    p[1] = s[0]->poly_1->coef_bk;
                                                    p[0] = s[0]->poly_0->coef_bk;
                                                    for (int i = 0; i < n + 1; ++i) {
                                                        p[7][i] = p[7][i] - p[6][i] - p[5][i] - p[4][i] + p[3][i] + p[2][i] + p[1][i] - p[0][i];
                                                    }
                                                    std::reverse(p[7].begin(), p[7].end());
                                                    if (!dividePolynomialByPolynomial(p[7], bin_exp[3])) {
                                                        ++N;
                                                        continue;
                                                    }

                                                    // p1001.
                                                    for (size_t l8 = 0; l8 < l_size[8]; ++l8) {
                                                        s[8] = poly_level[4]->poly_1->stat_l[l8];

                                                        // p10010 - p10000 - p00010 + p00000
                                                        p[3] = s[8]->poly_0->coef_bk;
                                                        p[2] = s[4]->poly_0->coef_bk;
                                                        p[1] = s[1]->poly_1->coef_bk;
                                                        p[0] = s[0]->poly_0->coef_bk;
                                                        for (int i = 0; i < n + 1; ++i) {
                                                            p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                                        }
                                                        std::reverse(p[3].begin(), p[3].end());
                                                        if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                                            ++O;
                                                            continue;
                                                        }

                                                        // p10011 - p10010 - p10001 - p00011 + p10000 + p00010 + p00001 - p00000
                                                        p[7] = s[8]->poly_1->coef_bk;
                                                        p[6] = s[8]->poly_0->coef_bk;
                                                        p[5] = s[4]->poly_1->coef_bk;
                                                        p[4] = s[1]->poly_1->coef_bk;
                                                        p[3] = s[4]->poly_0->coef_bk;
                                                        p[2] = s[1]->poly_0->coef_bk;
                                                        p[1] = s[0]->poly_1->coef_bk;
                                                        p[0] = s[0]->poly_0->coef_bk;
                                                        for (int i = 0; i < n + 1; ++i) {
                                                            p[7][i] = p[7][i] - p[6][i] - p[5][i] - p[4][i] + p[3][i] + p[2][i] + p[1][i] - p[0][i];
                                                        }
                                                        std::reverse(p[7].begin(), p[7].end());
                                                        if (!dividePolynomialByPolynomial(p[7], bin_exp[3])) {
                                                            ++P;
                                                            continue;
                                                        }

                                                        // p1010.
                                                        for (size_t l9 = 0; l9 < l_size[9]; ++l9) {
                                                            s[9] = poly_level[5]->poly_0->stat_l[l9];

                                                            // p10100 - p10000 - p00100 + p00000
                                                            p[3] = s[9]->poly_0->coef_bk;
                                                            p[2] = s[4]->poly_0->coef_bk;
                                                            p[1] = s[2]->poly_1->coef_bk;
                                                            p[0] = s[0]->poly_0->coef_bk;
                                                            for (int i = 0; i < n + 1; ++i) {
                                                                p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                                            }
                                                            std::reverse(p[3].begin(), p[3].end());
                                                            if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                                                ++Q;
                                                                continue;
                                                            }

                                                            // p10101 - p10100 - p10001 - p00101 + p10000 + p00100 + p00001 - p00000
                                                            p[7] = s[9]->poly_1->coef_bk;
                                                            p[6] = s[9]->poly_0->coef_bk;
                                                            p[5] = s[4]->poly_1->coef_bk;
                                                            p[4] = s[2]->poly_1->coef_bk;
                                                            p[3] = s[4]->poly_0->coef_bk;
                                                            p[2] = s[2]->poly_0->coef_bk;
                                                            p[1] = s[0]->poly_1->coef_bk;
                                                            p[0] = s[0]->poly_0->coef_bk;
                                                            for (int i = 0; i < n + 1; ++i) {
                                                                p[7][i] = p[7][i] - p[6][i] - p[5][i] - p[4][i] + p[3][i] + p[2][i] + p[1][i] - p[0][i];
                                                            }
                                                            std::reverse(p[7].begin(), p[7].end());
                                                            if (!dividePolynomialByPolynomial(p[7], bin_exp[3])) {
                                                                ++R;
                                                                continue;
                                                            }

                                                            // p1100.
                                                            for (size_t l10 = 0; l10 < l_size[10]; ++l10) {
                                                                s[10] = poly_level[6]->poly_0->stat_l[l10];

                                                                // p11000 - p10000 - p01000 + p00000
                                                                p[3] = s[10]->poly_0->coef_bk;
                                                                p[2] = s[4]->poly_0->coef_bk;
                                                                p[1] = s[3]->poly_1->coef_bk;
                                                                p[0] = s[0]->poly_0->coef_bk;
                                                                for (int i = 0; i < n + 1; ++i) {
                                                                    p[3][i] = p[3][i] - p[2][i] - p[1][i] + p[0][i];
                                                                }
                                                                std::reverse(p[3].begin(), p[3].end());
                                                                if (!dividePolynomialByPolynomial(p[3], bin_exp[2])) {
                                                                    ++S;
                                                                    continue;
                                                                }

                                                                // p11001 - p11000 - p10001 - p01001 + p10000 + p01000 + p00001 - p00000
                                                                p[7] = s[10]->poly_1->coef_bk;
                                                                p[6] = s[10]->poly_0->coef_bk;
                                                                p[5] = s[4]->poly_1->coef_bk;
                                                                p[4] = s[3]->poly_1->coef_bk;
                                                                p[3] = s[4]->poly_0->coef_bk;
                                                                p[2] = s[3]->poly_0->coef_bk;
                                                                p[1] = s[0]->poly_1->coef_bk;
                                                                p[0] = s[0]->poly_0->coef_bk;
                                                                for (int i = 0; i < n + 1; ++i) {
                                                                    p[7][i] = p[7][i] - p[6][i] - p[5][i] - p[4][i] + p[3][i] + p[2][i] + p[1][i] - p[0][i];
                                                                }

                                                                std::reverse(p[7].begin(), p[7].end());
                                                                if (!dividePolynomialByPolynomial(p[7], bin_exp[3])) {
                                                                    ++T;
                                                                    continue;
                                                                }

                                                                // p0111.
                                                                for (size_t l11 = 0; l11 < l_size[11]; ++l11) {
                                                                    s[11] = poly_level[3]->poly_1->stat_l[l11];

                                                                    // p01110 - p01100 - p01010 - p00110 + p01000 + p00100 + p00010 - p00000
                                                                    p[7] = s[11]->poly_0->coef_bk;
                                                                    p[6] = s[7]->poly_0->coef_bk;
                                                                    p[5] = s[6]->poly_0->coef_bk;
                                                                    p[4] = s[5]->poly_0->coef_bk;
                                                                    p[3] = s[3]->poly_0->coef_bk;
                                                                    p[2] = s[2]->poly_0->coef_bk;
                                                                    p[1] = s[1]->poly_0->coef_bk;
                                                                    p[0] = s[0]->poly_0->coef_bk;
                                                                    for (int i = 0; i < n + 1; ++i) {
                                                                        p[7][i] = p[7][i] - p[6][i] - p[5][i] - p[4][i] + p[3][i] + p[2][i] + p[1][i] - p[0][i];
                                                                    }
                                                                    std::reverse(p[7].begin(), p[7].end());
                                                                    if (!dividePolynomialByPolynomial(p[7], bin_exp[3])) {
                                                                        ++U;
                                                                        continue;
                                                                    }

                                                                    /*
                                                                    p01111
                                                                    - p01110 - p01101 - p01011 - p00111
                                                                    + p01100 + p01010 + p01001 + p00110 + p00101 + p00011
                                                                    - p01000 - p00100 - p00010 - p00001
                                                                    + p00000
                                                                    */
                                                                    p[15] = s[11]->poly_1->coef_bk;
                                                                    p[14] = s[11]->poly_0->coef_bk;
                                                                    p[13] = s[7]->poly_1->coef_bk;
                                                                    p[12] = s[6]->poly_1->coef_bk;
                                                                    p[11] = s[5]->poly_1->coef_bk;
                                                                    p[10] = s[7]->poly_0->coef_bk;
                                                                    p[9] = s[6]->poly_0->coef_bk;
                                                                    p[8] = s[3]->poly_1->coef_bk;
                                                                    p[7] = s[5]->poly_0->coef_bk;
                                                                    p[6] = s[2]->poly_1->coef_bk;
                                                                    p[5] = s[1]->poly_1->coef_bk;
                                                                    p[4] = s[3]->poly_0->coef_bk;
                                                                    p[3] = s[2]->poly_0->coef_bk;
                                                                    p[2] = s[1]->poly_0->coef_bk;
                                                                    p[1] = s[0]->poly_1->coef_bk;
                                                                    p[0] = s[0]->poly_0->coef_bk;

                                                                    for (int i = 0; i < n + 1; ++i) {
                                                                        p[15][i] = p[15][i]
                                                                            - p[14][i] - p[13][i] - p[12][i] - p[11][i]
                                                                            + p[10][i] + p[9][i] + p[8][i] + p[7][i] + p[6][i] + p[5][i]
                                                                            - p[4][i] - p[3][i] - p[2][i] - p[1][i]
                                                                            + p[0][i];
                                                                    }
                                                                    std::reverse(p[15].begin(), p[15].end());
                                                                    if (!dividePolynomialByPolynomial(p[15], bin_exp[4])) {
                                                                        ++V;
                                                                        continue;
                                                                    }

                                                                    // p1011.
                                                                    for (size_t l12 = 0; l12 < l_size[12]; ++l12) {
                                                                        s[12] = poly_level[5]->poly_1->stat_l[l12];

                                                                        // p10110 - p10100 - p10010 - p00110 + p10000 + p00100 + p00010 - p00000
                                                                        p[7] = s[12]->poly_0->coef_bk;
                                                                        p[6] = s[9]->poly_0->coef_bk;
                                                                        p[5] = s[8]->poly_0->coef_bk;
                                                                        p[4] = s[5]->poly_0->coef_bk;
                                                                        p[3] = s[4]->poly_0->coef_bk;
                                                                        p[2] = s[2]->poly_0->coef_bk;
                                                                        p[1] = s[1]->poly_0->coef_bk;
                                                                        p[0] = s[0]->poly_0->coef_bk;
                                                                        for (int i = 0; i < n + 1; ++i) {
                                                                            p[7][i] = p[7][i] - p[6][i] - p[5][i] - p[4][i] + p[3][i] + p[2][i] + p[1][i] - p[0][i];
                                                                        }
                                                                        std::reverse(p[7].begin(), p[7].end());
                                                                        if (!dividePolynomialByPolynomial(p[7], bin_exp[3])) {
                                                                            ++W;
                                                                            continue;
                                                                        }

                                                                        /*
                                                                        p10111
                                                                        - p10110 - p10101 - p10011 - p00111
                                                                        + p10100 + p10010 + p10001 + p00110 + p00101 + p00011
                                                                        - p10000 - p00100 - p00010 - p00001
                                                                        + p00000
                                                                        */
                                                                        p[15] = s[12]->poly_1->coef_bk;
                                                                        p[14] = s[12]->poly_0->coef_bk;
                                                                        p[13] = s[9]->poly_1->coef_bk;
                                                                        p[12] = s[8]->poly_1->coef_bk;
                                                                        p[11] = s[5]->poly_1->coef_bk;
                                                                        p[10] = s[9]->poly_0->coef_bk;
                                                                        p[9] = s[8]->poly_0->coef_bk;
                                                                        p[8] = s[4]->poly_1->coef_bk;
                                                                        p[7] = s[5]->poly_0->coef_bk;
                                                                        p[6] = s[2]->poly_1->coef_bk;
                                                                        p[5] = s[1]->poly_1->coef_bk;
                                                                        p[4] = s[4]->poly_0->coef_bk;
                                                                        p[3] = s[2]->poly_0->coef_bk;
                                                                        p[2] = s[1]->poly_0->coef_bk;
                                                                        p[1] = s[0]->poly_1->coef_bk;
                                                                        p[0] = s[0]->poly_0->coef_bk;
                                                                        for (int i = 0; i < n + 1; ++i) {
                                                                            p[15][i] = p[15][i]
                                                                                - p[14][i] - p[13][i] - p[12][i] - p[11][i]
                                                                                + p[10][i] + p[9][i] + p[8][i] + p[7][i] + p[6][i] + p[5][i]
                                                                                - p[4][i] - p[3][i] - p[2][i] - p[1][i]
                                                                                + p[0][i];
                                                                        }
                                                                        std::reverse(p[15].begin(), p[15].end());
                                                                        if (!dividePolynomialByPolynomial(p[15], bin_exp[4])) {
                                                                            ++X;
                                                                            continue;
                                                                        }

                                                                        // p1101.
                                                                        for (size_t l13 = 0; l13 < l_size[13]; ++l13) {
                                                                            s[13] = poly_level[6]->poly_1->stat_l[l13];

                                                                            // p11010 - p10100 - p10010 - p01010 + p10000 + p01000 + p00010 - p00000
                                                                            p[7] = s[13]->poly_0->coef_bk;
                                                                            p[6] = s[9]->poly_0->coef_bk;
                                                                            p[5] = s[8]->poly_0->coef_bk;
                                                                            p[4] = s[6]->poly_0->coef_bk;
                                                                            p[3] = s[4]->poly_0->coef_bk;
                                                                            p[2] = s[3]->poly_0->coef_bk;
                                                                            p[1] = s[1]->poly_0->coef_bk;
                                                                            p[0] = s[0]->poly_0->coef_bk;
                                                                            for (int i = 0; i < n + 1; ++i) {
                                                                                p[7][i] = p[7][i] - p[6][i] - p[5][i] - p[4][i] + p[3][i] + p[2][i] + p[1][i] - p[0][i];
                                                                            }
                                                                            std::reverse(p[7].begin(), p[7].end());
                                                                            if (!dividePolynomialByPolynomial(p[7], bin_exp[3])) {
                                                                                ++Y;
                                                                                continue;
                                                                            }

                                                                            /*
                                                                            p11011
                                                                            - p11010 - p11001 - p10011 - p01011
                                                                            + p11000 + p10010 + p10001 + p01010 + p01001 + p00011
                                                                            - p10000 - p01000 - p00010 - p00001
                                                                            + p00000
                                                                            */
                                                                            p[15] = s[13]->poly_1->coef_bk;
                                                                            p[14] = s[13]->poly_0->coef_bk;
                                                                            p[13] = s[10]->poly_1->coef_bk;
                                                                            p[12] = s[8]->poly_1->coef_bk;
                                                                            p[11] = s[6]->poly_1->coef_bk;
                                                                            p[10] = s[10]->poly_0->coef_bk;
                                                                            p[9] = s[8]->poly_0->coef_bk;
                                                                            p[8] = s[4]->poly_1->coef_bk;
                                                                            p[7] = s[6]->poly_0->coef_bk;
                                                                            p[6] = s[3]->poly_1->coef_bk;
                                                                            p[5] = s[1]->poly_1->coef_bk;
                                                                            p[4] = s[4]->poly_0->coef_bk;
                                                                            p[3] = s[3]->poly_0->coef_bk;
                                                                            p[2] = s[1]->poly_0->coef_bk;
                                                                            p[1] = s[0]->poly_1->coef_bk;
                                                                            p[0] = s[0]->poly_0->coef_bk;
                                                                            for (int i = 0; i < n + 1; ++i) {
                                                                                p[15][i] = p[15][i]
                                                                                    - p[14][i] - p[13][i] - p[12][i] - p[11][i]
                                                                                    + p[10][i] + p[9][i] + p[8][i] + p[7][i] + p[6][i] + p[5][i]
                                                                                    - p[4][i] - p[3][i] - p[2][i] - p[1][i]
                                                                                    + p[0][i];
                                                                            }
                                                                            std::reverse(p[15].begin(), p[15].end());
                                                                            if (!dividePolynomialByPolynomial(p[15], bin_exp[4])) {
                                                                                ++Z;
                                                                                continue;
                                                                            }

                                                                            // p1110.
                                                                            for (size_t l14 = 0; l14 < l_size[14]; ++l14) {
                                                                                s[14] = poly_level[7]->poly_0->stat_l[l14];

                                                                                // p11100 - p11000 - p10100 - p01100 + p10000 + p01000 + p00100 - p00000
                                                                                p[7] = s[14]->poly_0->coef_bk;
                                                                                p[6] = s[10]->poly_0->coef_bk;
                                                                                p[5] = s[9]->poly_0->coef_bk;
                                                                                p[4] = s[7]->poly_0->coef_bk;
                                                                                p[3] = s[4]->poly_0->coef_bk;
                                                                                p[2] = s[3]->poly_0->coef_bk;
                                                                                p[1] = s[2]->poly_0->coef_bk;
                                                                                p[0] = s[0]->poly_0->coef_bk;
                                                                                for (int i = 0; i < n + 1; ++i) {
                                                                                    p[7][i] = p[7][i] - p[6][i] - p[5][i] - p[4][i] + p[3][i] + p[2][i] + p[1][i] - p[0][i];
                                                                                }
                                                                                std::reverse(p[7].begin(), p[7].end());
                                                                                if (!dividePolynomialByPolynomial(p[7], bin_exp[3])) {
                                                                                    ++Z1;
                                                                                    continue;
                                                                                }

                                                                                /*
                                                                                p11101
                                                                                - p11100 - p11001 - p10101 - p01101
                                                                                + p11000 + p10100 + p10001 + p01100 + p01001 + p00101
                                                                                - p10000 - p01000 - p00100 - p00001
                                                                                + p00000
                                                                                */
                                                                                p[15] = s[14]->poly_1->coef_bk;
                                                                                p[14] = s[14]->poly_0->coef_bk;
                                                                                p[13] = s[10]->poly_1->coef_bk;
                                                                                p[12] = s[9]->poly_1->coef_bk;
                                                                                p[11] = s[7]->poly_1->coef_bk;
                                                                                p[10] = s[10]->poly_0->coef_bk;
                                                                                p[9] = s[9]->poly_0->coef_bk;
                                                                                p[8] = s[4]->poly_1->coef_bk;
                                                                                p[7] = s[7]->poly_0->coef_bk;
                                                                                p[6] = s[3]->poly_1->coef_bk;
                                                                                p[5] = s[2]->poly_1->coef_bk;
                                                                                p[4] = s[4]->poly_0->coef_bk;
                                                                                p[3] = s[3]->poly_0->coef_bk;
                                                                                p[2] = s[2]->poly_0->coef_bk;
                                                                                p[1] = s[0]->poly_1->coef_bk;
                                                                                p[0] = s[0]->poly_0->coef_bk;
                                                                                for (int i = 0; i < n + 1; ++i) {
                                                                                    p[15][i] = p[15][i]
                                                                                        - p[14][i] - p[13][i] - p[12][i] - p[11][i]
                                                                                        + p[10][i] + p[9][i] + p[8][i] + p[7][i] + p[6][i]
                                                                                        + p[5][i] - p[4][i] - p[3][i] - p[2][i] - p[1][i]
                                                                                        + p[0][i];
                                                                                }
                                                                                std::reverse(p[15].begin(), p[15].end());
                                                                                if (!dividePolynomialByPolynomial(p[15], bin_exp[4])) {
                                                                                    ++Z2;
                                                                                    continue;
                                                                                }

                                                                                // p1111.
                                                                                for (size_t l15 = 0; l15 < l_size[15]; ++l15) {
                                                                                    s[15] = poly_level[7]->poly_1->stat_l[l15];

                                                                                    /*
                                                                                    p11110
                                                                                    - p11100 - p11010 - p10110 - p01110
                                                                                    + p11000 + p10100 + p10010 + p01100 + p01010 + p00110
                                                                                    - p10000 - p01000 - p00100 - p00010
                                                                                    + p00000
                                                                                    */
                                                                                    p[15] = s[15]->poly_0->coef_bk;
                                                                                    p[14] = s[14]->poly_0->coef_bk;
                                                                                    p[13] = s[13]->poly_0->coef_bk;
                                                                                    p[12] = s[12]->poly_0->coef_bk;
                                                                                    p[11] = s[11]->poly_0->coef_bk;
                                                                                    p[10] = s[10]->poly_0->coef_bk;
                                                                                    p[9] = s[9]->poly_0->coef_bk;
                                                                                    p[8] = s[8]->poly_0->coef_bk;
                                                                                    p[7] = s[7]->poly_0->coef_bk;
                                                                                    p[6] = s[6]->poly_0->coef_bk;
                                                                                    p[5] = s[5]->poly_0->coef_bk;
                                                                                    p[4] = s[4]->poly_0->coef_bk;
                                                                                    p[3] = s[3]->poly_0->coef_bk;
                                                                                    p[2] = s[2]->poly_0->coef_bk;
                                                                                    p[1] = s[1]->poly_0->coef_bk;
                                                                                    p[0] = s[0]->poly_0->coef_bk;
                                                                                    for (int i = 0; i < n + 1; ++i) {
                                                                                        p[15][i] = p[15][i]
                                                                                            - p[14][i] - p[13][i] - p[12][i] - p[11][i]
                                                                                            + p[10][i] + p[9][i] + p[8][i] + p[7][i] + p[6][i] + p[5][i]
                                                                                            - p[4][i] - p[3][i] - p[2][i] - p[1][i]
                                                                                            + p[0][i];
                                                                                    }
                                                                                    std::reverse(p[15].begin(), p[15].end());
                                                                                    if (!dividePolynomialByPolynomial(p[15], bin_exp[4])) {
                                                                                        ++Z3;
                                                                                        continue;
                                                                                    }

                                                                                    /*
                                                                                    p11111
                                                                                    - p11110 - p11101 - p11011 - p10111 - p01111
                                                                                    + p11100 + p11010 + p11001 + p10110 + p10101 + p10011 + p01110 + p01101 + p01011 + p00111
                                                                                    - p11000 - p10100 - p10010 - p10001 - p01100 - p01010 - p01001 - p00110 - p00101 - p00011
                                                                                    + p10000 + p01000 + p00100 + p00010 + p00001
                                                                                    - p00000
                                                                                    */
                                                                                    p[31] = s[15]->poly_1->coef_bk;
                                                                                    p[30] = s[15]->poly_0->coef_bk;
                                                                                    p[29] = s[14]->poly_1->coef_bk;
                                                                                    p[28] = s[13]->poly_1->coef_bk;
                                                                                    p[27] = s[12]->poly_1->coef_bk;
                                                                                    p[26] = s[11]->poly_1->coef_bk;
                                                                                    p[25] = s[14]->poly_0->coef_bk;
                                                                                    p[24] = s[13]->poly_0->coef_bk;
                                                                                    p[23] = s[10]->poly_1->coef_bk;
                                                                                    p[22] = s[12]->poly_0->coef_bk;
                                                                                    p[21] = s[9]->poly_1->coef_bk;
                                                                                    p[20] = s[8]->poly_1->coef_bk;
                                                                                    p[19] = s[11]->poly_0->coef_bk;
                                                                                    p[18] = s[7]->poly_1->coef_bk;
                                                                                    p[17] = s[6]->poly_1->coef_bk;
                                                                                    p[16] = s[5]->poly_0->coef_bk;
                                                                                    p[15] = s[10]->poly_0->coef_bk;
                                                                                    p[14] = s[9]->poly_0->coef_bk;
                                                                                    p[13] = s[8]->poly_0->coef_bk;
                                                                                    p[12] = s[4]->poly_1->coef_bk;
                                                                                    p[11] = s[7]->poly_0->coef_bk;
                                                                                    p[10] = s[6]->poly_0->coef_bk;
                                                                                    p[9] = s[3]->poly_1->coef_bk;
                                                                                    p[8] = s[5]->poly_0->coef_bk;
                                                                                    p[7] = s[2]->poly_1->coef_bk;
                                                                                    p[6] = s[1]->poly_1->coef_bk;
                                                                                    p[5] = s[4]->poly_0->coef_bk;
                                                                                    p[4] = s[3]->poly_0->coef_bk;
                                                                                    p[3] = s[2]->poly_0->coef_bk;
                                                                                    p[2] = s[1]->poly_0->coef_bk;
                                                                                    p[1] = s[0]->poly_1->coef_bk;
                                                                                    p[0] = s[0]->poly_0->coef_bk;
                                                                                    for (int i = 0; i < n + 1; ++i) {
                                                                                        p[31][i] = p[31][i]
                                                                                            - p[30][i] - p[29][i] - p[28][i] - p[27][i] - p[26][i]
                                                                                            + p[25][i] + p[24][i] + p[23][i] + p[22][i] + p[21][i] + p[20][i] + p[19][i] + p[18][i] + p[17][i] + p[16][i]
                                                                                            - p[15][i] - p[14][i] - p[13][i] - p[12][i] - p[11][i] - p[10][i] - p[9][i] - p[8][i] - p[7][i] - p[6][i]
                                                                                            + p[5][i] + p[4][i] + p[3][i] + p[2][i] + p[1][i]
                                                                                            - p[0][i];
                                                                                    }
                                                                                    std::reverse(p[31].begin(), p[31].end());
                                                                                    if (!dividePolynomialByPolynomial(p[31], bin_exp[4])) {
                                                                                        ++Z4;
                                                                                        continue;
                                                                                    }

                                                                                    s[15]->status = true;
                                                                                    s[14]->status = true;
                                                                                    s[13]->status = true;
                                                                                    s[12]->status = true;
                                                                                    s[11]->status = true;
                                                                                    s[10]->status = true;
                                                                                    s[9]->status = true;
                                                                                    s[8]->status = true;
                                                                                    s[7]->status = true;
                                                                                    s[6]->status = true;
                                                                                    s[5]->status = true;
                                                                                    s[4]->status = true;
                                                                                    s[3]->status = true;
                                                                                    s[2]->status = true;
                                                                                    s[1]->status = true;
                                                                                    s[0]->status = true;

                                                                                    new_full_bk_level.push_back({ s[0], s[1], s[2], s[5], s[3], s[6], s[7], s[11], s[4], s[8], s[9], s[12], s[10], s[13], s[14], s[15] });
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                if (lim > 3) {
                    if (A) cout << "A: " << A << '\n';
                    if (B) cout << "B: " << B << '\n';
                    if (C) cout << "C: " << C << '\n';
                    if (D) cout << "D: " << D << '\n';
                    if (E) cout << "E: " << E << '\n';
                    if (F) cout << "F: " << F << '\n';
                    if (G) cout << "G: " << G << '\n';
                    if (H) cout << "H: " << H << '\n';
                    if (I) cout << "I: " << I << '\n';
                    if (J) cout << "J: " << J << '\n';
                    if (K) cout << "K: " << K << '\n';
                    if (L) cout << "L: " << L << '\n';
                    if (M) cout << "M: " << M << '\n';
                    if (N) cout << "N: " << N << '\n';
                    if (O) cout << "O: " << O << '\n';
                    if (P) cout << "P: " << P << '\n';
                    if (Q) cout << "Q: " << Q << '\n';
                    if (R) cout << "R: " << R << '\n';
                    if (S) cout << "S: " << S << '\n';
                    if (T) cout << "T: " << T << '\n';
                    if (U) cout << "U: " << U << '\n';
                    if (V) cout << "V: " << V << '\n';
                    if (W) cout << "W: " << W << '\n';
                    if (X) cout << "X: " << X << '\n';
                    if (Y) cout << "Y: " << Y << '\n';
                    if (Z) cout << "Z: " << Z << '\n';
                    if (Z1) cout << "Z1: " << Z1 << '\n';
                    if (Z2) cout << "Z2: " << Z2 << '\n';
                    if (Z3) cout << "Z3: " << Z3 << '\n';
                    if (Z4) cout << "Z4: " << Z4 << '\n';
                }

                ++it_h;
            }

            if (A) cout << "A: " << A << '\n';
            if (B) cout << "B: " << B << '\n';
            if (C) cout << "C: " << C << '\n';
            if (D) cout << "D: " << D << '\n';
            if (E) cout << "E: " << E << '\n';
            if (F) cout << "F: " << F << '\n';
            if (G) cout << "G: " << G << '\n';
            if (H) cout << "H: " << H << '\n';
            if (I) cout << "I: " << I << '\n';
            if (J) cout << "J: " << J << '\n';
            if (K) cout << "K: " << K << '\n';
            if (L) cout << "L: " << L << '\n';
            if (M) cout << "M: " << M << '\n';
            if (N) cout << "N: " << N << '\n';
            if (O) cout << "O: " << O << '\n';
            if (P) cout << "P: " << P << '\n';
            if (Q) cout << "Q: " << Q << '\n';
            if (R) cout << "R: " << R << '\n';
            if (S) cout << "S: " << S << '\n';
            if (T) cout << "T: " << T << '\n';
            if (U) cout << "U: " << U << '\n';
            if (V) cout << "V: " << V << '\n';
            if (W) cout << "W: " << W << '\n';
            if (X) cout << "X: " << X << '\n';
            if (Y) cout << "Y: " << Y << '\n';
            if (Z) cout << "Z: " << Z << '\n';
            if (Z1) cout << "Z1: " << Z1 << '\n';
            if (Z2) cout << "Z2: " << Z2 << '\n';
            if (Z3) cout << "Z3: " << Z3 << '\n';
            if (Z4) cout << "Z4: " << Z4 << '\n';

            full_bk_level = new_full_bk_level;

            cout << '\n' << "Full level: " << full_bk_level.size() << '\n';
            file << '\n' << "Full level: " << full_bk_level.size() << '\n';
            for (size_t i = 0; i < full_bk_level.size(); ++i) {
                file << '\n';
                for (size_t j = 0; j < full_bk_level[i].size(); ++j) {
                    print(file, full_bk_level[i][j]->poly_0->coef_bk, 1);
                    file << '\t';
                    print(file, full_bk_level[i][j]->poly_1->coef_bk, 1);
                }
            }

            it_h = 0;
            end_h = new_level.size();
            while (it_h < end_h) {
                it_l = 0;
                end_l = new_level[it_h].size();
                while (it_l < end_l) {
                    cont = false;
                    if (new_level[it_h][it_l]->elem_r == nullptr) {
                        new_level[it_h].erase(find(new_level[it_h].begin(), new_level[it_h].end(), new_level[it_h][it_l]));

                        end_l--;
                        it_l--;
                    }
                    else if (!new_level[it_h][it_l]->status) {
                        new_level[it_h][it_l]->RemoveLevel();
                        new_level[it_h].erase(find(new_level[it_h].begin(), new_level[it_h].end(), new_level[it_h][it_l]));

                        end_l--;
                        it_l--;
                    }

                    ++it_l;
                }

                if (!new_level[it_h].size()) {
                    new_level.erase(find(new_level.begin(), new_level.end(), new_level[it_h]));

                    it_h--;
                    end_h--;
                }

                ++it_h;
            }

            level = new_level;

            cout << '\n' << "Level: " << level.size();
            file << '\n' << "Level: " << level.size();
            count = 0;
            for (size_t i = 0; i < level.size(); ++i) {
                count += level[i].size();
                cout << ' ' << level[i].size() << ' ';
                file << ' ' << level[i].size() << ' ';
            }
            cout << ' ' << count << '\n';
            file << ' ' << count << '\n';

            ++lim;

            time_diff = double(clock() - time_start) / double(CLOCKS_PER_SEC);
            cout << "Izpildes laiks : " << time_diff / 60 << " min." << '\n';
        }

        cout << '\n' << "FINISHED";
        file << '\n' << "FINISHED";
        if (n == 0 && full_bk_level.size()) {
            cout << ' ' << "OK";
            file << ' ' << "OK";
        }
        cout << '\n';
        file << '\n';

        for (int i = 0; i < roots->size(); ++i) {
            delete (*roots)[i];
        }
        delete roots;

        file.close();

        time_diff = double(clock() - time_start) / double(CLOCKS_PER_SEC);
        cout << "Izpildes laiks : " << time_diff / 60 << " min." << '\n';
    }
};


int main() {
    // 1st param = n
    // 2nd param = d
    // 3rd param = log (0 - minimal, 1 - full)
    // 4th param = special case with n=14, d=5
    // 5th param = optimization
    BooleanFunction fun(10, 4, 0, false, false);
    fun.FindRepresentingPolynomial();

    return 0;
}