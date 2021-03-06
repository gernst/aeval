#ifndef SMTUTILS__HPP__
#define SMTUTILS__HPP__
#include <assert.h>

#include "ae/ExprSimpl.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;
namespace ufo
{
  
  class SMTUtils {
  private:
    
    ExprFactory &efac;
    EZ3 z3;
    ZSolver<EZ3> smt;
    
  public:
    
    SMTUtils (ExprFactory& _efac) :
    efac(_efac),
    z3(efac),
    smt (z3)
    {}

    template <typename T> Expr getModel(T& vars)
    {
      ExprVector eqs;
      getModel(vars, eqs);
      return conjoin (eqs, efac);
    }

    template <typename T> void getModel(T& vars, ExprVector& eqs)
    {
      ZSolver<EZ3>::Model m = smt.getModel();
      for (auto & v : vars) if (v != m.eval(v))
      {
        eqs.push_back(mk<EQ>(v, m.eval(v)));
      }
    }

    /**
     * SMT-check
     */
    bool isSat(Expr a, Expr b)
    {
      smt.reset();
      smt.assertExpr (a);
      smt.assertExpr (b);
      if (!smt.solve ()) {
        return false;
      }
      return true;
    }

    /**
     * SMT-check
     */
    bool isSat(Expr a, Expr b, Expr c)
    {
      smt.reset();
      smt.assertExpr (a);
      smt.assertExpr (b);
      smt.assertExpr (c);
      if (!smt.solve ()) {
        return false;
      }
      return true;
    }

    /**
     * SMT-check
     */
    bool isSat(Expr a, bool reset=true)
    {
      if (reset) smt.reset();
      smt.assertExpr (a);
      if (!smt.solve ()) {
        return false;
      }
      return true;
    }

    /**
     * SMT-based formula equivalence check
     */
    bool isEquiv(Expr a, Expr b)
    {
      return implies (a, b) && implies (b, a);
    }
    
    /**
     * SMT-based implication check
     */
    bool implies (Expr a, Expr b)
    {
      if (isOpX<TRUE>(b)) return true;
      if (isOpX<FALSE>(a)) return true;
      return ! isSat(a, mk<NEG>(b));
    }
    
    /**
     * SMT-based check for a tautology
     */
    bool isTrue(Expr a){
      if (isOpX<TRUE>(a)) return true;
      return !isSat(mk<NEG>(a));
    }
    
    /**
     * SMT-based check for false
     */
    bool isFalse(Expr a){
      if (isOpX<FALSE>(a)) return true;
      return !isSat(a);
    }

    /**
     * Check if v has only one sat assignment in phi
     */
    bool hasOneModel(Expr v, Expr phi) {
      if (isFalse(phi)) return false;

      ZSolver<EZ3>::Model m = smt.getModel();
      Expr val = m.eval(v);
      if (v == val) return false;

      ExprSet assumptions;
      assumptions.insert(mk<NEQ>(v, val));

      return (!isSat(conjoin(assumptions, efac), false));
    }

    /**
     * ITE-simplifier (prt 2)
     */
    Expr simplifyITE(Expr ex, Expr upLevelCond)
    {
      if (isOpX<ITE>(ex)){

        Expr cond = ex->arg(0);
        Expr br1 = ex->arg(1);
        Expr br2 = ex->arg(2);

        if (!isSat(cond, upLevelCond)) return br2;

        if (!isSat(mk<NEG>(cond), upLevelCond)) return br1;

        return mk<ITE>(cond,
                       simplifyITE(br1, mk<AND>(upLevelCond, cond)),
                       simplifyITE(br2, mk<AND>(upLevelCond, mk<NEG>(cond))));
      } else {
        return ex;
      }
    }

    /**
     * ITE-simplifier (prt 1)
     */
    Expr simplifyITE(Expr ex)
    {
      if (isOpX<ITE>(ex)){

        Expr cond = simplifyITE(ex->arg(0));
        Expr br1 = ex->arg(1);
        Expr br2 = ex->arg(2);

        if (isOpX<TRUE>(cond)) return br1;
        if (isOpX<FALSE>(cond)) return br2;

        if (br1 == br2) return br1;

        if (isOpX<TRUE>(br1) && isOpX<FALSE>(br2)) return cond;

        if (isOpX<FALSE>(br1) && isOpX<TRUE>(br2)) return mk<NEG>(cond);

        return mk<ITE>(cond,
                       simplifyITE(br1, cond),
                       simplifyITE(br2, mk<NEG>(cond)));

      }
      else if (isOpX<IMPL>(ex)) {

        return mk<IMPL>(simplifyITE(ex->left()), simplifyITE(ex->right()));
      } else if (isOpX<AND>(ex) || isOpX<OR>(ex)){

        ExprSet args;
        for (auto it = ex->args_begin(), end = ex->args_end(); it != end; ++it){
          args.insert(simplifyITE(*it));
        }
        return isOpX<AND>(ex) ? conjoin(args, efac) : disjoin (args, efac);
      }
      return ex;
    }
    
    /**
     * Remove some redundant conjuncts from the set of formulas
     */
    void removeRedundantConjuncts(ExprSet& conjs)
    {
      if (conjs.size() < 2) return;
      ExprSet newCnjs = conjs;

      for (auto & cnj : conjs)
      {
        if (isTrue (cnj))
        {
          newCnjs.erase(cnj);
          continue;
        }

        ExprSet newCnjsTry = newCnjs;
        newCnjsTry.erase(cnj);

        if (implies (conjoin(newCnjsTry, efac), cnj)) newCnjs.erase(cnj);
      }
      conjs = newCnjs;
    }

    /**
     * Remove some redundant conjuncts from the formula
     */
    Expr removeRedundantConjuncts(Expr exp)
    {
      ExprSet conjs;
      getConj(exp, conjs);
      if (conjs.size() < 2) return exp;
      else
      {
        removeRedundantConjuncts(conjs);
        return conjoin(conjs, efac);
      }
    }

    /**
     * Remove some redundant disjuncts from the formula
     */
    void removeRedundantDisjuncts(ExprSet& disjs)
    {
      if (disjs.size() < 2) return;
      ExprSet newDisjs = disjs;

      for (auto & disj : disjs)
      {
        if (isFalse (disj))
        {
          newDisjs.erase(disj);
          continue;
        }

        ExprSet newDisjsTry = newDisjs;
        newDisjsTry.erase(disj);

        if (implies (disj, disjoin(newDisjsTry, efac))) newDisjs.erase(disj);
      }
      disjs = newDisjs;
    }

    /**
     * Remove some redundant disjuncts from the formula
     */
    Expr removeRedundantDisjuncts(Expr exp)
    {
      ExprSet disjs;
      getDisj(exp, disjs);
      if (disjs.size() < 2) return exp;
      else
      {
        removeRedundantDisjuncts(disjs);
        return disjoin(disjs, efac);
      }
    }

    /**
     * Model-based simplification of a formula with 1 (one only) variable
     */
    Expr numericUnderapprox(Expr exp)
    {
      ExprVector cnstr_vars;
      filter (exp, bind::IsConst (), back_inserter (cnstr_vars));
      if (cnstr_vars.size() == 1)
      {
        smt.reset();
        smt.assertExpr (exp);
        if (smt.solve ()) {
          ZSolver<EZ3>::Model m = smt.getModel();
          return mk<EQ>(cnstr_vars[0], m.eval(cnstr_vars[0]));
        }
      }
      return exp;
    }

    void serialize_formula(Expr form)
    {
      smt.reset();
      smt.assertExpr(form);
      smt.toSmtLib (outs());
      outs().flush ();
    }

    template <typename T> void serialize_formula(T& forms)
    {
      smt.reset();
      for (auto form : forms) smt.assertExpr(form);
      smt.toSmtLib (outs());
      outs().flush ();
    }
  };
  
  /**
   * Horn-based interpolation over particular vars
   */
  inline Expr getItp(Expr A, Expr B, ExprVector& sharedVars)
  {
    ExprFactory &efac = A->getFactory();
    EZ3 z3(efac);
    
    ExprVector allVars;
    filter (mk<AND>(A,B), bind::IsConst (), back_inserter (allVars));
    
    ExprVector sharedTypes;
    
    for (auto &var: sharedVars) {
      sharedTypes.push_back (bind::typeOf (var));
    }
    sharedTypes.push_back (mk<BOOL_TY> (efac));
    
    // fixed-point object
    ZFixedPoint<EZ3> fp (z3);
    ZParams<EZ3> params (z3);
    params.set (":engine", "pdr");
    params.set (":xform.slice", false);
    params.set (":xform.inline-linear", false);
    params.set (":xform.inline-eager", false);
    fp.set (params);
    
    Expr errRel = bind::boolConstDecl(mkTerm<string> ("err", efac));
    fp.registerRelation(errRel);
    Expr errApp = bind::fapp (errRel);
    
    Expr itpRel = bind::fdecl (mkTerm<string> ("itp", efac), sharedTypes);
    fp.registerRelation (itpRel);
    Expr itpApp = bind::fapp (itpRel, sharedVars);
    
    fp.addRule(allVars, boolop::limp (A, itpApp));
    fp.addRule(allVars, boolop::limp (mk<AND> (B, itpApp), errApp));
    
    tribool res;
    try {
      res = fp.query(errApp);
    } catch (z3::exception &e){
      char str[3000];
      strncpy(str, e.msg(), 300);
      outs() << "Z3 ex: " << str << "...\n";
      exit(55);
    }
    
    if (res) return NULL;
    
    return fp.getCoverDelta(itpApp);
  }
  
  /**
   * Horn-based interpolation
   */
  inline Expr getItp(Expr A, Expr B)
  {
    ExprVector sharedVars;
    
    ExprVector aVars;
    filter (A, bind::IsConst (), back_inserter (aVars));
    
    ExprVector bVars;
    filter (B, bind::IsConst (), back_inserter (bVars));
    
    // computing shared vars:
    for (auto &var: aVars) {
      if (find(bVars.begin(), bVars.end(), var) != bVars.end())
      {
        sharedVars.push_back(var);
      }
    }
    
    return getItp(A, B, sharedVars);
  };
  
}

#endif
