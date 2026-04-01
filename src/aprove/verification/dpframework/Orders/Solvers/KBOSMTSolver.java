package aprove.verification.dpframework.Orders.Solvers;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.SMTUtility.*;

/**
 * Solver for Knuth-Bendix orders with SMT solving
 * Currently implemented features:
 *  - basic KBO
 *  - quasi precedence
 *  - status
 *
 * @author Andreas Kelle-Emden
 * @version $Id$
 */
public class KBOSMTSolver implements AbortableConstraintSolver<TRSTerm> {

    private boolean quasi = false;
    private boolean status = false;
    private SMTEngine smtChecker = null;
    private AFSType afstype = AFSType.NOAFS;

    public KBOSMTSolver(final boolean quasi, final boolean status, final SMTEngine smtChecker) {
        this.quasi = quasi;
        this.status = status;
        this.smtChecker = smtChecker;
    }

    public void setQuasi(final boolean quasi) {
        this.quasi = quasi;
    }

    public void setStatus(final boolean status) {
        this.status = status;
    }

    public void setSMTChecker(final SMTEngine smtChecker) {
        this.smtChecker = smtChecker;
    }

    public void setAfstype(final AFSType afstype) {
        switch (afstype) {
        case NOAFS:
        case MONOTONEAFS:
        case FULLAFS:
            break;
        default:
            throw new UnsupportedOperationException("KBO currently only implements NOAFS, MONOTONEAFS and FULLAFS");
        }
        this.afstype = afstype;
    }

    private int countvar(final TRSTerm t, final TRSVariable var) {
        if (t instanceof TRSVariable) {
            if (t.equals(var)) {
                return 1;
            }
        } else {
            final FunctionSymbol sym = ((TRSFunctionApplication) t).getRootSymbol();
            final int arity = sym.getArity();
            int res = 0;
            for (int i = 0; i < arity; i++) {
                res += this.countvar(((TRSFunctionApplication) t).getArgument(i), var);
            }
            return res;
        }
        return 0;
    }

    private boolean checkApplicable(final TRSTerm l, final TRSTerm r) {
        final Set<TRSVariable> varSet = r.getVariables();
        for (final TRSVariable v : varSet) {
            if (this.countvar(l, v) < this.countvar(r, v)) {
                return false;
            }
        }
        return true;
    }

    // Recursively check if the term l is in the right form
    // for KBO2a: f1(f2(...fn(x)...))
    private boolean checkKBO2a(final TRSTerm l, final TRSVariable x) {
        if (l instanceof TRSVariable) {
            final TRSVariable v = (TRSVariable) l;
            return v.equals(x);
        } else {
            final TRSFunctionApplication fa = (TRSFunctionApplication) l;
            final FunctionSymbol sym = fa.getRootSymbol();
            final int arity = sym.getArity();
            if (arity == 1) {
                return this.checkKBO2a(fa.getArgument(0), x);
            } else {
                return false;
            }
        }
    }

    @Override
    public final ExportableOrder<TRSTerm> solve(final Collection<Constraint<TRSTerm>> constraints, final Abortion aborter)
            throws AbortionException {
        return this.solve(constraints, null, aborter);
    }

    public ExportableOrder<TRSTerm> solve(Collection<Constraint<TRSTerm>> cons, Set<? extends GeneralizedRule> nonStrict, final Abortion aborter)
            throws AbortionException {

        if (cons == null) {
            cons = new LinkedHashSet<Constraint<TRSTerm>>();
        }
        if (nonStrict == null) {
            nonStrict = new LinkedHashSet<Rule>();
        }
        final Collection<Constraint<TRSTerm>> cs = new LinkedHashSet<Constraint<TRSTerm>>(cons);

        for (final GeneralizedRule rule : nonStrict) {
            cs.add(Constraint.fromRule(rule, OrderRelation.GE));
        }

        SMTEncoder encoder = null;
        if (this.afstype == AFSType.NOAFS) {
            encoder = new NoAFSEncoder();
        } else {
            encoder = new FullAFSEncoder();
        }

        // Check function symbols for special characters
        final Set<FunctionSymbol> symSet = Constraint.getFunctionSymbols(cs);
        final Pair<Map<FunctionSymbol, String>, Map<String, FunctionSymbol>> mapPair =
            SMTUtility.getYICESSymNameMap(symSet);
        final Map<FunctionSymbol, String> symNameMap = mapPair.x;
        final Map<String, FunctionSymbol> retrMap = mapPair.y;

        final StringBuilder smtInput = new StringBuilder();

        // Define w_0 > 0
        smtInput.append("(define w0::nat)\n");
        smtInput.append("(assert (> w0 0))\n");
        // Define weight function w where
        // wfbar is the weight of the function symbol bar

        // Assert w(c) >= w0 for all constant functions c
        for (final FunctionSymbol sym : symSet) {
            smtInput.append("(define wf");
            smtInput.append(symNameMap.get(sym));
            smtInput.append("::nat)\n");
            if (sym.getArity() == 0) {
                smtInput.append("(assert (>= wf");
                smtInput.append(symNameMap.get(sym));
                smtInput.append(" w0))\n");
            }
        }

        // Encode ordering > on function symbols
        // here, 0 is the greatest element!

        if (!symSet.isEmpty()) {
            // Define new scalar data type for function symbols
            smtInput.append("(define-type funcsyms (scalar");
            for (final FunctionSymbol sym : symSet) {
                smtInput.append(" ");
                smtInput.append(symNameMap.get(sym));
            }
            smtInput.append("))\n");

            // Define nat representation of funcsyms
            // The greatest elements w.r.t. > have representation 0
            smtInput.append("(define relf::(-> funcsyms nat))\n");
            // Define strictness, if not quasi
            final Object[] symArr = symSet.toArray();
            if (!this.quasi) {
                for (int i = 0; i < symArr.length; i++) {
                    for (int j = i + 1; j < symArr.length; j++) {
                        smtInput.append("(assert (/= (relf ");
                        smtInput.append(symNameMap.get(symArr[i]));
                        smtInput.append(") (relf ");
                        smtInput.append(symNameMap.get(symArr[j]));
                        smtInput.append(")))\n");
                    }
                }
            }

            encoder.encodeDefines(smtInput, symSet, symNameMap);
        }

        // Encode admissibility

        // If f is a unary function symbol and has weight 0, it is the greatest
        // element in the ordering
        // quasi: one of the greatest (i.e. f >= g for all g)
        for (final FunctionSymbol sym : symSet) {
            if (sym.getArity() == 1) {
                smtInput.append("(assert (=> (= wf");
                smtInput.append(symNameMap.get(sym));
                smtInput.append(" 0) (= (relf ");
                smtInput.append(symNameMap.get(sym));
                smtInput.append(") 0)))\n");
            }
        }

        // Encode KBO
        smtInput.append("(define ge__");
        smtInput.append("::(-> nat nat bool))\n");
        smtInput.append("(define gr__");
        smtInput.append("::(-> nat nat bool))\n");
        int count = 0;
        for (final GeneralizedRule rule : nonStrict) {
            aborter.checkAbortion();
            count++;
            final TRSTerm l = rule.getLeft();
            final TRSTerm r = rule.getRight();
            encoder.encodeAll(l, r, smtInput, "", "", count, count, symSet, symNameMap);
            smtInput.append("(assert (ge__ ");
            smtInput.append(count);
            smtInput.append(" ");
            smtInput.append(count);
            smtInput.append("))\n");
        }
        for (final Constraint<TRSTerm> c : cons) {
            aborter.checkAbortion();
            count++;
            final TRSTerm l = c.getLeft();
            final TRSTerm r = c.getRight();
            final OrderRelation rel = c.getType();
            if (rel.equals(OrderRelation.GE)) {
                encoder.encodeAll(l, r, smtInput, "", "", count, count, symSet, symNameMap);
                smtInput.append("(assert (ge__ ");
                smtInput.append(count);
                smtInput.append(" ");
                smtInput.append(count);
                smtInput.append("))\n");
            } else if (rel.equals(OrderRelation.GR)) {
                encoder.encodeAll(l, r, smtInput, "", "", count, count, symSet, symNameMap);
                smtInput.append("(assert (gr__ ");
                smtInput.append(count);
                smtInput.append(" ");
                smtInput.append(count);
                smtInput.append("))\n");
            } else if (rel.equals(OrderRelation.EQ)) {
                if (!l.equals(r)) {
                    smtInput.append("(assert false)\n");
                }
            } else {
                // Not supported
                return null;
            }
        }

        if (!nonStrict.isEmpty()) {
            // Encode one-greater constraint for RRR and MRR
            count = 0;
            smtInput.append("(assert (or");
            for (final GeneralizedRule rule : nonStrict) {
                count++;
                smtInput.append(" (gr__ ");
                smtInput.append(count);
                smtInput.append(" ");
                smtInput.append(count);
                smtInput.append(")");
            }
            smtInput.append("))");
        }

        smtInput.append("(check)\n");

        // TODO
        //System.err.println(smtInput);

        // Call the SMT checker
        Pair<YNM, Map<String, String>> resPair;
        try {
            resPair = this.smtChecker.solve(smtInput.toString(), SMTLogic.QF_LIA, aborter);
        } catch (final WrongLogicException e) {
            System.err.println("Solver error: " + e.getErrorMessage());
            resPair = new Pair<>(YNM.MAYBE, null);
        }
        final Map<String, String> resMap = resPair.y;

        if (resPair.x != YNM.YES || resMap == null) {
            // SMT checker returned UNSAT or something unknown
            return null;
        }
        if (resMap.isEmpty()) {
            // SMT checker is veeeeeeery buggy!!!!!
            assert false : "SMT checker returned with no result!";
        }

        return encoder.getAndCheckOrder(cons, nonStrict, resMap, retrMap, symSet);

    }

    private abstract class SMTEncoder {
        public abstract void encodeAll(TRSTerm l,
            TRSTerm r,
            StringBuilder smtInput,
            String posL,
            String posR,
            int paramL,
            int paramR,
            Set<FunctionSymbol> symSet,
            Map<FunctionSymbol, String> symNameMap);

        // Recursively build a string of added weights for a given term
        protected abstract void buildWeightString(final TRSTerm l,
            final StringBuilder sb,
            final Map<FunctionSymbol, String> symNameMap);

        // Encode GREATER EQUAL
        public String encodeGE(final TRSTerm l,
            final TRSTerm r,
            final String posL,
            final String posR,
            final int paramL,
            final int paramR,
            final Set<FunctionSymbol> symSet,
            final Map<FunctionSymbol, String> symNameMap) {
            if (!KBOSMTSolver.this.checkApplicable(l, r)) {
                // KBO not applicable on this
                return "false";
            }
            final StringBuilder encodeString = new StringBuilder();
            if (l.equals(r)) {
                encodeString.append("true ");
            } else {
                // Get weight string for the terms
                final StringBuilder weightl = new StringBuilder();
                this.buildWeightString(l, weightl, symNameMap);
                final StringBuilder weightr = new StringBuilder();
                this.buildWeightString(r, weightr, symNameMap);
                encodeString.append("(or ");
                // KBO1: w(l) > w(r)
                encodeString.append("(> ");
                encodeString.append(weightl);
                encodeString.append(" ");
                encodeString.append(weightr);
                encodeString.append(") ");
                if (l instanceof TRSFunctionApplication) {
                    // KBO2: w(l) = w(r) AND ...
                    encodeString.append("(and (= ");
                    encodeString.append(weightl);
                    encodeString.append(" ");
                    encodeString.append(weightr);
                    encodeString.append(") ");
                    if (r instanceof TRSVariable) {
                        // KBO2a: l = f1(f2(...fn(x)...)), n >= 0 and r = x
                        final TRSVariable x = (TRSVariable) r;
                        if (KBOSMTSolver.this.checkKBO2a(l, x)) {
                            encodeString.append("true ");
                        } else {
                            encodeString.append("false ");
                        }
                    } else {
                        final TRSFunctionApplication fal = (TRSFunctionApplication) l;
                        final TRSFunctionApplication far = (TRSFunctionApplication) r;
                        final FunctionSymbol syml = fal.getRootSymbol();
                        final FunctionSymbol symr = far.getRootSymbol();
                        final String symNamel = symNameMap.get(syml);
                        final String symNamer = symNameMap.get(symr);

                        encodeString.append("(or ");
                        // KBO2b: l = f(...), r = g(...) and f > g
                        encodeString.append("(< (relf ");
                        encodeString.append(symNameMap.get(syml));
                        encodeString.append(") (relf ");
                        encodeString.append(symNameMap.get(symr));
                        encodeString.append(")) ");

                        encodeString.append("(and ");
                        encodeString.append("(= (relf ");
                        encodeString.append(symNameMap.get(syml));
                        encodeString.append(") (relf ");
                        encodeString.append(symNameMap.get(symr));
                        encodeString.append(")) ");
                        final int arityL = syml.getArity();
                        final int arityR = symr.getArity();
                        final int arity = (arityL > arityR) ? arityR : arityL;
                        if (arity > 0) {
                            encodeString.append("(or ");

                            // KBO2c: l = f(s1, ..., sn), r = f(t1, ..., tm) and
                            // s1 >= t1, ..., s(i-1) >= t(i-1), si > ti for some i <= k
                            // or si >= ti for all i <= k
                            // where k = min(n,m)
                            for (int i = 0; i < arity; i++) {
                                // subterm i is greater, all subterms left of that are greaterequal
                                encodeString.append("(and (gr");
                                encodeString.append(posL);
                                encodeString.append("_");
                                encodeString.append(paramL);
                                encodeString.append("__");
                                encodeString.append(posR);
                                encodeString.append("_");
                                encodeString.append(paramR);
                                encodeString.append(" (stat");
                                encodeString.append(symNamel);
                                encodeString.append(" ");
                                encodeString.append(i);
                                encodeString.append(") (stat");
                                encodeString.append(symNamer);
                                encodeString.append(" ");
                                encodeString.append(i);
                                encodeString.append("))");
                                for (int j = 0; j < i; j++) {
                                    encodeString.append(" (ge");
                                    encodeString.append(posL);
                                    encodeString.append("_");
                                    encodeString.append(paramL);
                                    encodeString.append("__");
                                    encodeString.append(posR);
                                    encodeString.append("_");
                                    encodeString.append(paramR);
                                    encodeString.append(" (stat");
                                    encodeString.append(symNamel);
                                    encodeString.append(" ");
                                    encodeString.append(j);
                                    encodeString.append(") (stat");
                                    encodeString.append(symNamer);
                                    encodeString.append(" ");
                                    encodeString.append(j);
                                    encodeString.append("))");
                                }
                                encodeString.append(")");
                            }
                            if (arityL >= arityR) {
                                encodeString.append("(and");
                                for (int j = 0; j < arity; j++) {
                                    encodeString.append(" (ge");
                                    encodeString.append(posL);
                                    encodeString.append("_");
                                    encodeString.append(paramL);
                                    encodeString.append("__");
                                    encodeString.append(posR);
                                    encodeString.append("_");
                                    encodeString.append(paramR);
                                    encodeString.append(" (stat");
                                    encodeString.append(symNamel);
                                    encodeString.append(" ");
                                    encodeString.append(j);
                                    encodeString.append(") (stat");
                                    encodeString.append(symNamer);
                                    encodeString.append(" ");
                                    encodeString.append(j);
                                    encodeString.append("))");
                                }
                                encodeString.append(")");
                            } else {
                                encodeString.append("false ");
                            }
                            encodeString.append(")");
                        } else if (arityL < arityR) {
                            encodeString.append("false ");
                        }
                        encodeString.append("))");
                    }
                    encodeString.append(")");

                } else {
                    // l is a variable
                    // l >= r is satisfied iff
                    // r is a constant with minimal weight and
                    // minimal precedence
                    if (r instanceof TRSVariable) {
                        encodeString.append("false");
                    } else {
                        final TRSFunctionApplication far = (TRSFunctionApplication) r;
                        final FunctionSymbol symr = far.getRootSymbol();
                        final int arity = symr.getArity();
                        if (arity == 0) {
                            // r is a constant
                            encodeString.append("(and (= wf");
                            encodeString.append(symNameMap.get(symr));
                            encodeString.append(" w0) ");
                            for (final FunctionSymbol sym : symSet) {
                                if (sym.getArity() == 0 && !sym.equals(symr)) {
                                    encodeString.append("(> (relf ");
                                    encodeString.append(symNameMap.get(symr));
                                    encodeString.append(") (relf ");
                                    encodeString.append(symNameMap.get(sym));
                                    encodeString.append("))");
                                }
                            }
                            encodeString.append(")");
                        } else {
                            encodeString.append("false");
                        }
                    }
                }
                encodeString.append(")\n");
            }
            return encodeString.toString();
        }

        // Encode GREATER THAN
        public String encodeGR(final TRSTerm l,
            final TRSTerm r,
            final String posL,
            final String posR,
            final int paramL,
            final int paramR,
            final Set<FunctionSymbol> symSet,
            final Map<FunctionSymbol, String> symNameMap) {
            if (!KBOSMTSolver.this.checkApplicable(l, r)) {
                // KBO not applicable on this
                return "false";
            }
            final StringBuilder encodeString = new StringBuilder();
            // Get weight string for the terms
            final StringBuilder weightl = new StringBuilder();
            this.buildWeightString(l, weightl, symNameMap);
            final StringBuilder weightr = new StringBuilder();
            this.buildWeightString(r, weightr, symNameMap);
            encodeString.append("(or ");
            // KBO1: w(l) > w(r)
            encodeString.append("(> ");
            encodeString.append(weightl);
            encodeString.append(" ");
            encodeString.append(weightr);
            encodeString.append(") ");
            if (l instanceof TRSFunctionApplication) {
                // KBO2: w(l) = w(r) AND ...
                encodeString.append("(and (= ");
                encodeString.append(weightl);
                encodeString.append(" ");
                encodeString.append(weightr);
                encodeString.append(") ");
                if (r instanceof TRSVariable) {
                    // KBO2a: l = f1(f2(...fn(x)...)), n > 0 and r = x
                    final TRSVariable x = (TRSVariable) r;
                    if (!l.equals(r) && KBOSMTSolver.this.checkKBO2a(l, x)) {
                        encodeString.append("true ");
                    } else {
                        encodeString.append("false ");
                    }
                } else {
                    final TRSFunctionApplication fal = (TRSFunctionApplication) l;
                    final TRSFunctionApplication far = (TRSFunctionApplication) r;
                    final FunctionSymbol syml = fal.getRootSymbol();
                    final FunctionSymbol symr = far.getRootSymbol();
                    final String symNamel = symNameMap.get(syml);
                    final String symNamer = symNameMap.get(symr);

                    encodeString.append("(or ");
                    // KBO2b: l = f(...), r = g(...) and f > g
                    encodeString.append("(< (relf ");
                    encodeString.append(symNameMap.get(syml));
                    encodeString.append(") (relf ");
                    encodeString.append(symNameMap.get(symr));
                    encodeString.append(")) ");

                    final int arity = syml.getArity();
                    if (arity == 0) {
                        encodeString.append("false ");
                    } else {
                        encodeString.append("(and ");
                        encodeString.append("(= (relf ");
                        encodeString.append(symNameMap.get(syml));
                        encodeString.append(") (relf ");
                        encodeString.append(symNameMap.get(symr));
                        encodeString.append(")) ");
                        final int arityR = symr.getArity();
                        if (arity > 0 && arityR > 0) {
                            encodeString.append("(or ");

                            // KBO2c (quasi): l = f(s1, ..., sn), r = g(t1, ..., tm),
                            // f ~ g and n > m
                            if (KBOSMTSolver.this.quasi && arity > arityR && arityR > 0) {
                                for (int i = 0; i < arityR; i++) {
                                    // subterm i is greater, all subterms left of that are greaterequal
                                    encodeString.append("(and (gr");
                                    encodeString.append(posL);
                                    encodeString.append("_");
                                    encodeString.append(paramL);
                                    encodeString.append("__");
                                    encodeString.append(posR);
                                    encodeString.append("_");
                                    encodeString.append(paramR);
                                    encodeString.append(" (stat");
                                    encodeString.append(symNamel);
                                    encodeString.append(" ");
                                    encodeString.append(i);
                                    encodeString.append(") (stat");
                                    encodeString.append(symNamer);
                                    encodeString.append(" ");
                                    encodeString.append(i);
                                    encodeString.append(")) ");
                                    for (int j = 0; j < i; j++) {
                                        encodeString.append(" (ge");
                                        encodeString.append(posL);
                                        encodeString.append("_");
                                        encodeString.append(paramL);
                                        encodeString.append("__");
                                        encodeString.append(posR);
                                        encodeString.append("_");
                                        encodeString.append(paramR);
                                        encodeString.append(" (stat");
                                        encodeString.append(symNamel);
                                        encodeString.append(" ");
                                        encodeString.append(j);
                                        encodeString.append(") (stat");
                                        encodeString.append(symNamer);
                                        encodeString.append(" ");
                                        encodeString.append(j);
                                        encodeString.append("))");
                                    }
                                    encodeString.append(")");
                                }
                                encodeString.append("(and");
                                for (int j = 0; j < arityR; j++) {
                                    encodeString.append(" (gr");
                                    encodeString.append(posL);
                                    encodeString.append("_");
                                    encodeString.append(paramL);
                                    encodeString.append("__");
                                    encodeString.append(posR);
                                    encodeString.append("_");
                                    encodeString.append(paramR);
                                    encodeString.append(" (stat");
                                    encodeString.append(symNamel);
                                    encodeString.append(" ");
                                    encodeString.append(j);
                                    encodeString.append(") (stat");
                                    encodeString.append(symNamer);
                                    encodeString.append(" ");
                                    encodeString.append(j);
                                    encodeString.append("))");
                                }
                                encodeString.append(")");
                            }

                            // KBO2c: l = f(s1, ..., sn), r = f(t1, ..., tn) and
                            // s1 >= t1, ..., s(i-1) >= t(i-1), si > ti for some i <= n
                            else if (arity <= arityR && arity > 0) {
                                for (int i = 0; i < arity; i++) {
                                    // subterm i is greater, all subterms left of that are greaterequal
                                    encodeString.append("(and (gr");
                                    encodeString.append(posL);
                                    encodeString.append("_");
                                    encodeString.append(paramL);
                                    encodeString.append("__");
                                    encodeString.append(posR);
                                    encodeString.append("_");
                                    encodeString.append(paramR);
                                    encodeString.append(" (stat");
                                    encodeString.append(symNamel);
                                    encodeString.append(" ");
                                    encodeString.append(i);
                                    encodeString.append(") (stat");
                                    encodeString.append(symNamer);
                                    encodeString.append(" ");
                                    encodeString.append(i);
                                    encodeString.append("))");
                                    for (int j = 0; j < i; j++) {
                                        encodeString.append(" (ge");
                                        encodeString.append(posL);
                                        encodeString.append("_");
                                        encodeString.append(paramL);
                                        encodeString.append("__");
                                        encodeString.append(posR);
                                        encodeString.append("_");
                                        encodeString.append(paramR);
                                        encodeString.append(" (stat");
                                        encodeString.append(symNamel);
                                        encodeString.append(" ");
                                        encodeString.append(j);
                                        encodeString.append(") (stat");
                                        encodeString.append(symNamer);
                                        encodeString.append(" ");
                                        encodeString.append(j);
                                        encodeString.append("))");
                                    }
                                    encodeString.append(")");
                                }
                            } else {
                                encodeString.append("false");
                            }
                            encodeString.append(")");
                        }
                        encodeString.append(")");
                    }
                    encodeString.append(")");
                }
                encodeString.append(")");

            } else {
                // l is a variable - not a good idea
                encodeString.append("false");
            }
            encodeString.append(")");
            return encodeString.toString();
        }

        public abstract void encodeDefines(StringBuilder smtInput,
            Set<FunctionSymbol> symSet,
            Map<FunctionSymbol, String> symNameMap);

        public abstract ExportableOrder<TRSTerm> getAndCheckOrder(Collection<Constraint<TRSTerm>> cons,
            Set<? extends GeneralizedRule> nonStrict,
            Map<String, String> resMap,
            Map<String, FunctionSymbol> retrMap,
            Set<FunctionSymbol> symSet);
    }

    private class NoAFSEncoder extends SMTEncoder {

        // Recursively build a string of added weights for a given term
        @Override
        protected void buildWeightString(final TRSTerm l,
            final StringBuilder sb,
            final Map<FunctionSymbol, String> symNameMap) {
            if (l instanceof TRSVariable) {
                sb.append("w0");
            } else {
                final TRSFunctionApplication fa = (TRSFunctionApplication) l;
                final FunctionSymbol sym = fa.getRootSymbol();
                final String symName = symNameMap.get(sym);
                final int arity = sym.getArity();
                if (arity == 0) {
                    sb.append(" wf");
                    sb.append(symName);
                } else {
                    sb.append("(+ wf");
                    sb.append(symName);
                    for (int i = 0; i < arity; i++) {
                        sb.append(" ");
                        this.buildWeightString(fa.getArgument(i), sb, symNameMap);
                    }
                    sb.append(")");
                }
            }
        }

        // Define all variables
        @Override
        public void encodeAll(final TRSTerm l,
            final TRSTerm r,
            final StringBuilder smtInput,
            final String posL,
            final String posR,
            final int paramL,
            final int paramR,
            final Set<FunctionSymbol> symSet,
            final Map<FunctionSymbol, String> symNameMap) {
            if (!l.isVariable() && !r.isVariable()) {
                final TRSFunctionApplication fal = (TRSFunctionApplication) l;
                final TRSFunctionApplication far = (TRSFunctionApplication) r;
                final FunctionSymbol syml = fal.getRootSymbol();
                final FunctionSymbol symr = far.getRootSymbol();
                final int arityl = syml.getArity();
                final int arityr = symr.getArity();
                final int arity = (arityl < arityr) ? arityl : arityr;
                final String newPosL = posL + "_" + paramL;
                final String newPosR = posR + "_" + paramR;
                smtInput.append("(define gr");
                smtInput.append(newPosL);
                smtInput.append("__");
                smtInput.append(newPosR);
                smtInput.append("::(-> nat nat bool))\n");
                smtInput.append("(define ge");
                smtInput.append(newPosL);
                smtInput.append("__");
                smtInput.append(newPosR);
                smtInput.append("::(-> nat nat bool))\n");
                if (KBOSMTSolver.this.status) {
                    for (int i = 0; i < arityl; i++) {
                        for (int j = 0; j < arityr; j++) {
                            this.encodeAll(fal.getArgument(i), far.getArgument(j), smtInput, newPosL, newPosR, i, j,
                                symSet, symNameMap);
                        }
                    }
                } else {
                    for (int i = 0; i < arity; i++) {
                        this.encodeAll(fal.getArgument(i), far.getArgument(i), smtInput, newPosL, newPosR, i, i,
                            symSet, symNameMap);
                    }
                }
            }

            String encodeString;
            encodeString = this.encodeGR(l, r, posL, posR, paramL, paramR, symSet, symNameMap);
            smtInput.append("(assert (= (");
            smtInput.append("gr");
            smtInput.append(posL);
            smtInput.append("__");
            smtInput.append(posR);
            smtInput.append(" ");
            smtInput.append(paramL);
            smtInput.append(" ");
            smtInput.append(paramR);
            smtInput.append(") ");
            smtInput.append(encodeString);
            smtInput.append("))\n");

            encodeString = this.encodeGE(l, r, posL, posR, paramL, paramR, symSet, symNameMap);
            smtInput.append("(assert (= (");
            smtInput.append("ge");
            smtInput.append(posL);
            smtInput.append("__");
            smtInput.append(posR);
            smtInput.append(" ");
            smtInput.append(paramL);
            smtInput.append(" ");
            smtInput.append(paramR);
            smtInput.append(") ");
            smtInput.append(encodeString);
            smtInput.append("))\n");
        }

        @Override
        public ExportableOrder<TRSTerm> getAndCheckOrder(final Collection<Constraint<TRSTerm>> cons,
            final Set<? extends GeneralizedRule> nonStrict,
            final Map<String, String> resMap,
            final Map<String, FunctionSymbol> retrMap,
            final Set<FunctionSymbol> symSet) {
            final Qoset<FunctionSymbol> precedence = Qoset.<FunctionSymbol>create(symSet);
            final Map<FunctionSymbol, BigInteger> weightMap = new LinkedHashMap<FunctionSymbol, BigInteger>();
            final Map<String, Integer> precMap = new LinkedHashMap<String, Integer>();
            BigInteger w0 = null;

            final StatusMap<FunctionSymbol> statusMap = StatusMap.create(symSet);
            final Map<FunctionSymbol, int[]> statusCreateMap = new LinkedHashMap<FunctionSymbol, int[]>();
            for (final FunctionSymbol sym : symSet) {
                statusCreateMap.put(sym, new int[sym.getArity()]);
            }
            for (final Map.Entry<String, String> entry : resMap.entrySet()) {
                final String key = entry.getKey();
                final String val = entry.getValue();

                if (key.startsWith("wf")) {
                    // function symbol weight
                    final String symName = key.substring(2);
                    final FunctionSymbol sym = retrMap.get(symName);
                    weightMap.put(sym, BigInteger.valueOf(Integer.parseInt(val)));
                } else if (key.startsWith("(relf")) {
                    // precedence
                    final String symName = key.substring(6, key.length() - 1);
                    final FunctionSymbol sym = retrMap.get(symName);
                    assert (sym != null) : key + " " + symName + retrMap;
                    final Integer prec = Integer.parseInt(val);
                    for (final Map.Entry<String, Integer> e : precMap.entrySet()) {
                        final String oldSymName = e.getKey();
                        final FunctionSymbol oldSym = retrMap.get(oldSymName);
                        if (Globals.useAssertions) {
                            assert (oldSym != null);
                        }
                        final Integer oldP = e.getValue();
                        try {
                            if (oldP < prec) {
                                precedence.setGreater(oldSym, sym);
                            } else if (oldP.equals(prec)) {
                                precedence.setEquivalent(oldSym, sym);
                            } else {
                                precedence.setGreater(sym, oldSym);
                            }
                        } catch (final OrderedSetException exc) {
                            if (Globals.useAssertions) {
                                assert false;
                            }
                            return null;
                        }
                    }
                    precMap.put(symName, prec);
                } else if (key.startsWith("w0")) {
                    // weight of variables
                    w0 = BigInteger.valueOf(Integer.parseInt(val));
                } else if (key.startsWith("(stat")) {
                    final String keyString = key.substring(5, key.length() - 1);
                    final String[] keyArray = keyString.split(" ");
                    final FunctionSymbol sym = retrMap.get(keyArray[0]);
                    final Integer before = Integer.parseInt(keyArray[1]);
                    final Integer after = Integer.parseInt(val);
                    final int[] thisArr = statusCreateMap.get(sym);
                    thisArr[before] = after;
                }
            }

            for (final FunctionSymbol sym : symSet) {
                final int[] arr = statusCreateMap.get(sym);
                final Permutation perm = Permutation.create(arr);
                statusMap.assignPermutation(sym, perm);
            }

            if (Globals.useAssertions) {
                if (w0 == null) {
                    assert (w0 != null);
                }
            }

            // Check if some symbols do not occur in weight map
            for (final FunctionSymbol sym : symSet) {
                if (weightMap.get(sym) == null) {
                    weightMap.put(sym, BigInteger.ZERO);
                }
            }

            QKBO solvingOrder;
            if (KBOSMTSolver.this.quasi) {
                if (KBOSMTSolver.this.status) {
                    solvingOrder = new QKBOS(precedence, weightMap, w0, statusMap);
                } else {
                    solvingOrder = new QKBO(precedence, weightMap, w0);
                }
            } else {
                if (KBOSMTSolver.this.status) {
                    solvingOrder = new KBOS(precedence, weightMap, w0, statusMap);
                } else {
                    solvingOrder = new NewKBO(precedence, weightMap, w0);
                }
            }

            // Check order
            if (Globals.useAssertions) {
                if (!nonStrict.isEmpty()) {
                    boolean hasOneGreater = false;
                    for (final GeneralizedRule rule : nonStrict) {
                        if (!solvingOrder.solves(Constraint.fromRule(rule, OrderRelation.GE))) {
                            System.err.println("Non-strict constraint not solved!");
                            System.err.println("Rule:" + rule);
                            System.err.println("Ordering:\n" + solvingOrder);
                            assert false;
                        }
                        if (solvingOrder.solves(Constraint.fromRule(rule, OrderRelation.GR))) {
                            hasOneGreater = true;
                        }
                    }
                    if (!hasOneGreater) {
                        System.err.println("No rule is oriented strictly!");
                        System.err.println("Ordering:\n" + solvingOrder);
                        assert false;
                    }
                }
                for (final Constraint<TRSTerm> c : cons) {
                    if (!solvingOrder.solves(c)) {
                        System.err.println("Constraint not solved!");
                        System.err.println("Constraint:" + c);
                        System.err.println("Ordering:\n" + solvingOrder);
                        assert false;
                    }
                }
            }

            return solvingOrder;

        }

        @Override
        public void encodeDefines(final StringBuilder smtInput,
            final Set<FunctionSymbol> symSet,
            final Map<FunctionSymbol, String> symNameMap) {
            // Define for every function symbol with arity > 1 a status function
            for (final FunctionSymbol sym : symSet) {
                final int arity = sym.getArity();
                final String symName = symNameMap.get(sym);
                smtInput.append("(define stat");
                smtInput.append(symName);
                smtInput.append("::(-> nat nat))\n");
                for (int i = 0; i < arity; i++) {
                    // permutation constraints:
                    // statf(i) < n for all i < n
                    // where k is the number of arguments to be compared
                    smtInput.append("(assert (< (stat");
                    smtInput.append(symName);
                    smtInput.append(" ");
                    smtInput.append(i);
                    smtInput.append(") ");
                    smtInput.append(arity);
                    smtInput.append("))\n");
                    for (int j = i + 1; j < arity; j++) {
                        // Every position is taken exactly one time
                        smtInput.append("(assert (/= (stat");
                        smtInput.append(symName);
                        smtInput.append(" ");
                        smtInput.append(i);
                        smtInput.append(") (stat");
                        smtInput.append(symName);
                        smtInput.append(" ");
                        smtInput.append(j);
                        smtInput.append(")))\n");
                    }
                }
                if (!KBOSMTSolver.this.status) {
                    // All arguments must be compared in strict ordering
                    for (int i = 0; i < arity; i++) {
                        smtInput.append("(assert (= (stat");
                        smtInput.append(symName);
                        smtInput.append(" ");
                        smtInput.append(i);
                        smtInput.append(") ");
                        smtInput.append(i);
                        smtInput.append("))\n");
                    }
                }
            }
        }
    }

    private class FullAFSEncoder extends SMTEncoder {

        public FullAFSEncoder() {
            throw new UnsupportedOperationException("Not implemented yet!");
        }

        // Recursively build a string of added weights for a given term
        @Override
        protected void buildWeightString(final TRSTerm l,
            final StringBuilder sb,
            final Map<FunctionSymbol, String> symNameMap) {
            if (l instanceof TRSVariable) {
                sb.append("w0");
            } else {
                final TRSFunctionApplication fa = (TRSFunctionApplication) l;
                final FunctionSymbol sym = fa.getRootSymbol();
                final String symName = symNameMap.get(sym);
                final int arity = sym.getArity();
                if (arity == 0) {
                    sb.append(" wf");
                    sb.append(symName);
                } else {
                    sb.append("(+ wf");
                    sb.append(symName);
                    for (int i = 0; i < arity; i++) {
                        sb.append(" (ite (or (and (= afsflag");
                        sb.append(symName);
                        sb.append(" -1) (< (stat");
                        sb.append(symName);
                        sb.append(" ");
                        sb.append(i);
                        sb.append(") argcnt");
                        sb.append(symName);
                        sb.append(")) (= afsflag");
                        sb.append(symName);
                        sb.append(" ");
                        sb.append(i);
                        sb.append(")) (");
                        this.buildWeightString(fa.getArgument(i), sb, symNameMap);
                        sb.append(") 0)");
                    }
                    sb.append(")");
                }
            }
        }



        // Define all variables
        @Override
        public void encodeAll(final TRSTerm l,
            final TRSTerm r,
            final StringBuilder smtInput,
            final String posL,
            final String posR,
            final int paramL,
            final int paramR,
            final Set<FunctionSymbol> symSet,
            final Map<FunctionSymbol, String> symNameMap) {
            if (!l.isVariable() && !r.isVariable()) {
                final TRSFunctionApplication fal = (TRSFunctionApplication) l;
                final TRSFunctionApplication far = (TRSFunctionApplication) r;
                final FunctionSymbol syml = fal.getRootSymbol();
                final FunctionSymbol symr = far.getRootSymbol();
                final int arityl = syml.getArity();
                final int arityr = symr.getArity();
                final int arity = (arityl < arityr) ? arityl : arityr;
                final String newPosL = posL + "_" + paramL;
                final String newPosR = posR + "_" + paramR;
                smtInput.append("(define gr");
                smtInput.append(newPosL);
                smtInput.append("__");
                smtInput.append(newPosR);
                smtInput.append("::(-> nat nat bool))\n");
                smtInput.append("(define ge");
                smtInput.append(newPosL);
                smtInput.append("__");
                smtInput.append(newPosR);
                smtInput.append("::(-> nat nat bool))\n");
                if (KBOSMTSolver.this.status) {
                    for (int i = 0; i < arityl; i++) {
                        for (int j = 0; j < arityr; j++) {
                            this.encodeAll(fal.getArgument(i), far.getArgument(j), smtInput, newPosL, newPosR, i, j,
                                symSet, symNameMap);
                        }
                    }
                } else {
                    for (int i = 0; i < arity; i++) {
                        this.encodeAll(fal.getArgument(i), far.getArgument(i), smtInput, newPosL, newPosR, i, i,
                            symSet, symNameMap);
                    }
                }
            }

            String encodeString;
            encodeString = this.encodeGR(l, r, posL, posR, paramL, paramR, symSet, symNameMap);
            smtInput.append("(assert (= (");
            smtInput.append("gr");
            smtInput.append(posL);
            smtInput.append("__");
            smtInput.append(posR);
            smtInput.append(" ");
            smtInput.append(paramL);
            smtInput.append(" ");
            smtInput.append(paramR);
            smtInput.append(") ");
            smtInput.append(encodeString);
            smtInput.append("))\n");

            encodeString = this.encodeGE(l, r, posL, posR, paramL, paramR, symSet, symNameMap);
            smtInput.append("(assert (= (");
            smtInput.append("ge");
            smtInput.append(posL);
            smtInput.append("__");
            smtInput.append(posR);
            smtInput.append(" ");
            smtInput.append(paramL);
            smtInput.append(" ");
            smtInput.append(paramR);
            smtInput.append(") ");
            smtInput.append(encodeString);
            smtInput.append("))\n");
        }

        @Override
        public ExportableOrder<TRSTerm> getAndCheckOrder(final Collection<Constraint<TRSTerm>> cons,
            final Set<? extends GeneralizedRule> nonStrict,
            final Map<String, String> resMap,
            final Map<String, FunctionSymbol> retrMap,
            final Set<FunctionSymbol> symSet) {
            final Qoset<FunctionSymbol> precedence = Qoset.<FunctionSymbol>create(symSet);
            final Map<FunctionSymbol, BigInteger> weightMap = new LinkedHashMap<FunctionSymbol, BigInteger>();
            final Map<String, Integer> precMap = new LinkedHashMap<String, Integer>();
            BigInteger w0 = null;

            final StatusMap<FunctionSymbol> statusMap = StatusMap.create(symSet);
            final Map<FunctionSymbol, int[]> statusCreateMap = new LinkedHashMap<FunctionSymbol, int[]>();
            for (final FunctionSymbol sym : symSet) {
                statusCreateMap.put(sym, new int[sym.getArity()]);
            }
            for (final Map.Entry<String, String> entry : resMap.entrySet()) {
                final String key = entry.getKey();
                final String val = entry.getValue();

                if (key.startsWith("wf")) {
                    // function symbol weight
                    final String symName = key.substring(2);
                    final FunctionSymbol sym = retrMap.get(symName);
                    weightMap.put(sym, BigInteger.valueOf(Integer.parseInt(val)));
                } else if (key.startsWith("(relf")) {
                    // precedence
                    final String symName = key.substring(6, key.length() - 1);
                    final FunctionSymbol sym = retrMap.get(symName);
                    final Integer prec = Integer.parseInt(val);
                    for (final Map.Entry<String, Integer> e : precMap.entrySet()) {
                        final String oldSymName = e.getKey();
                        final FunctionSymbol oldSym = retrMap.get(oldSymName);
                        if (Globals.useAssertions) {
                            assert (oldSym != null);
                        }
                        final Integer oldP = e.getValue();
                        try {
                            if (oldP < prec) {
                                precedence.setGreater(oldSym, sym);
                            } else if (oldP.equals(prec)) {
                                precedence.setEquivalent(oldSym, sym);
                            } else {
                                precedence.setGreater(sym, oldSym);
                            }
                        } catch (final OrderedSetException exc) {
                            if (Globals.useAssertions) {
                                assert false;
                            }
                            return null;
                        }
                    }
                    precMap.put(symName, prec);
                } else if (key.startsWith("w0")) {
                    // weight of variables
                    w0 = BigInteger.valueOf(Integer.parseInt(val));
                } else if (key.startsWith("(stat")) {
                    final String keyString = key.substring(5, key.length() - 1);
                    final String[] keyArray = keyString.split(" ");
                    final FunctionSymbol sym = retrMap.get(keyArray[0]);
                    final Integer before = Integer.parseInt(keyArray[1]);
                    final Integer after = Integer.parseInt(val);
                    final int[] thisArr = statusCreateMap.get(sym);
                    thisArr[before] = after;
                }
            }

            for (final FunctionSymbol sym : symSet) {
                final int[] arr = statusCreateMap.get(sym);
                final Permutation perm = Permutation.create(arr);
                statusMap.assignPermutation(sym, perm);
            }

            if (Globals.useAssertions) {
                if (w0 == null) {
                    assert (w0 != null);
                }
            }

            // Check if some symbols do not occur in weight map
            for (final FunctionSymbol sym : symSet) {
                if (weightMap.get(sym) == null) {
                    weightMap.put(sym, BigInteger.ZERO);
                }
            }

            QKBO solvingOrder;
            if (KBOSMTSolver.this.quasi) {
                if (KBOSMTSolver.this.status) {
                    solvingOrder = new QKBOS(precedence, weightMap, w0, statusMap);
                } else {
                    solvingOrder = new QKBO(precedence, weightMap, w0);
                }
            } else {
                if (KBOSMTSolver.this.status) {
                    solvingOrder = new KBOS(precedence, weightMap, w0, statusMap);
                } else {
                    solvingOrder = new NewKBO(precedence, weightMap, w0);
                }
            }

            // Check order
            if (Globals.useAssertions) {
                if (!nonStrict.isEmpty()) {
                    boolean hasOneGreater = false;
                    for (final GeneralizedRule rule : nonStrict) {
                        if (!solvingOrder.solves(Constraint.fromRule(rule, OrderRelation.GE))) {
                            System.err.println("Non-strict constraint not solved!");
                            System.err.println("Rule:" + rule);
                            System.err.println("Ordering:\n" + solvingOrder);
                            assert false;
                        }
                        if (solvingOrder.solves(Constraint.fromRule(rule, OrderRelation.GR))) {
                            hasOneGreater = true;
                        }
                    }
                    if (!hasOneGreater) {
                        System.err.println("No rule is oriented strictly!");
                        System.err.println("Ordering:\n" + solvingOrder);
                        assert false;
                    }
                }
                for (final Constraint<TRSTerm> c : cons) {
                    if (!solvingOrder.solves(c)) {
                        System.err.println("Constraint not solved!");
                        System.err.println("Constraint:" + c);
                        System.err.println("Ordering:\n" + solvingOrder);
                        assert false;
                    }
                }
            }

            return solvingOrder;

        }

        @Override
        public void encodeDefines(final StringBuilder smtInput,
            final Set<FunctionSymbol> symSet,
            final Map<FunctionSymbol, String> symNameMap) {
            // Define argcounts and boolean functions for argument filtering
            for (final FunctionSymbol sym : symSet) {
                final String symName = symNameMap.get(sym);
                // afsflagf defines to which argument a function application
                // will be collapsed. If afsflagf == -1 the symbol will not be collapsed
                smtInput.append("(define afsflag");
                smtInput.append(symName);
                smtInput.append("::int)\n");
                // the first argcntf parameters will be compared
                smtInput.append("(define argcnt");
                smtInput.append(symName);
                smtInput.append("::nat)\n");
            }

            // Define for every function symbol with arity > 1 a status function
            for (final FunctionSymbol sym : symSet) {
                final int arity = sym.getArity();
                final String symName = symNameMap.get(sym);
                smtInput.append("(define stat");
                smtInput.append(symName);
                smtInput.append("::(-> nat nat))\n");
                for (int i = 0; i < arity; i++) {
                    // permutation constraints:
                    // statf(i) < n for all i < n
                    // or i < k for argument filtering
                    // where k is the number of arguments to be compared
                    smtInput.append("(assert (or (< (stat");
                    smtInput.append(symName);
                    smtInput.append(" ");
                    smtInput.append(i);
                    smtInput.append(") ");
                    smtInput.append(arity);
                    smtInput.append(") (< argcnt");
                    smtInput.append(symName);
                    smtInput.append(" ");
                    smtInput.append(i);
                    smtInput.append(")))\n");
                    for (int j = i + 1; j < arity; j++) {
                        // Every position is taken exactly one time
                        smtInput.append("(assert (/= (stat");
                        smtInput.append(symName);
                        smtInput.append(" ");
                        smtInput.append(i);
                        smtInput.append(") (stat");
                        smtInput.append(symName);
                        smtInput.append(" ");
                        smtInput.append(j);
                        smtInput.append(")))\n");
                    }
                }
                if (!KBOSMTSolver.this.status) {
                    if (KBOSMTSolver.this.afstype != AFSType.FULLAFS) {
                        // All arguments must be compared in strict ordering
                        for (int i = 0; i < arity; i++) {
                            smtInput.append("(assert (= (stat");
                            smtInput.append(symName);
                            smtInput.append(" ");
                            smtInput.append(i);
                            smtInput.append(") ");
                            smtInput.append(i);
                            smtInput.append("))\n");
                        }
                    } else {
                        // Strict ordering, but not every argument is compared
                        for (int i = 0; i < arity - 1; i++) {
                            smtInput.append("(assert (< (stat");
                            smtInput.append(symName);
                            smtInput.append(" ");
                            smtInput.append(i);
                            smtInput.append(") (stat");
                            smtInput.append(symName);
                            smtInput.append(" ");
                            smtInput.append(i + 1);
                            smtInput.append(")))\n");
                        }
                    }
                }
            }

            // AFS constraints go here...
            for (final FunctionSymbol sym : symSet) {
                final String symName = symNameMap.get(sym);
                // Collapsing function symbols get weight 0
                smtInput.append("(assert (=> (> afsflag");
                smtInput.append(symName);
                smtInput.append(" -1) (= wf");
                smtInput.append(symName);
                smtInput.append(" 0)))\n");
                final int arity = sym.getArity();
                for (int i = 0; i < arity; i++) {
                    smtInput.append("(assert (< (argcnt");
                    smtInput.append(symName);
                    smtInput.append(" ");
                    smtInput.append(i);
                    smtInput.append(") ");
                    smtInput.append(arity);
                    smtInput.append("))\n");
                }
            }
            switch (KBOSMTSolver.this.afstype) {
            case NOAFS:
                for (final FunctionSymbol sym : symSet) {
                    final String symName = symNameMap.get(sym);
                    smtInput.append("(assert (= afsflag");
                    smtInput.append(symName);
                    smtInput.append(" -1))\n");
                    final int arity = sym.getArity();
                    smtInput.append("(assert (= (argcnt");
                    smtInput.append(symName);
                    smtInput.append(" ");
                    smtInput.append(arity);
                    smtInput.append(")))\n");
                }
                break;
            case MONOTONEAFS:
                for (final FunctionSymbol sym : symSet) {
                    final int arity = sym.getArity();
                    final String symName = symNameMap.get(sym);
                    if (arity != 1) {
                        smtInput.append("(assert (= afsflag");
                        smtInput.append(symName);
                        smtInput.append(" -1))\n");
                    }
                    smtInput.append("(assert (= (argcnt");
                    smtInput.append(symName);
                    smtInput.append(" ");
                    smtInput.append(arity);
                    smtInput.append(")))\n");
                }
                break;
            }

        }

    }

}
