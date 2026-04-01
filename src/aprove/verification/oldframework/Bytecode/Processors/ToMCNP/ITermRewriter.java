package aprove.verification.oldframework.Bytecode.Processors.ToMCNP;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


/**
 *
 * Rewrites Integer Term to SMT Formulas.
 *
 * @author Matthias Hoelzel
 *
 */
class ITermRewriter {
    /**
     * Cache.
     * Setting cache to null will disable cache
     */
    private final LinkedHashMap<TRSTerm, Pair<SMTLIBIntVariable, Formula<SMTLIBTheoryAtom>>> cache;

    /**
     * Produces SMT-formulas.
     */
    private final FormulaFactory<SMTLIBTheoryAtom> factory;

    /**
     * The holy predefined map
     */
    private final IDPPredefinedMap predefinedMap;

    /**
     * Constructor
     */
    public ITermRewriter(final FormulaFactory<SMTLIBTheoryAtom> formulaFactory) {
        super();

        this.cache = new LinkedHashMap<TRSTerm, Pair<SMTLIBIntVariable,Formula<SMTLIBTheoryAtom>>>();
        this.factory = formulaFactory;
        this.predefinedMap = IDPPredefinedMap.DEFAULT_MAP;
    }

    /**
     * Rewrite an integer term to an SMTFormula.
     *
     * @param t a term.
     * @param formulas list to add formula.
     * @return a pair: the variable storing the result
     */
    public SMTLIBIntVariable rewrite(final TRSTerm t, final List<Formula<SMTLIBTheoryAtom>> formulas) {
        final Pair<SMTLIBIntVariable, Formula<SMTLIBTheoryAtom>> result = this.rewrite(t);
        formulas.add(result.y);
        return result.x;
    }

    /**
     * Rewrite an integer term to an SMTFormula.
     *
     * @param t a term.
     * @return a pair: the variable storing the result + the corresponding formula.
     */
    public Pair<SMTLIBIntVariable, Formula<SMTLIBTheoryAtom>> rewrite(final TRSTerm t) {
        final Pair<SMTLIBIntVariable, Formula<SMTLIBTheoryAtom>> result;

        if (this.cache != null && this.cache.containsKey(t)) {
            result = this.cache.get(t);
        } else {
            final List<SMTLIBTheoryAtom> atoms = new LinkedList<SMTLIBTheoryAtom>();
            final List<Formula<SMTLIBTheoryAtom>> formulas = new LinkedList<Formula<SMTLIBTheoryAtom>>();

            final SMTLIBIntVariable var = this.rewriteITerm(t, atoms, formulas);

            final Formula<SMTLIBTheoryAtom> formula = this.factory.buildAnd(
                    this.factory.buildAnd(this.factory.buildTheoryAtoms(atoms)),
                    this.factory.buildAnd(formulas));
            result = new Pair<SMTLIBIntVariable, Formula<SMTLIBTheoryAtom>>(var, formula);

            if (this.cache != null) {
                this.cache.put(t, result);
            }
        }


        return result;
    }

    private SMTLIBIntVariable rewriteITerm(final TRSTerm t,
            final List<SMTLIBTheoryAtom> atoms,
            final List<Formula<SMTLIBTheoryAtom>> formulae) {
        // TODO: Check this!
        if (t.isVariable()) {
            final TRSVariable x = (TRSVariable) t;
            final SMTLIBIntVariable varX = SMTLIBIntVariable
                    .create(x.getName());
            return varX;
        } else {
            final SMTLIBIntVariable result = SMTLIBIntVariable.create(
                    IDPToMCSUtility.getFreshName());
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            final FunctionSymbol sym = func.getRootSymbol();
            final String symName = sym.getName();

            if ("PMAX".equals(symName)) {
                // For integers a, x_0, ... x_n (n > 0, because x_0 := 0) we have:
                // a = max(x_0, ... , x_n) iff
                // (conjunction over i (a >= x_i)) and (disjunction over j (a <= x_j))

                Formula<SMTLIBTheoryAtom> forceMaximum = null;
                final LinkedList<TRSTerm> args = new LinkedList<TRSTerm>(func.getArguments());
                args.add(IDPToMCSUtility.createIntegerTerm(0));
                for (final TRSTerm arg : args) {
                    final SMTLIBIntVariable current = this.rewriteITerm(arg, atoms, formulae);
                    final SMTLIBIntCMP cmp = SMTLIBIntGE.create(result, current);
                    // Auf zum Atom!
                    atoms.add(cmp);

                    final SMTLIBIntCMP cmp2 = SMTLIBIntGE.create(current,
                            result);
                    if (forceMaximum == null) {
                        forceMaximum = this.factory.buildTheoryAtom(cmp2);
                    } else {
                        forceMaximum = this.factory.buildOr(forceMaximum,
                                this.factory.buildTheoryAtom(cmp2));
                    }
                }
                assert forceMaximum != null;
                formulae.add(forceMaximum);
            } else if (this.predefinedMap.isAdd(sym)) {
                // Addition should have arity 2.
                assert sym.getArity() == 2;
                final ArrayList<SMTLIBIntValue> argList = new ArrayList<SMTLIBIntValue>(2);
                for (final TRSTerm arg : func.getArguments()) {
                    argList.add(this.rewriteITerm(arg, atoms, formulae));
                }
                final SMTLIBTheoryAtom atom = SMTLIBIntEquals.create(result,
                        SMTLIBIntPlus.create(argList));
                // Auf zum ATEM! ;)
                atoms.add(atom);
            } else if (this.predefinedMap.isSub(sym)) {
                // Subtraction should have arity 2.
                assert sym.getArity() == 2;
                final ArrayList<SMTLIBIntValue> argList = new ArrayList<SMTLIBIntValue>(2);
                for (final TRSTerm arg : func.getArguments()) {
                    argList.add(this.rewriteITerm(arg, atoms, formulae));
                }
                final SMTLIBTheoryAtom atom = SMTLIBIntEquals.create(result,
                        SMTLIBIntMinus.create(argList));
                atoms.add(atom);
            } else if (this.predefinedMap.isMul(sym)) {

                // Multiplication should have arity 2.
                assert sym.getArity() == 2;
                final SMTLIBIntVariable x = this.rewriteITerm(func
                        .getArgument(0), atoms, formulae);
                final SMTLIBIntVariable y = this.rewriteITerm(func
                        .getArgument(1), atoms, formulae);
                final SMTLIBIntVariable z = result;

                final ArrayList<SMTLIBIntValue> argList = new ArrayList<SMTLIBIntValue>();
                argList.add(x);
                argList.add(y);

                final SMTLIBTheoryAtom atom = SMTLIBIntEquals.create(z,
                        SMTLIBIntMult.create(argList));
                atoms.add(atom);

                // TODO: Is the SMT-Solver clever enough to generate the
                // following implications?
                /*
                 * SMTLIBIntValue zero =
                 * SMTLIBIntConstant.create(BigInteger.valueOf(0));
                 * SMTLIBIntValue one =
                 * SMTLIBIntConstant.create(BigInteger.valueOf(1));
                 *
                 * ArrayList<Formula<SMTLIBTheoryAtom>> argList2 = new
                 * ArrayList<Formula<SMTLIBTheoryAtom>>();
                 * argList2.add(this.factory.buildAnd(
                 * this.factory.buildTheoryAtom(SMTLIBIntGT.create(x, zero)),
                 * this.factory.buildTheoryAtom(SMTLIBIntGT.create(y, zero))));
                 * argList2.add(this.factory.buildAnd(
                 * this.factory.buildTheoryAtom(SMTLIBIntLT.create(x, zero)),
                 * this.factory.buildTheoryAtom(SMTLIBIntLT.create(y, zero))));
                 * Formula<SMTLIBTheoryAtom> formula1 =
                 * this.factory.buildImplication(
                 * this.factory.buildOr(argList2),
                 * this.factory.buildTheoryAtom(SMTLIBIntGT.create(z, zero)));
                 * formulae.add(formula1);
                 */
            } else if (this.predefinedMap.isInt(sym, DomainFactory.INTEGERS)) {
                final BigInteger i = this.predefinedMap.getInt(sym,
                        DomainFactory.INTEGERS);
                final SMTLIBIntValue val = SMTLIBIntConstant.create(i);
                final SMTLIBTheoryAtom atom = SMTLIBIntEquals.create(result,
                        val);
                atoms.add(atom);
            } else {
                assert false : "Unexcepted symbol: " + symName;
            }
            return result;
        }
    }
}
