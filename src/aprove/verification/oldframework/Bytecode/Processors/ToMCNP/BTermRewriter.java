package aprove.verification.oldframework.Bytecode.Processors.ToMCNP;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;

/**
 *
 * Rewrites a term, yielding boolean values, to a SMT-formula.
 *
 * @author Matthias Hoelzel
 *
 */
class BTermRewriter {
    /**
     * Cache.
     * Setting cache to null will disable cache
     */
    private final LinkedHashMap<TRSFunctionApplication, Formula<SMTLIBTheoryAtom>> cache;

    /**
     * Produces SMT-formulas.
     */
    private final FormulaFactory<SMTLIBTheoryAtom> factory;

    /**
     * The holy predefined map
     */
    private final IDPPredefinedMap predefinedMap;

    /**
     * ITerm rewriter
     */
    private final ITermRewriter iRewriter;

    /**
     * Constructor
     */
    public BTermRewriter(final FormulaFactory<SMTLIBTheoryAtom> formulaFactory, final ITermRewriter rewriter) {
        super();

        this.cache = new LinkedHashMap<>();
        this.factory = formulaFactory;
        this.predefinedMap = IDPPredefinedMap.DEFAULT_MAP;
        this.iRewriter = rewriter;
    }

    public Formula<SMTLIBTheoryAtom> rewrite(final TRSFunctionApplication func) {
        if (this.cache.containsKey(func)) {
            return this.cache.get(func);
        } else {
            final Formula<SMTLIBTheoryAtom> result = this.rewriteBTerm(func);
            this.cache.put(func, result);
            return result;
        }
    }

    /**
     * Rewrite boolean term to formula.
     *
     * @param func
     *            FunctionApplication only using pre-defined function symbols
     *            generating boolean values as result.
     * @return SMT-Formula representing the input term.
     */
    private Formula<SMTLIBTheoryAtom> rewriteBTerm(final TRSFunctionApplication func) {
        // TODO: Check this!
        final FunctionSymbol sym = func.getRootSymbol();
        Formula<SMTLIBTheoryAtom> result = null;

        if (this.predefinedMap.isBooleanFalse(sym)) {
            result = this.factory.buildTheoryAtom(SMTLIBBoolFalse.create());
        } else if (this.predefinedMap.isBooleanTrue(sym)) {
            result = this.factory.buildTheoryAtom(SMTLIBBoolTrue.create());
        } else if (this.predefinedMap.isGe(sym) || this.predefinedMap.isGt(sym) || this.predefinedMap.isLe(sym)
            || this.predefinedMap.isLt(sym) || this.predefinedMap.isEq(sym) || this.predefinedMap.isNeq(sym)) {
            // TODO: I guess these operations are only defined for ITerms.
            final List<SMTLIBTheoryAtom> atoms = new LinkedList<>();
            final List<Formula<SMTLIBTheoryAtom>> formulae = new LinkedList<>();

            final SMTLIBIntVariable x = this.iRewriter.rewrite(func.getArgument(0), formulae);
            final SMTLIBIntVariable y = this.iRewriter.rewrite(func.getArgument(1), formulae);

            SMTLIBTheoryAtom preciousAtom = null;

            if (this.predefinedMap.isNeq(sym)) {
                preciousAtom = SMTLIBIntEquals.create(x, y);
                final Formula<SMTLIBTheoryAtom> formula =
                    this.factory.buildAnd(this.factory.buildAnd(this.factory.buildTheoryAtoms(atoms)),
                        this.factory.buildAnd(formulae));
                result =
                    this.factory.buildAnd(this.factory.buildNot(this.factory.buildTheoryAtom(preciousAtom)), formula);
            } else {
                if (this.predefinedMap.isGe(sym)) {
                    preciousAtom = SMTLIBIntGE.create(x, y);
                } else if (this.predefinedMap.isGt(sym)) {
                    preciousAtom = SMTLIBIntGT.create(x, y);
                } else if (this.predefinedMap.isLe(sym)) {
                    preciousAtom = SMTLIBIntLE.create(x, y);
                } else if (this.predefinedMap.isLt(sym)) {
                    preciousAtom = SMTLIBIntLT.create(x, y);
                } else if (this.predefinedMap.isEq(sym)) {
                    preciousAtom = SMTLIBIntEquals.create(x, y);
                }

                final Formula<SMTLIBTheoryAtom> formula =
                    this.factory.buildAnd(this.factory.buildAnd(this.factory.buildTheoryAtoms(atoms)),
                        this.factory.buildAnd(formulae));

                result = this.factory.buildAnd(this.factory.buildTheoryAtom(preciousAtom), formula);
            }
        } else if (this.predefinedMap.isLand(sym)) {
            assert sym.getArity() == 2;
            assert func.getArgument(0) instanceof TRSFunctionApplication;
            assert func.getArgument(1) instanceof TRSFunctionApplication;

            final Formula<SMTLIBTheoryAtom> x = this.rewriteBTerm((TRSFunctionApplication) func.getArgument(0));
            final Formula<SMTLIBTheoryAtom> y = this.rewriteBTerm((TRSFunctionApplication) func.getArgument(1));

            result = this.factory.buildAnd(x, y);
        } else if (this.predefinedMap.isLor(sym)) {
            assert sym.getArity() == 2;
            assert func.getArgument(0) instanceof TRSFunctionApplication;
            assert func.getArgument(1) instanceof TRSFunctionApplication;

            final Formula<SMTLIBTheoryAtom> x = this.rewriteBTerm((TRSFunctionApplication) func.getArgument(0));
            final Formula<SMTLIBTheoryAtom> y = this.rewriteBTerm((TRSFunctionApplication) func.getArgument(1));

            result = this.factory.buildOr(x, y);
        } else if (this.predefinedMap.isLnot(sym)) {
            assert sym.getArity() == 1;
            assert func.getArgument(0) instanceof TRSFunctionApplication;

            final Formula<SMTLIBTheoryAtom> form = this.rewriteBTerm(func);

            result = this.factory.buildNot(form);
        } else {
            assert false : "Unexpected symbol: " + sym;
        }

        return result;
    }
}
