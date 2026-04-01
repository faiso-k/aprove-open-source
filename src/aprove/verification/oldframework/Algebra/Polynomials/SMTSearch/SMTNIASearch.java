package aprove.verification.oldframework.Algebra.Polynomials.SMTSearch;

import java.math.*;
import java.util.*;

import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Search for POLOs by directly using SMT NIA applying an SMT solver like z3.
 * Can also be used for solving a Diophantine Formula given a PoloSmtConverter.
 *
 * @author Christian Kuknat
 */
public class SMTNIASearch extends AbstractSearchAlgorithm {

    public SMTNIASearch(final DefaultValueMap<String, BigInteger> ranges) {
        super(ranges);
    }

    @Override
    public Map<String, BigInteger> search(final Set<SimplePolyConstraint> constraints,
        final Set<SimplePolyConstraint> searchStrictConstraints,
        final SimplePolynomial maxMe,
        final Abortion aborter) throws AbortionException {
        assert (constraints != null);
        assert (searchStrictConstraints != null);

        final FormulaFactory<SMTLIBTheoryAtom> factory = new AtomCachingFactory<>();
        final Set<String> variables = new LinkedHashSet<>();
        final List<Formula<SMTLIBTheoryAtom>> spcList = new LinkedList<>();
        for (final SimplePolyConstraint spc : constraints) {
            spcList.add(factory.buildTheoryAtom(spc.toSMTLIB()));
            variables.addAll(spc.getIndefinites());
        }
        if (!searchStrictConstraints.isEmpty()) {
            final List<Formula<SMTLIBTheoryAtom>> notToBeBuilt = new LinkedList<>();
            for (final SimplePolyConstraint strictSpc : searchStrictConstraints) {
                // the strict spcs with constraint GE
                final SMTLIBTheoryAtom smtStrictSpc = strictSpc.toSMTLIB();
                spcList.add(factory.buildTheoryAtom(smtStrictSpc));
                variables.addAll(strictSpc.getIndefinites());
                // the strict spcs with constraint EQ for negating
                final SimplePolyConstraint equalStrict =
                    new SimplePolyConstraint(strictSpc.getPolynomial(), ConstraintType.EQ);
                final SMTLIBTheoryAtom equalStrictSMT = equalStrict.toSMTLIB();
                notToBeBuilt.add(factory.buildTheoryAtom(equalStrictSMT));
            }
            // conjunction of strict constraints with type EQ
            final Formula<SMTLIBTheoryAtom> andOfTheEquals = factory.buildAnd(notToBeBuilt);
            // and the negation of the above mentioned
            final Formula<SMTLIBTheoryAtom> notIsBuild = factory.buildNot(andOfTheEquals);
            spcList.add(notIsBuild);
        }

        final SMTLIBIntConstant zero = SMTLIBIntConstant.create(BigInteger.ZERO);
        for (final String var : variables) {
            // var >= 0
            final SMTLIBIntVariable smtVar = SMTLIBIntVariable.create(var);
            final SMTLIBIntGE lowerConstraint = SMTLIBIntGE.create(smtVar, zero);
            spcList.add(factory.buildTheoryAtom(lowerConstraint));

            // var <= range
            final BigInteger range = this.ranges.get(var);
            if (range.compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) < 0) {
                final SMTLIBIntConstant smtRange = SMTLIBIntConstant.create(range);
                final SMTLIBIntGE upperConstraitn = SMTLIBIntGE.create(smtRange, smtVar);
                spcList.add(factory.buildTheoryAtom(upperConstraitn));
            }
        }
        final Formula<SMTLIBTheoryAtom> smtFormula = factory.buildAnd(spcList);

        Map<String, BigInteger> solution = null;
        final List<Formula<SMTLIBTheoryAtom>> smtFormulaAsSingletonList = Collections.singletonList(smtFormula);
        final SMTEngine smtEngine = new SMTLIBEngine();
        Pair<YNM, Map<String, String>> r;
        try {
            r = smtEngine.solve(smtFormulaAsSingletonList, SMTLogic.QF_NIA, aborter);
        } catch (final WrongLogicException e) {
            // we do not care
            r = new Pair<>(YNM.MAYBE, null);
        }
        if (r.x == YNM.YES) {
            solution = new LinkedHashMap<>();
            for (final Map.Entry<String, String> assignment : r.y.entrySet()) {
                final BigInteger value = new BigInteger(assignment.getValue());
                solution.put(assignment.getKey(), value);
            }
        }
        return solution;
    }

    @Override
    public Map<String, BigInteger> search(final Set<SimplePolyConstraint> constraints,
        final Set<SimplePolyConstraint> searchStrictConstraints,
        final Abortion aborter) throws AbortionException {
        return this.search(constraints, searchStrictConstraints, null, aborter);
    }

    @Override
    public Map<String, BigInteger> search(final Formula<Diophantine> f, final Abortion aborter)
            throws AbortionException {
        final FormulaToSPCsVisitor formulaToSPCs = new FormulaToSPCsVisitor();
        f.apply(formulaToSPCs);
        final Pair<Set<SimplePolyConstraint>, Set<SimplePolyConstraint>> spcs = formulaToSPCs.getPair();
        return this.search(spcs.x, spcs.y, aborter);
    }

}
