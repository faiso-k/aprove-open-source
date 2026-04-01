package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.runtime.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Remove Redundant Rules Polo Processor. Given a CSR, tries to
 * orient all rules non-strictly and at least one of them strictly,
 * then removes the strictly oriented rules.
 *
 * Uses mu-monotonic polynomial orderings.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class CSRRRRPoloProcessor extends CSRProcessor {

    private final boolean autostrict; // true -> autostrict, false -> searchstrict
    private final POLOFactory factory;

    @ParamsViaArgumentObject
    public CSRRRRPoloProcessor (final Arguments arguments) {
        this.autostrict = arguments.autostrict;
        final POLOFactory.Arguments facArgs = new POLOFactory.Arguments();
        facArgs.degree = arguments.degree;
        facArgs.engine = arguments.engine;
        facArgs.maxSimpleDegree = arguments.maxSimpleDegree;
        facArgs.range = arguments.range;
        facArgs.satConverter = arguments.satConverter;
        facArgs.simplification = arguments.simplification;
        facArgs.simplifyAll = arguments.simplifyAll;
        facArgs.stripExponents = arguments.stripExponents;
        this.factory = new POLOFactory(facArgs);

    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.TRSProblem.Processors.QTRSProcessor#processQTRS(aprove.verification.dpframework.TRSProblem.QTRSProblem, aprove.strategies.Abortions.Abortion)
     */
    @Override
    protected Result processCSR(final CSRProblem csr, final Abortion aborter)
            throws AbortionException {
        Set<Rule> r, deletedRules, remainingRules;
        r = csr.getR();
        deletedRules = new LinkedHashSet<Rule>();
        remainingRules = new LinkedHashSet<Rule>();
        Order<TRSTerm> solvingOrder;
        Set<Constraint<TRSTerm>> constraints;
        constraints = Constraint.fromRules(r, OrderRelation.GE);
        Set<VarPolyConstraint> polyConstraints;
        final POLOSolver solver = this.factory.getSolver(constraints);
        solver.setAllowWeakMonotonicity(false);
        solver.setMu(csr.getReplacementMap());
        polyConstraints = solver.createPoloConstraints(aborter, constraints);

        if (this.autostrict) {
            solver.addASC(polyConstraints);
            solvingOrder = solver.solve(aborter, polyConstraints);
        }
        else { // searchstrict
            solvingOrder = solver.solve(aborter,
                    new HashSet<VarPolyConstraint>(0), polyConstraints);
        }

        if (solvingOrder == null) {
            return ResultFactory.unsuccessful();
        }
        for (final Rule rule : r) {
            if (! solvingOrder.inRelation(rule.getLeft(), rule.getRight())) {
                if (Globals.useAssertions) {
                    Constraint<TRSTerm> c;
                    c = Constraint.create(rule.getLeft(), rule.getRight(),
                            OrderRelation.GE);
                    assert(solvingOrder.solves(c));
                }
                remainingRules.add(rule);
            }
            else {
                deletedRules.add(rule);
            }
        }
        if (Globals.useAssertions) {
            assert (! deletedRules.isEmpty());
        }

        // take care of new subproblem and proof
        ImmutableSet<Rule> newSubProblemRules;
        newSubProblemRules = ImmutableCreator.create(remainingRules);
        final CSRProblem newCsr = csr.createSubProblem(newSubProblemRules);
        Proof proof;
        proof = new PoloCSRProof(csr, newCsr, deletedRules, (POLO) solvingOrder);
        final Result result = ResultFactory.proved(newCsr, this.computeImplication(csr), proof);
        return result;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.TRSProblem.Processors.QTRSProcessor#isQTRSApplicable(aprove.verification.dpframework.TRSProblem.QTRSProblem)
     */
    @Override
    public boolean isCSRApplicable(final CSRProblem csr) {
        if (Options.certifier.isCeta()) {
            return false;
        }
        return true;
    }


    /**
     * @param qtrs the QTRSProblem this processor is applied on
     * @return whether the application of this processor on qtrs
     *  is just sound or actually equivalent
     */
    private Implication computeImplication(final CSRProblem qtrs) {
        if (qtrs.getInnermost()) {
            // innermost: deleting a rule may make ->_R^i bigger
            // and lead to non-termination of the resulting problem
            // since we do not have any set Q for CSRProblems (yet);
            // consider reducing the innermost terminating system
            //  { f(a) -> f(a), a -> b }
            // to the innermost non-terminating system
            //  { f(a) -> f(a) }
            // using a_Pol = 1, b_Pol = 0, f_Pol = x_1
            return YNMImplication.SOUND;
        }
        else {
            return YNMImplication.EQUIVALENT;
        }
    }

    private static final class PoloCSRProof extends CSRProof {

        private final CSRProblem csr;
        private final CSRProblem newCsr;
        private final Set<Rule> deletedRules;
        private final POLO polo;

        private PoloCSRProof(
            final CSRProblem csr,
            final CSRProblem newCsr,
            final Set<Rule> deletedRules,
            final POLO polo)
        {
            this.csr = csr;
            this.newCsr = newCsr;
            this.deletedRules = deletedRules;
            this.polo = polo;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder result = new StringBuilder();
            result.append("The following rules can be removed because they are oriented strictly by a " + o.mu() + "-monotonic polynomial ordering:");
            result.append(o.linebreak());
            result.append(o.set(this.deletedRules, Export_Util.RULES));
            result.append("Used ordering:");
            result.append(o.linebreak());
            result.append(this.polo.export(o));
            result.append(o.newline());
            result.append(o.linebreak());
            return result.toString();
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            if (!this.isCPFCheckableProof(modus)) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
            return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.newCsr);
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return !modus.isPositive();
        }

    }

    public static class Arguments {
        public boolean autostrict = false;
        public int degree;
        public Engine engine;
        public int maxSimpleDegree;
        public int range;
        public DiophantineSATConverter satConverter;
        public SimplificationMode simplification;
        public boolean simplifyAll;
        public boolean stripExponents;
    }

}
