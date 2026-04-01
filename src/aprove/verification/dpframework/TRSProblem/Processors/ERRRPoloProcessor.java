package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
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
 * Remove Redundant Rules Polo Processor. Given a ETRS, tries to
 * orient all rules non-strictly and at least one of them strictly,
 * then removes the strictly oriented rules.
 *
 * @author stein
 * @version $Id$
 */
public class ERRRPoloProcessor extends ETRSProcessor {

    private final boolean autostrict; // true -> autostrict, false -> searchstrict
    private final POLOFactory factory;

    @ParamsViaArgumentObject
    public ERRRPoloProcessor (Arguments arguments) {
        this.autostrict = arguments.autostrict;

        POLOFactory.Arguments facArgs = new POLOFactory.Arguments();
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

    @Override
    protected Result processETRS(ETRSProblem ETRS, Abortion aborter)
            throws AbortionException {
        Set<Rule> r, deletedRules, remainingRules;
        ImmutableSet<Equation> e;
        r = ETRS.getR();
        e = ETRS.getE();

        deletedRules = new LinkedHashSet<Rule>();
        remainingRules = new LinkedHashSet<Rule>();
        Order<TRSTerm> solvingOrder;
        Set<Constraint<TRSTerm>> constraintsAll;
        Set<Constraint<TRSTerm>> constraints;
        constraints = Constraint.fromRules(r, OrderRelation.GE);
        constraintsAll = Constraint.fromEquations(e);
        constraintsAll.addAll(constraints);

        Set<VarPolyConstraint> polyConstraints;

        POLOSolver solver = this.factory.getSolver(constraintsAll);
        polyConstraints = solver.createPoloConstraints(aborter, constraints);
        Set<SimplePolyConstraint> eqnsConstraints;
        eqnsConstraints = this.getACPoloConstraints(e, solver);

        if (this.autostrict) {
            solver.addASC(polyConstraints);
            solvingOrder = solver.solve(eqnsConstraints, aborter, polyConstraints);
        }
        else { // searchstrict
            Set<VarPolyConstraint>emptyConstraints = new HashSet<VarPolyConstraint>();
            solvingOrder = solver.solve( eqnsConstraints, emptyConstraints,
                    polyConstraints, aborter);
        }

        if (solvingOrder == null) {
            return ResultFactory.unsuccessful();
        }
        for (Rule rule : r) {
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
        ETRSProblem newETRS;
        newETRS = ETRS.createSubProblemWithSmallerR(newSubProblemRules);
        Proof proof;
        proof = new RRRPoloETRSProof(ETRS, deletedRules, (POLO) solvingOrder);
        Result result = ResultFactory.proved(newETRS, this.computeImplication(ETRS), proof);
        return result;
    }


    private Set<SimplePolyConstraint> getACPoloConstraints(ImmutableSet<Equation> eqns, POLOSolver solver) {
        Set<SimplePolyConstraint> ret = new LinkedHashSet<SimplePolyConstraint>();
        // Add ACPolo Conditions for usable equations
        for(Equation e : eqns) {
            if(e.checkAEquation()) {
                ret.addAll(solver.getInterpretation().getACPolyConstraints(e.getFunctionSymbols(),0));
            }
            else if(e.checkCEquation()) {
                ret.addAll(solver.getInterpretation().getCPolyConstraints(e.getFunctionSymbols()));
            }
            else {
                if(Globals.useAssertions) {
                    assert false;
                }
            }
        }
        return ret;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.TRSProblem.Processors.ETRSProcessor#isETRSApplicable(aprove.verification.dpframework.TRSProblem.ETRSProblem)
     */
    @Override
    public boolean isETRSApplicable(ETRSProblem ETRS) {
        return true;
    }


    /**
     * @param ETRS the ETRSProblem this processor is applied on
     * @return whether the application of this processor on ETRS
     *  is just sound or actually equivalent
     */
    private Implication computeImplication(ETRSProblem ETRS) {
        return YNMImplication.EQUIVALENT;
    }

    private static final class RRRPoloETRSProof extends ETRSProof {

        private ETRSProblem ETRS;
        private Set<Rule> deletedRules;
        private POLO polo;

        private RRRPoloETRSProof(ETRSProblem ETRS, Set<Rule> deletedRules, POLO polo) {
            this.ETRS = ETRS;
            this.deletedRules = deletedRules;
            this.polo = polo;
        }


        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            result.append("The following E TRS is given: ");
            result.append(this.ETRS.export(o));
            result.append("The following rules can be removed by the rule removal processor "+o.cite(Citation.LPAR04)+ " because they are oriented strictly by a polynomial ordering:");
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
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (!this.isCPFCheckableProof(modus)) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
            return CPFTag.AC_TERMINATION_PROOF.create(doc,
                    CPFTag.AC_RULE_REMOVAL.create(doc,
                    this.polo.toCPF(doc, xmlMetaData),
                    CPFTag.trs(doc, xmlMetaData, this.deletedRules),
                    childrenProofs[0]));
        }

        @Override
        public String getNonCPFExportableReason(CPFModus modus) {
            return super.getNonCPFExportableReason(modus);
        }


        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return modus.isPositive();
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
