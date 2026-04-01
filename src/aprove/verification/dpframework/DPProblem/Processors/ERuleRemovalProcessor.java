package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Rule Removal processor. Using a POLO, tries to orient all rules of P
 * and R non-strictly and at least one rule of P or R strictly, then
 * deletes the strictly oriented rules. (See Theorem 3.11 of EDP Framework.)
 *
 * @author stein
 * @version $Id$
 */
public class ERuleRemovalProcessor extends EAbstractStrictPoloEDPProblemProcessor {

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.ERuleRemovalProcessor");

    @ParamsViaArgumentObject
    public ERuleRemovalProcessor(Arguments arguments) {
        super(arguments);
    }


    @Override
    protected Result processEDPProblem(EDPProblem edp, Abortion aborter)
            throws AbortionException {


        ImmutableSet<Rule> r = edp.getR();
        ImmutableSet<Rule> p = edp.getP();
        ImmutableSet<Equation> esharp = edp.getESharp();
        ImmutableSet<Equation> e = edp.getE();
        Order<TRSTerm> solvingOrder;

        Set<Constraint<TRSTerm>> eSharpConstraints = Constraint.fromEquations(esharp);
        Set<Constraint<TRSTerm>> constraintsAll = new LinkedHashSet<Constraint<TRSTerm>>();
        constraintsAll.addAll(eSharpConstraints);
        constraintsAll.addAll(Constraint.fromEquations(e));

        POLOSolver solver;
        ERuleRemovalProcessor.log.log(Level.FINE, "Using mode: {0}\n", this.mode);
        Set<Constraint<TRSTerm>> constraintsGe;
        Set<VarPolyConstraint> poloConstraints;
        Set<SimplePolyConstraint> eqnsConstraints;

        switch (this.mode) {
        case AUTOSTRICT :
            constraintsGe = Constraint.fromRules(r, OrderRelation.GE);
            constraintsGe.addAll(Constraint.fromRules(p, OrderRelation.GE));
            constraintsAll.addAll(constraintsGe);
            solver = this.factory.getSolver(constraintsAll);
            solver.setAllowWeakMonotonicity(false);

            poloConstraints = solver.createPoloConstraints(aborter, constraintsGe);
            solver.addASC(poloConstraints);
            eqnsConstraints = this.getACPoloConstraints(e, solver);
            //Add esharp constraints
            poloConstraints.addAll(solver.createPoloConstraints(aborter, eSharpConstraints));

            solvingOrder = solver.solve(eqnsConstraints, aborter, poloConstraints);
            break;
        case ALLSTRICT :
            constraintsGe = Constraint.fromRules(r, OrderRelation.GR);
            constraintsGe.addAll(Constraint.fromRules(p, OrderRelation.GR));
            constraintsAll.addAll(constraintsGe);
            solver = this.factory.getSolver(constraintsAll);
            poloConstraints = solver.createPoloConstraints(aborter, constraintsGe);
            eqnsConstraints = this.getACPoloConstraints(e, solver);
            //Add esharp constraints
            poloConstraints.addAll(solver.createPoloConstraints(aborter, eSharpConstraints));

            solvingOrder = solver.solve(eqnsConstraints, aborter, poloConstraints);
            break;
        case SEARCHSTRICT :
            constraintsGe = Constraint.fromRules(r, OrderRelation.GE);
            constraintsGe.addAll(Constraint.fromRules(p, OrderRelation.GE));
            constraintsAll.addAll(constraintsGe);
            solver = this.factory.getSolver(constraintsAll);
            poloConstraints = solver.createPoloConstraints(aborter, constraintsGe);
            eqnsConstraints = this.getACPoloConstraints(e, solver);

            solvingOrder = solver.solve(eqnsConstraints, solver.createPoloConstraints(aborter, eSharpConstraints),  poloConstraints, aborter);
            break;
        default:
            return ResultFactory.notApplicable();
        }

        return this.processEDPProblem(solvingOrder, edp, aborter);
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

    /**
     * Checks whether some rules in R or P of edp are oriented strictly
     * by solvingOrder, removes them and generates an according proof.
     *
     * Requires that solvingOrder orients all rules of P and R in edp at least
     * non-strictly.
     *
     * @param solvingOrder the order which is supposed to orient all rules in
     *  P united with R non-strictly
     * @param edp the EDPProblem to simplify
     * @param aborter
     * @return the corresponding result
     */
    protected Result processEDPProblem(Order<TRSTerm> solvingOrder, EDPProblem edp,
                Abortion aborter) throws AbortionException {
        if (solvingOrder == null) {
            return ResultFactory.unsuccessful();
        }

        ImmutableSet<Rule> p, r;
        p = edp.getP();
        r = edp.getR();

        // check which elements of P or R have been oriented strictly
        Set<Rule> newPRules, deletedPRules, newRRules, deletedRRules;
        newPRules = new LinkedHashSet<Rule>();
        deletedPRules = new LinkedHashSet<Rule>();
        newRRules = new LinkedHashSet<Rule>();
        deletedRRules = new LinkedHashSet<Rule>();
        for (Rule rule : p) {
            // only add non-strictly oriented rules
            if (! solvingOrder.inRelation(rule.getLeft(), rule.getRight())) {
                if (Globals.useAssertions) {
                    Constraint<TRSTerm> constraint;
                    constraint = Constraint.create(rule.getLeft(),
                            rule.getRight(), OrderRelation.GE);
                    assert (solvingOrder.solves(constraint));
                }
                newPRules.add(rule);
            }
            else {
                deletedPRules.add(rule);
            }

        }
        for (Rule rule : r) {
            // only add non-strictly oriented rules
            if (! solvingOrder.inRelation(rule.getLeft(), rule.getRight())) {
                if (Globals.useAssertions) {
                    Constraint<TRSTerm> constraint;
                    constraint = Constraint.create(rule.getLeft(),
                            rule.getRight(), OrderRelation.GE);
                    assert (solvingOrder.solves(constraint));
                }
                newRRules.add(rule);
            }
            else {
                deletedRRules.add(rule);
            }

        }
        for (Equation eq : edp.getE()) {
           if (Globals.useAssertions) {
                Constraint<TRSTerm> constraint;
                constraint = Constraint.create(eq.getLeft(),
                        eq.getRight(), OrderRelation.EQ);
                assert (solvingOrder.solves(constraint));
            }
        }
        for (Equation eq : edp.getESharp()) {
            if (Globals.useAssertions) {
                 Constraint<TRSTerm> constraint;
                 constraint = Constraint.create(eq.getLeft(),
                         eq.getRight(), OrderRelation.EQ);
                 assert (solvingOrder.solves(constraint));
             }
        }


        if (Globals.useAssertions) {
            assert (! (deletedPRules.isEmpty()
                    && deletedRRules.isEmpty()));
        }

        // build smaller subproblem and the proof
        // different cases to be able to reuse some computed results of the current edp problem
        EDPProblem newEdp;
        if (deletedRRules.isEmpty()) {
            newEdp = edp.getSubProblemWithSmallerP(ImmutableCreator.create(newPRules));
        } else if (deletedPRules.isEmpty()) {
            newEdp = edp.getSubProblemWithSmallerR(ImmutableCreator.create(newRRules));
        } else {
            newEdp = edp.getSubProblemWithSmallerPandR(ImmutableCreator.create(newPRules), ImmutableCreator.create(newRRules));
        }
        POLO polo = (POLO) solvingOrder;
        Proof proof = new ERuleRemovalProof(deletedRRules, deletedPRules, polo, newEdp, edp);
        Result result = ResultFactory.proved(newEdp, YNMImplication.EQUIVALENT, proof);

        return result;
    }

    @Override
    public boolean isEDPApplicable(EDPProblem edp) {
        return true;
    }


    private static final class ERuleRemovalProof extends EDPProof {

        private EDPProblem edp;
        private Set<Rule> orientedRRules;
        private Set<Rule> orientedPRules;
        private POLO polo;
        private EDPProblem oldEdp;

        private ERuleRemovalProof (Set<Rule> orientedRRules, Set<Rule> orientedPRules,
                POLO polo, EDPProblem resultingEdp, EDPProblem origEdp) {
            if (Globals.useAssertions) {
                assert(! (orientedPRules.isEmpty()
                        && orientedRRules.isEmpty()));
            }
            this.orientedRRules = orientedRRules;
            this.orientedPRules = orientedPRules;
            this.polo = polo;
            this.edp = resultingEdp;
            this.oldEdp = origEdp;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            if (true) { // TODO deal with level
                result.append("By using the rule removal processor "+o.cite(Citation.DA_STEIN)+" with the following polynomial ordering "+o.cite(Citation.POLO)+", at least one Dependency Pair or term rewrite system rule of this EDP problem can be strictly oriented.\n");
                result.append(o.cond_linebreak());
                if (! this.orientedPRules.isEmpty()) {
                    result.append("Strictly oriented dependency pairs:\n");
                    result.append(o.set(this.orientedPRules, Export_Util.RULES));
                }
                result.append(o.cond_linebreak());
                if (! this.orientedRRules.isEmpty()) {
                    result.append("Strictly oriented rules of the TRS R:\n");
                    result.append(o.set(this.orientedRRules, Export_Util.RULES));
                }
                result.append(o.cond_linebreak());
                result.append("Used ordering: POLO with ");
                result.append(this.polo.export(o));
                result.append(o.cond_linebreak());
            }
            return result.toString();
        }
        
        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (!this.isCPFCheckableProof(modus)) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
            Set<Rule> usable = new LinkedHashSet<>(this.oldEdp.getR());
            for (Equation e : this.oldEdp.getE()) {
        		usable.add(Rule.create((TRSFunctionApplication) e.getLeft(), e.getRight())); 
            }
            return CPFTag.AC_DP_PROOF.create(doc,
                    CPFTag.AC_MONO_RED_PAIR_PROC.create(doc,
                    this.polo.toCPF(doc, xmlMetaData),
                    CPFTag.dps(doc, xmlMetaData, this.orientedPRules),
                    CPFTag.trs(doc, xmlMetaData, this.orientedRRules),
                    CPFTag.USABLE_RULES.create(doc, CPFTag.rules(doc, xmlMetaData, usable)),
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
}
