package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Usable Rules Reduction Pair Processor (Thm 4.30, EDP Framework).
 * Using a polynomial ordering, trims the TRS R to just the usable rules of P,
 * the equations of E to the usable equations
 * and further removes all rules from R and P which contain non-usable symbols
 * of P, where the usable rules of P and P itself
 * have to be orientable non-strictly. If some rules are oriented strictly,
 * they are removed as well.
 *
 * @author stein
 * @version $Id$
 */
public class EUsableRulesReductionPairsProcessor extends EAbstractPoloEDPProblemProcessor {

    private static Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.EUsableRulesReductionPairsProcessor");

    @ParamsViaArgumentObject
    public EUsableRulesReductionPairsProcessor(Arguments arguments) {
        super(arguments);
    }

    @Override
    protected Result processEDPProblem(EDPProblem origedp, Abortion aborter)
            throws AbortionException {
        if (EUsableRulesReductionPairsProcessor.log.isLoggable(Level.FINE)) {
            EUsableRulesReductionPairsProcessor.log.log(Level.FINE, "Applying UsableRulesReductionPairsProcessor\n");
        }

        EDPProblem edp = origedp;
        origedp = null;

        ImmutableSet<Rule> usableRules;
        ImmutableSet<Equation> usableEquations;
        boolean useImproved = false;
        //take improved usable rules and equations in C case
        if(edp.getRwithE().checkC()) {
            useImproved = true;
            ECUsableRules U = new ECUsableRules(edp.getRwithE());
            usableRules = U.getUsableRules(edp.getP(),edp.getESharp());
            usableEquations = U.getUsableEquations(edp.getP(),edp.getESharp());
        }
        else {
            usableRules = edp.getUsableRules();
            usableEquations = edp.getUsableEquations();
        }



        ImmutableSet<Rule> p = edp.getP();
        ImmutableSet<Equation> esharp = edp.getESharp();
        Order<TRSTerm> solvingOrder;
        Set<Constraint<TRSTerm>> constraintsGe;
        constraintsGe = Constraint.fromRules(usableRules, OrderRelation.GE);
        constraintsGe.addAll(Constraint.fromRules(p, OrderRelation.GE));

        Set<Constraint<TRSTerm>> eSharpConstraints = Constraint.fromEquations(esharp);
        Set<Constraint<TRSTerm>> constraintsAll = new LinkedHashSet<Constraint<TRSTerm>>();
        constraintsAll.addAll(eSharpConstraints);
        constraintsAll.addAll(Constraint.fromEquations(usableEquations));
        constraintsAll.addAll(constraintsGe);



        // strong monotonicity is required here (as set by default)
        POLOSolver solver = this.factory.getSolver(constraintsAll);
        solver.setAllowWeakMonotonicity(false);

        Set<VarPolyConstraint> poloConstraints = solver.createPoloConstraints(aborter, constraintsGe);
        //Add esharp constraints
        poloConstraints.addAll(solver.createPoloConstraints(aborter, eSharpConstraints));
        Set<SimplePolyConstraint> eqnsConstraints = new LinkedHashSet<SimplePolyConstraint>();

        //Add ACPolo Conditions for usable equations
        for(Equation eq : usableEquations) {
            if(eq.checkAEquation()) {
                eqnsConstraints.addAll(solver.getInterpretation().getACPolyConstraints(eq.getFunctionSymbols(),0));
            }
            else if(eq.checkCEquation()) {
                eqnsConstraints.addAll(solver.getInterpretation().getCPolyConstraints(eq.getFunctionSymbols()));
            }
            else {
                if(Globals.useAssertions) {
                    assert false;
                }
            }
        }

        solvingOrder = solver.solve(eqnsConstraints, aborter, poloConstraints);
        if (solvingOrder == null) {
            return ResultFactory.unsuccessful();
        }

        if (Globals.useAssertions) {
            for (Constraint<TRSTerm> c : constraintsAll) {
                assert (solvingOrder.solves(c));
            }
        }

        Set<FunctionSymbol> usableSyms = EUsableRulesReductionPairsProcessor.computeUsableSignature(edp);


        Set<Rule> newP = new LinkedHashSet<>();
        Set<Rule> newR = new LinkedHashSet<>();
        Set<Rule> deletedP = new LinkedHashSet<>(p);
        Set<Rule> deletedR = new LinkedHashSet<>(edp.getR());
        Set<Equation> deletedE = Options.certifier.isCeta() ? new HashSet<>(0) : new LinkedHashSet<>(edp.getE());
        // check whether we have happened to orient some rules strictly
        // such that we can delete them (thereby simulating a call to the
        // RuleRemovalProcessor, which would yield a significant overhead)
        for (Rule rule : p) {
            if (!(EUsableRulesReductionPairsProcessor.nonUsableSymbolInLhs(rule, usableSyms) || solvingOrder.inRelation(rule.getLeft(), rule.getRight()))) {
                newP.add(rule);
                deletedP.remove(rule);
            }
        }
        for (Rule rule : usableRules) {
            if (!(EUsableRulesReductionPairsProcessor.nonUsableSymbolInLhs(rule, usableSyms) || solvingOrder.inRelation(rule.getLeft(), rule.getRight()))) {
                newR.add(rule);
                deletedR.remove(rule);
            }
        }
        for (Equation eq : usableEquations) {
            if(deletedE.contains(eq)) {
                deletedE.remove(eq);
            }
        }

        // build smaller subproblem and proof
        EDPProblem newEdp;
        if (deletedP.isEmpty()) {
            // we only changed the TRS R, but not P
            if (deletedR.isEmpty()) {
                if(deletedE.isEmpty()) {
                    if (Globals.useAssertions) {
                        assert false;
                    }
                    newEdp = edp;
                }
                else {
                    newEdp = edp.getSubProblemWithSmallerE(ImmutableCreator.create(usableEquations));
                }
            } else {
                if(Options.certifier.isCpf() || deletedE.isEmpty()) {
                    newEdp = edp.getSubProblemWithSmallerR(ImmutableCreator.create(newR));
                }
                else {
                    newEdp = edp.getSubProblemWithSmallerRandE(ImmutableCreator.create(newR), ImmutableCreator.create(usableEquations));
                }
            }
        } else {
            if (deletedR.isEmpty()) {
                if(deletedE.isEmpty()) {
                    newEdp = edp.getSubProblemWithSmallerP(ImmutableCreator.create(newP));
                }
                else {
                    newEdp = edp.getSubProblemWithSmallerPandE(ImmutableCreator.create(newP), ImmutableCreator.create(usableEquations));
                }
            } else {
                if(deletedE.isEmpty()) {
                    newEdp = edp.getSubProblemWithSmallerPandR(ImmutableCreator.create(newP), ImmutableCreator.create(newR));
                }
                else {
                    newEdp = edp.getSubProblemWithSmallerPandRandE(ImmutableCreator.create(newP),ImmutableCreator.create(newR), ImmutableCreator.create(usableEquations));
                }
            }
        }
        POLO polo = (POLO) solvingOrder;
        Proof proof = new EUsableRulesReductionPairsProof(deletedR, deletedP, deletedE, polo, origedp, useImproved, usableRules, usableEquations);
        Result result = ResultFactory.proved(newEdp, YNMImplication.EQUIVALENT, proof);

        return result;
    }

    private static Set<FunctionSymbol> computeUsableSignature(EDPProblem edp) {
        Set<FunctionSymbol> usableSyms = new HashSet<FunctionSymbol>();
        for (Rule rule : edp.getUsableRules()) {
            rule.getRight().collectFunctionSymbols(usableSyms);
        }
        for (Rule rule : edp.getP()) {
            rule.getRight().collectFunctionSymbols(usableSyms);
        }
        for (Equation eq : edp.getUsableEquations()) {
            eq.getRight().collectFunctionSymbols(usableSyms);
            eq.getLeft().collectFunctionSymbols(usableSyms);
        }
        return usableSyms;
    }

    private static boolean nonUsableSymbolInLhs(Rule rule, Set<FunctionSymbol> usableSyms) {
        for (FunctionSymbol f : rule.getLeft().getFunctionSymbols()) {
            if (!usableSyms.contains(f)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean isEDPApplicable(EDPProblem edp) {
        return EUsableRulesReductionPairsProcessor.checkApplication(edp);
    }

    public static boolean checkApplication(EDPProblem edp) {
        if (!edp.getMinimal()) {
            return false;
        }

        Set<Rule> usableR = edp.getUsableRules();
        Set<Equation> usableE = edp.getUsableEquations();

        // check whether we can gain something
        if (usableR.size() < edp.getR().size()) {
            return true;
        }
        if (!Options.certifier.isCeta() && usableE.size() < edp.getE().size()) {
            return true;
        }
        // okay we cannot remove non-usable rules or equations

        // usable symbols deletion
        Set<FunctionSymbol> usableSyms = EUsableRulesReductionPairsProcessor.computeUsableSignature(edp);
        for (FunctionSymbol f : edp.getSignatureOfRandP()) {
            if (!usableSyms.contains(f)) {
                return true; // we can delete a rule, as the non-usable symbol f can only occur in a lhs of a rule
            }
        }

        // okay, we cannot remove rules which have non-usable symbols on their lhs.

        return false;
    }

    private static final class EUsableRulesReductionPairsProof extends EDPProof {
        private Set<Rule> removedPRules;
        private Set<Rule> removedRRules;
        private Set<Equation> removedEqns;
        private Set<Rule> usableRules;
        private Set<Equation> usableEqs;
        private POLO polo;
        private boolean usedImproved;

        private EUsableRulesReductionPairsProof (Set<Rule> removedRRules, Set<Rule> removedPRules,
                Set<Equation> removedEqns, POLO polo, EDPProblem originalEDP, boolean usedImproved,
                Set<Rule> usableRules, Set<Equation> usableEqs) {
            this.removedPRules = removedPRules;
            this.removedRRules = removedRRules;
            this.removedEqns = removedEqns;
            this.polo = polo;
            this.usedImproved = usedImproved;
            this.usableRules = usableRules;
            this.usableEqs = usableEqs;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            if (true) { // TODO do s.th. w/ level

                result.append("By using the ");
                if(this.usedImproved) {
                    result.append("improved ");
                }
                result.append("usable rules and equations with reduction pair processor "+o.cite(Citation.DA_STEIN)+" with a polynomial ordering "+o.cite(Citation.POLO)+", " +
                                "all dependency pairs and the corresponding ");
                if(this.usedImproved) {
                    result.append("improved ");
                }
                result.append("usable rules can be oriented non-strictly, the ");
                if(this.usedImproved) {
                    result.append("improved ");
                }
                result.append(" usable equations and the esharp equations can be oriented equivalently.");
                result.append(" All non-usable rules and equations are removed, and ");
                result.append("those dependency pairs and ");
                if(this.usedImproved) {
                    result.append("improved ");
                }
                result.append("usable rules that have been oriented strictly or contain non-usable symbols in their left-hand side are removed as well.");
                result.append(o.linebreak());
                result.append(o.cond_linebreak());
                if (! this.removedPRules.isEmpty()) {
                    result.append("The following dependency pairs can be deleted:");
                    result.append(o.cond_linebreak());
                    result.append(o.set(this.removedPRules, Export_Util.RULES));
                }
                else {
                    result.append("No dependency pairs are removed.");
                    result.append(o.linebreak());
                    result.append(o.cond_linebreak());
                }
                if (! this.removedRRules.isEmpty()) {
                    result.append("The following rules are removed from R:");
                    result.append(o.cond_linebreak());
                    result.append(o.set(this.removedRRules, Export_Util.RULES));
                }
                else {
                    result.append("No rules are removed from R.");
                    result.append(o.linebreak());
                    result.append(o.cond_linebreak());
                }
                if (! this.removedEqns.isEmpty()) {
                    result.append("The following equations are removed from E:");
                    result.append(o.cond_linebreak());
                    result.append(o.set(this.removedEqns, Export_Util.RULES));
                }
                else {
                    result.append("No equations are removed from E.");
                    result.append(o.linebreak());
                    result.append(o.cond_linebreak());
                }
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
            Set<Rule> usable = new LinkedHashSet<>(this.usableRules);
            for (Equation e : this.usableEqs) {
        		usable.add(Rule.create((TRSFunctionApplication) e.getLeft(), e.getRight())); 
            }
            return CPFTag.AC_DP_PROOF.create(doc,
        	    CPFTag.AC_MONO_RED_PAIR_PROC.create(doc,
        		    this.polo.toCPF(doc, xmlMetaData),
        		    CPFTag.dps(doc, xmlMetaData, this.removedPRules),
        		    CPFTag.trs(doc, xmlMetaData, this.removedRRules),
        		    CPFTag.USABLE_RULES.create(doc, CPFTag.rules(doc, xmlMetaData, usable)),
        		    childrenProofs[0]
        		    ));
        }
        
        @Override
        public String getNonCPFExportableReason(final CPFModus modus) {
            return super.getNonCPFExportableReason(modus) + " " + (modus.isPositive() ? "in disproof" : "removed equations");
        }

        

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return modus.isPositive() && this.removedEqns.isEmpty();
        }

    }
}
