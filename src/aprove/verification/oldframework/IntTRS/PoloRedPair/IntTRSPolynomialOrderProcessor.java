package aprove.verification.oldframework.IntTRS.PoloRedPair;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

/**
 * Tries to find a polynomial order. In case of success it will remove every
 * rule that is oriented strictly.
 * @author Matthias Hoelzel
 */
public class IntTRSPolynomialOrderProcessor extends Processor.ProcessorSkeleton {
    /** The arguments */
    private final PolynomialOrderArguments arguments;

    /** A class for the arguments */
    public static class PolynomialOrderArguments {
        /**
         * Strategy to select lower or upper bounds, if both are available.
         */
        public BoundBehavior boundBehavior = BoundBehavior.PREFER_LOWER_BOUNDS;

        /** The degree for the polynomial order we want to use. */
        public int degree = 1;

        /**
         * Hunting for binomials in order to generate weaker constraints. This
         * will only be useful, if degree is larger than 1.
         */
        public boolean factorBinomials;

        /**
         * @deprecated for unknown reasons
         */
        @Deprecated
        public boolean alwaysReturnObligation;

        /**
         * If set to true, then we try to combine arguments. Example: x > y, y >
         * 5 => x >= 7.
         */
        public boolean combineArgumentConstraints = true;

        /**
         * If we have a variable x with a <= x <= a + c, then we do a case
         * distinction: x = a or x = a + 1 or .. or x = a + c. Otherwise we can
         * only use x <= a+c or a <= x. This argument controls how big c is
         * allowed to be.
         */
        public int variableInstantiationLimit = 1;

        /**
         * If set to false, the processor will always do what boundBehavior
         * says.
         */
        public boolean useBoundHeuristic = true;

        /**
         * If set to true, then the processor tries to infers which rules are
         * decreasing w.r.t. the polynomial interpretation and which rules are
         * bounded. Then the processor returns two problems: one problem without
         * the decreasing rules and another without the bounded rules.
         */
        public boolean useGeneralizedReductionPairs = true;

        /**
         * If set to false, the processor will not use a heuristic to choose the
         * variable to be substituted. Instead it uses the first variable which
         * in the list of expressible variables. For instance, if we have
         * something like x1 + x2 >= 0 the left term can be substituted using a
         * fresh variable u := x1 + x2. To introduce the new variable u (with
         * lower bound 0) it is possible to substitute x1 by u - x2 or x2 by u -
         * x1.
         */
        public boolean useSubstitutionHeuristic = true;

        /**
         * Use the new way to generate the constraints or the old one.
         */
        public boolean useNewConstraintsGeneration = true;
    }

    /**
     * A constructor.
     */
    public IntTRSPolynomialOrderProcessor() {
        this.arguments = new PolynomialOrderArguments();
    }

    /**
     * A constructor.
     * @param args Arguments for the processor.
     */
    public IntTRSPolynomialOrderProcessor(final PolynomialOrderArguments args) {
        this.arguments = args;
    }

    /**
     * Setter for the argument boundBehavior.
     * @param val BoundBehavior
     */
    public void setBoundBehavior(final BoundBehavior val) {
        this.arguments.boundBehavior = val;
    }

    /**
     * Setter for the argument degree.
     * @param val int
     */
    public void setDegree(final int val) {
        this.arguments.degree = val;
    }

    /**
     * Setter for the argument combineArgumentConstraints.
     * @param val boolean
     */
    public void setCombineArgumentConstraints(final boolean val) {
        this.arguments.combineArgumentConstraints = val;
    }

    /**
     * Setter for the argument variableInstantiationLimit.
     * @param val int
     */
    public void setVariableInstantiationLimit(final int val) {
        this.arguments.variableInstantiationLimit = val;
    }

    /**
     * Setter for the argument useBoundHeuristic.
     * @param val boolean
     */
    public void setUseBoundHeuristic(final boolean val) {
        this.arguments.useBoundHeuristic = val;
    }

    /**
     * Setter for the argument factorBinomials.
     * @param val boolean
     */
    public void setFactorBinomials(final boolean val) {
        this.arguments.factorBinomials = val;
    }

    /**
     * Setter for the argument useSubstitutionHeuristic.
     * @param val boolean
     */
    public void setUseSubstitutionHeuristic(final boolean val) {
        this.arguments.useSubstitutionHeuristic = val;
    }

    /**
     * Setter for the argument useGeneralizedReductionPairs.
     * @param val boolean
     */
    public void setUseGeneralizedReductionPairs(final boolean val) {
        this.arguments.useGeneralizedReductionPairs = val;
    }

    /**
     * Setter for the argument useNewConstraintsGeneration.
     * @param val boolean
     */
    public void setUseNewConstraintsGeneration(final boolean val) {
        this.arguments.useNewConstraintsGeneration = val;
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        // no non-linear orderings in certified mode
        if (Options.certifier.isNone() || this.arguments.degree == 1) {
            return obl instanceof IRSwTProblem && ((IRSwTProblem) obl).isIRS();
        }
        return false;
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
        {
        assert (obl instanceof IRSwTProblem);
        final IRSProblem problem;
        if (obl instanceof IRSProblem) {
            problem = (IRSProblem) obl;
        } else { // 123
            problem = new IRSProblem((IRSwTProblem) obl);
        }
        if (Options.certifier.isCeta()) {
            this.setUseGeneralizedReductionPairs(false);
        }
        final IntTRSPoloRedPairProof proof = new IntTRSPoloRedPairProof();

        final IntTRSPolynomialOrderWorker worker =
            new IntTRSPolynomialOrderWorker(problem, aborter, proof, this.arguments);
        final List<IRSProblem> toSolve = worker.work();
        int n = toSolve.size();
        if (n == 1 && toSolve.get(0).getRules().isEmpty()) {
            n = 0;
        }
        proof.setNumberSubproofs(n);

        if (n == 0) {
            // Nobody wants to see TRUE; everybody wants YES!
            return ResultFactory.proved(proof);
        } else if (!worker.hasChangedProblem()) {
            return ResultFactory.unsuccessful();
        } else {
            return ResultFactory.provedAnd(toSolve, YNMImplication.EQUIVALENT, proof);
        }
        }

    /**
     * A very fine proof.
     * @author cotto (don't blame me), Matthias Hoelzel
     */
    public class IntTRSPoloRedPairProof extends DefaultProof {
        /** The interpretation we used. Null if this did not work out. */
        private PolynomialInterpretation interpretation;

        /**
         * Collection of rules that have been removed due to a decrease in the
         * interpretation. Can also be null.
         */
        private Collection<IGeneralizedRule> droppedRulesDueToDecrease;

        /**
         * Collection of rules that have been removed due to boundedness. Can
         * also be null.
         */
        private Collection<IGeneralizedRule> droppedRulesDueToBoundedness;
        
        private int numberOfSubproofs; 

        /** Create the proof. */
        public IntTRSPoloRedPairProof() {
            super();
            this.shortName = "PolynomialOrderProcessor";
            this.longName = "PolynomialOrderProcessor";

            this.interpretation = null;
            this.droppedRulesDueToDecrease = null;
            this.droppedRulesDueToBoundedness = null;
            this.numberOfSubproofs = 0;
        }

        /**
         * Set the interpretation.
         * @param interpret polynomial interpretation
         */
        public void setIntepretation(final PolynomialInterpretation interpret) {
            this.interpretation = interpret;
        }

        /**
         * Get the interpretation.
         * @return
         */
        public PolynomialInterpretation getIntepretation() {
            return this.interpretation;
        }
        
        public void setNumberSubproofs(int number) {
            this.numberOfSubproofs = number;
        }

        /**
         * Sets the rules dropped due to a decrease in the interpretation.
         * @param dropped collection of rules
         */
        public void setDroppedRulesDueToDecrease(final Collection<IGeneralizedRule> dropped) {
            this.droppedRulesDueToDecrease = dropped;
        }

        /**
         * Stores the set of rules dropped due to boundedness.
         */
        public void setDroppedRulesDueToBoundedness(final Collection<IGeneralizedRule> dropped) {
            this.droppedRulesDueToBoundedness = dropped;
        }

        /**
         * Gets the rules dropped due to a decrease in the interpretation.
         * @return
         */
        public Collection<IGeneralizedRule> getDroppedRulesDueToDecrease() {
            return this.droppedRulesDueToDecrease;
        }

        /**
         * Gets the set of rules dropped due to boundedness.
         * @return
         */
        public Collection<IGeneralizedRule> getDroppedRulesDueToBoundedness() {
            return this.droppedRulesDueToBoundedness;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder builder = new StringBuilder();
            if (this.interpretation != null && this.droppedRulesDueToDecrease != null) {
                builder.append(eu.indent(eu.bold(eu.tttext("Found the following polynomial interpretation:"))));
                builder.append(eu.linebreak());
                builder.append(this.interpretation.export(eu));
                builder.append(eu.linebreak());
                builder.append(eu.indent(eu.bold(eu.tttext("The following rules are decreasing:"))));
                for (final IGeneralizedRule iRule : this.droppedRulesDueToDecrease) {
                    builder.append(eu.linebreak());
                    builder.append(iRule.export(eu));
                }
                builder.append(eu.linebreak());
                if (this.droppedRulesDueToBoundedness != null) {
                    builder.append(eu.indent(eu.bold(eu.tttext("The following rules are bounded:"))));
                    for (final IGeneralizedRule iRule : this.droppedRulesDueToBoundedness) {
                        builder.append(eu.linebreak());
                        builder.append(iRule.export(eu));
                    }
                    builder.append(eu.linebreak());
                }
            } else {
                builder.append("Could not find a polynomial order.");
            }
            return builder.toString();
        }
        
        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            Element subProof = this.numberOfSubproofs == 0 ? CPFTag.LTS_TRIVIAL.create(doc) : childrenProofs[0];
            Element rfs = this.interpretation.toCPF(doc, xmlMetaData);
            Element bnd = CPFTag.LTS_BOUND.create(doc, CPFTag.CONSTANT.create(doc, 0));
            Element removed = CPFTag.LTS_REMOVE.create(doc);
            for (IGeneralizedRule rule : this.droppedRulesDueToDecrease) {
                String transitionId = rule.getTransitionId(xmlMetaData);
                Element id = CPFTag.LTS_TRANSITION_DUP.create(doc, transitionId);
                removed.appendChild(id);
            }
            return CPFTag.LTS_TRANSITION_REMOVAL.create(doc, rfs, bnd, removed, subProof);
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return modus.isPositive() && this.numberOfSubproofs <= 1;
        }

        
    }
}
