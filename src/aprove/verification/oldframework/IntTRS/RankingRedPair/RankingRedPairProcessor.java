package aprove.verification.oldframework.IntTRS.RankingRedPair;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * This processor tries to synthesize some (non)linear rankings, which can be
 * used to simplify the given int-TRS.
 * @author Matthias Hoelzel
 */
public class RankingRedPairProcessor extends Processor.ProcessorSkeleton {
    /** Some arguments */
    private final Arguments arguments;

    /** Some argument class */
    public static class Arguments {
        /**
         * Use this to generate further constraints, e.g. x >= 3 & y >= 4
         * implies xy - 4x - 3y >= -12.
         */
        public boolean generateFollowingInequalities;

        /**
         * Eliminate free variables, i.e., simplify x >= z & z >= y to x >= y
         * where z is a free variable, which means that z is neither a start-
         * nor a end-variable.
         */
        public boolean freeVariableElimination = true;

        /**
         * If set to true, then the processor tries to infer which rules are
         * decreasing w.r.t. the polynomial interpretation and which rules are
         * bounded. Then the processor returns two problems: one problem without
         * the decreasing rules and another without the bounded rules.
         */
        public boolean useGeneralizedReductionPairs = true;

        /**
         * Linearize all expressions (for non-CLASSIC templates).
         * True:  x^2*y becomes z.
         * False: x^2*y becomes z*y where we can use that z = x^2.
         */
        public boolean linearizeAll = true;

        /**
         * The template for the (polynomial) ranking function. Classically
         * LINEAR but some massaging of the rules allows to use quite
         * different template functions.
         */
        public Template template = Template.CLASSIC;
    }

    /**
     * A template shape for a ranking function for the function symbols
     * (currently the same shape is used for each function symbol,
     * accounting for the symbol's respective arity, of course).
     */
    public enum Template {
        /** Sum of a constant and the arguments, the classic setting. */
        CLASSIC,
        /** Sum of a constant, the arguments, and their respective squares. */
        QUADRATIC,
        /** Sum of a constant, the arguments, and their respective absolutes values. */
        ABS;
    }

    /**
     * A constructor.
     * @param args Arguments for the processor.
     */
    @ParamsViaArgumentObject
    public RankingRedPairProcessor(final Arguments args) {
        this.arguments = args;
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        // for certified mode only use CLASSIC
        if (Options.certifier.isNone() || this.arguments.template == Template.CLASSIC) {
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
        assert obl instanceof IRSwTProblem : "Wrong obligation type!";
    if (!Options.certifier.isNone()) {
        this.arguments.useGeneralizedReductionPairs = false;
    }

    final IRSProblem oldProb;
    if (obl instanceof IRSProblem) {
        oldProb = (IRSProblem) obl;
    } else {
        oldProb = new IRSProblem((IRSwTProblem) obl);
    }
    final RankingReductionPairProof proof = new RankingReductionPairProof();
    final RankingRedPairWorker worker = new RankingRedPairWorker(oldProb, proof, this.arguments, aborter);

    final List<Set<IGeneralizedRule>> newRules = worker.work();

    if (newRules.size() == 1 && newRules.get(0).equals(oldProb.getRules())) {
        return ResultFactory.unsuccessful();
    } else if (newRules.isEmpty()) {
        return ResultFactory.proved(proof);
    } else if (newRules.size() == 1 && newRules.get(0).isEmpty()) {
        return ResultFactory.proved(proof);
    } else {
        final LinkedList<IRSProblem> results = new LinkedList<>();
        for (final Set<IGeneralizedRule> system : newRules) {
            results.add(new IRSProblem(ImmutableCreator.create(system)));
        }
        return ResultFactory.provedAnd(results, YNMImplication.EQUIVALENT, proof);
    }
        }

    /**
     * A very fine proof.
     * @author cotto (don't blame me), Matthias Hoelzel (blame cotto instead)
     */
    public class RankingReductionPairProof extends DefaultProof {
        /** The model, generated by the SMT-Solver */
        private Map<String, PreciseRational> model;

        /** The template for the interpretation */
        private Map<FunctionSymbol, VarPolynomial> template;

        /** Set of rules dropped due to strict decrease */
        private Set<IGeneralizedRule> droppedByStrictDecrease;

        /** Set of rules dropped due to boundedness */
        private Set<IGeneralizedRule> droppedByBoundedness;
        
        /** Global bound */
        private BigInteger bound;

        /**
         * Creates the proof.
         */
        public RankingReductionPairProof() {
        }

        /**
         * Setter for model.
         * @param modelValue maps string to rational values
         */
        public void setModel(final Map<String, PreciseRational> modelValue) {
            this.model = modelValue;
        }
        
        /**
         * Setter for bound
         * @param bound
         */
        public void setBound(final BigInteger bound) {
            this.bound = bound;
        }

        /**
         * Setter for template.
         * @param templateValue maps FunctionSymbols to VarPolynomials
         */
        public void setTemplate(final Map<FunctionSymbol, VarPolynomial> templateValue) {
            this.template = templateValue;
        }

        /**
         * Setter for droppedByStrictDecrease.
         * @param droppedRulesValue set of dropped rules
         */
        public void setDroppedRulesDueToDecrease(final Set<IGeneralizedRule> droppedRulesValue) {
            this.droppedByStrictDecrease = droppedRulesValue;
        }

        /**
         * Setter for droppedByBoundedness
         * @param droppedRulesValue set of dropped rules
         */
        public void setDroppedRulesDueToBoundedness(final Set<IGeneralizedRule> droppedRulesValue) {
            this.droppedByBoundedness = droppedRulesValue;
        }

        /**
         * @param eu export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            if (this.template == null || this.droppedByStrictDecrease == null || this.model == null) {
                return eu.tttext("Unsuccessful!");
            }

            final StringBuilder sb = new StringBuilder();
            this.exportInterpretation(eu, sb);
            this.exportDroppedRules(eu, sb);

            return sb.toString();
        }

        /**
         * Exports the interpretation.
         * @param eu some export helper
         * @param sb some StringBuilder
         */
        private void exportInterpretation(final Export_Util eu, final StringBuilder sb) {
            sb.append(eu.indent(eu.bold(eu.tttext("Interpretation:"))));
            sb.append(eu.linebreak());
            assert this.template != null && this.model != null : "exportInterpretation must not be called if the processor failed!";
            for (final Entry<FunctionSymbol, VarPolynomial> e : this.template.entrySet()) {
                sb.append(eu.escape("[ "));
                sb.append(e.getKey().export(eu));
                sb.append(eu.escape(" ] = "));
                boolean first = true;
                for (final Entry<IndefinitePart, SimplePolynomial> mono : e.getValue().getVarMonomials().entrySet()) {
                    final SimplePolynomial simple = mono.getValue();
                    final IndefinitePart indefPart = mono.getKey();
                    assert simple.isIndefinite() : "Invalid template!";
                    final String coeff = simple.getIndefinites().iterator().next();
                    final PreciseRational value = this.model.get(coeff);
                    assert value != null : "Invalid model!";
                    if (value.equals(new PreciseRational(BigInteger.ZERO))) {
                        continue;
                    }
                    if (!first) {
                        sb.append(eu.escape(" + "));
                    }
                    first = false;
                    if (value.equals(new PreciseRational(BigInteger.ONE))) {
                        sb.append(indefPart.export(eu));
                    } else {
                        sb.append(value.export(eu));
                        if (!indefPart.isEmpty()) {
                            sb.append(eu.multSign());
                            sb.append(indefPart.export(eu));
                        }
                    }
                }
                if (first) {
                    sb.append(eu.escape("0"));
                }
                sb.append(eu.linebreak());
            }
        }

        /**
         * Exports dropped rules.
         * @param eu some export helper
         * @param sb some StringBuilder
         */
        private void exportDroppedRules(final Export_Util eu, final StringBuilder sb) {
            // Export dropped rules:
            sb.append(eu.linebreak());
            sb.append(eu.indent(eu.bold(eu.tttext("The following rules are decreasing:"))));
            sb.append(eu.linebreak());
            this.exportRules(sb, eu, this.droppedByStrictDecrease);

            if (this.droppedByBoundedness != null) {
                sb.append(eu.indent(eu.bold(eu.tttext("The following rules are bounded:"))));
                sb.append(eu.linebreak());
                this.exportRules(sb, eu, this.droppedByBoundedness);
            }
        }

        /**
         * Exports a given set of rules.
         * @param sb some string builder
         * @param eu some export helper
         * @param rules rule to be exported
         */
        private
        void
        exportRules(final StringBuilder sb, final Export_Util eu, final Collection<IGeneralizedRule> rules)
        {
            for (final IGeneralizedRule iRule : rules) {
                sb.append(iRule.export(eu));
                sb.append(eu.linebreak());
            }
            sb.append(eu.linebreak());
        }

        public Set<IGeneralizedRule> getDroppedRulesDueToBoundedness() {
            return this.droppedByBoundedness;
        }

        public Set<IGeneralizedRule> getDroppedRulesDueToDecrease() {
            return this.droppedByStrictDecrease;
        }
        
        private Element varPolyToCPF(Document doc, VarPolynomial poly, Map<String, String> vars, PreciseRational lcd) {
            boolean first = true;
            final Element sum = CPFTag.SUM.createElement(doc);
            for (final Entry<IndefinitePart, SimplePolynomial> mono : poly.getVarMonomials().entrySet()) {
                final SimplePolynomial simple = mono.getValue();
                final IndefinitePart poloFactor = mono.getKey();
                final String coeff = simple.getIndefinites().iterator().next();
                final PreciseRational value = this.model.get(coeff).multiply(lcd);
                if (value.equals(new PreciseRational(BigInteger.ZERO))) {
                    continue;
                }                
                first = false;             
                if (!value.getDenominator().equals(BigInteger.ONE)) {
                    throw new RuntimeException("interal error: rational number in LTS-CPF-output should not occur\n" + value);
                }
                final Element coeffE = CPFTag.LTS_CONSTANT.create(doc, value.getNumerator());                
                final Element polynomial = poloFactor.toCpfLTS(doc, coeffE, vars);
                sum.appendChild(polynomial);
            }            
            
            if (first) {
                return CPFTag.LTS_CONSTANT.create(doc, 0);
            }
            return sum;
        }
        
        private BigInteger lcd;
        
        private void computeLcd() {
            BigInteger lcd = BigInteger.ONE;
            for (VarPolynomial poly : this.template.values()) {
                for (SimplePolynomial simple : poly.getVarMonomials().values()) {
                    final String coeff = simple.getIndefinites().iterator().next();
                    final PreciseRational value = this.model.get(coeff);
                    BigInteger denom = value.getDenominator();
                    if (!denom.equals(BigInteger.ONE)) {
                		lcd = lcd.multiply(denom).divide(lcd.gcd(denom));
                    }
                }        	
            }  
            this.lcd = lcd;            
        }
        
        private Element interpretationToCPF(Document doc, XMLMetaData xmlMetaData) {
            
            /* compute common denominator of coefficients */
            PreciseRational lcd_pr = new PreciseRational(this.lcd); 
            
            
            Element rfs = CPFTag.LTS_RANKING_FUNCTIONS.create(doc);
            for (final Entry<FunctionSymbol, VarPolynomial> entry : this.template.entrySet()) {
                FunctionSymbol f = entry.getKey();
                String ff = f.getName();
                VarPolynomial expr = entry.getValue();
                Map<String, String> map = new HashMap<>();
                List<String> cpfVars = xmlMetaData.getVarsForFS(f);
                int i = 1;
                for (String x : cpfVars) {
                    map.put(ff + "_" + i, x);
                    i++;
                }
                Element loc = CPFTag.LTS_LOCATION.create(doc, CPFTag.LTS_LOCATION_DUP.create(doc, ff));
                Element exp = CPFTag.LTS_EXPRESSION.create(doc, this.varPolyToCPF(doc, expr, map, lcd_pr));            
                Element rf = CPFTag.LTS_RANKING_FUNCTION.create(doc, loc, exp);
                rfs.appendChild(rf);
            }
            return rfs;
         }
        
        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            this.computeLcd();
            Element subProof = childrenProofs.length == 0 ? CPFTag.LTS_TRIVIAL.create(doc) : childrenProofs[0];
            Element rfs = interpretationToCPF(doc, xmlMetaData);
            Element bnd = CPFTag.LTS_BOUND.create(doc, CPFTag.CONSTANT.create(doc, this.bound.multiply(this.lcd).toString()));
            Element removed = CPFTag.LTS_REMOVE.create(doc);
            for (IGeneralizedRule rule : this.droppedByStrictDecrease) {
                String transitionId = rule.getTransitionId(xmlMetaData);
                Element id = CPFTag.LTS_TRANSITION_DUP.create(doc, transitionId);
                removed.appendChild(id);
            }
            return CPFTag.LTS_TRANSITION_REMOVAL.create(doc, rfs, bnd, removed, subProof);

        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return modus.isPositive();
        }        

    }
}
