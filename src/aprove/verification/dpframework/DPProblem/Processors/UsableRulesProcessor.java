package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.POLO.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * @version $Id$
 */
public class UsableRulesProcessor extends QDPProblemProcessor {

    /**
     * only allows application if the application yields a complete method
     */
    private final boolean beComplete;

    /**
     * if an incomplete transformation is used (i.e., the ce-rules will
     * be added), then if this flag is set, we will use applicative
     * ce-rules for applicative DP problems
     */
    private final boolean useApplicativeCeRules;

    @ParamsViaArgumentObject
    public UsableRulesProcessor(final Arguments arguments) {
        this(arguments.beComplete, arguments.useApplicativeCeRules);
    }

    public UsableRulesProcessor(final boolean beComplete, final boolean useApplicativeCeRules) {
        this.beComplete = beComplete;
        this.useApplicativeCeRules = useApplicativeCeRules;
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        return null != UsableRulesProcessor.checkApplicabilityConditions(qdp, this.beComplete);
    }

    public static boolean isQDPApplicable(final QDPProblem qdp, final boolean beComplete) {
        return null != UsableRulesProcessor.checkApplicabilityConditions(qdp, beComplete);
    }

    /**
     * returns whether we have to add ce-rules,
     * returns null if the processor is not applicable
     * @param qdp
     * @param beComplete
     * @return
     */
    public static Boolean checkApplicabilityConditions(final QDPProblem qdp, boolean beComplete) {
        final boolean minimal = qdp.getMinimal();
        final boolean innermost = qdp.QsupersetOfLhsR();
        if (!minimal && !innermost) {
            // sorry, no usable rules processor possible
            // in termination case if we do not have minimality
            return null;
        }

        final Set<Rule> usableRules = qdp.getUsableRules();
        final Set<Rule> R = qdp.getR();

        // first check whether we can gain something
        if (usableRules.size() < R.size()) {
            boolean ce;
            // check for innermost
            if (innermost) {
                ce = false;
            } else {
                // check for non-duplication (simple MRR)
                if (Rule.isDuplicating(qdp.getP()) || Rule.isDuplicating(usableRules)) {
                    if (beComplete) {
                        return null;
                    }
                    ce = true;
                } else {
                    ce = false;
                }
            }
            return ce;
        } else {
            // if we cannot delete anything, do not use this processor
            return null;
        }
    }

    @Override
    protected Result processQDPProblem(QDPProblem qdp, final Abortion aborter) throws AbortionException {

        if (Globals.useAssertions) {
            assert (this.isApplicable(qdp));
        }

        final QDPProblem origQdp = qdp;

        final boolean addCe = UsableRulesProcessor.checkApplicabilityConditions(qdp, this.beComplete);
        ImmutableSet<Rule> usableRules = null;
        Set<Rule> ceRules = null;

        if (addCe) {
            usableRules = qdp.getUsableRules();
            final Set<FunctionSymbol> signature = qdp.getSignature();
            // find ce-symbol
            final String prefix = "c";
            final boolean useAppl = this.useApplicativeCeRules && qdp.getApplicativeInfo() != null;
            final int arity = useAppl ? 0 : 2;
            int postfix = 1;
            FunctionSymbol c = FunctionSymbol.create(prefix, arity);
            while (signature.contains(c)) {
                c = FunctionSymbol.create(prefix + postfix, arity);
                postfix++;
            }

            final TRSVariable x = TRSTerm.createVariable("x");
            final TRSVariable y = TRSTerm.createVariable("y");
            TRSFunctionApplication cxy;

            if (useAppl) {
                FunctionSymbol applicationSymbol;
                // choose new appl Symbol
                String appName = "a";
                applicationSymbol = FunctionSymbol.create(appName, 2);
                while (signature.contains(applicationSymbol)) {
                    appName += "p";
                    applicationSymbol = FunctionSymbol.create(appName, 2);
                }
                // okay, we have our application symbol now
                final TRSFunctionApplication cTerm = TRSTerm.createFunctionApplication(c, TRSTerm.EMPTY_ARGS);
                final TRSFunctionApplication cx =
                    TRSTerm.createFunctionApplication(applicationSymbol, new TRSTerm[] {cTerm, x });
                cxy = TRSTerm.createFunctionApplication(applicationSymbol, new TRSTerm[] {cx, y });

            } else {
                // non applicative => use standard rules

                // add c(x,y) -> x, c(x,y) -> y to usable rule set
                cxy = TRSTerm.createFunctionApplication(c, new TRSTerm[] {x, y });
            }

            // add rules
            ceRules = new LinkedHashSet<Rule>();
            ceRules.add(Rule.create(cxy, x));
            ceRules.add(Rule.create(cxy, y));

            final Set<Rule> newUsable = new LinkedHashSet<Rule>(usableRules);
            newUsable.addAll(ceRules);
            usableRules = ImmutableCreator.create(newUsable);
        }

        final boolean innermost = qdp.QsupersetOfLhsR();

        // build new qdp-problem
        if (addCe) {
            qdp = QDPProblem.create(qdp.getP(), QTRSProblem.create(usableRules), false);
        } else {
            if (innermost) {
                qdp = qdp.getSubProblemWithUsableRules();
            } else {
                qdp = qdp.getSubProblemWithSmallerR(qdp.getUsableRules());
            }
        }

        final Implication impl = addCe ? YNMImplication.SOUND : YNMImplication.EQUIVALENT;

        final Result result = ResultFactory.proved(qdp, impl, new UsableRulesProof(origQdp, qdp, ceRules, innermost));
        return result;

    }

    private static class UsableRulesProof extends QDPProof {

        private final Set<Rule> ceRules;
        private final QDPProblem origQDP;
        private final QDPProblem newQDP;
        private final boolean innermost;

        private UsableRulesProof(final QDPProblem origQDP, final QDPProblem newQDP, final Set<Rule> ceRules, final boolean innermost) {
            this.ceRules = ceRules;
            this.innermost = innermost;
            this.origQDP = origQDP;
            this.newQDP = newQDP;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            String res;
            String afterRes = null;
            if (this.innermost) {
                res =
                    "As all Q-normal forms are R-normal forms we are in the innermost case. "
                        + "Hence, by the usable rules processor " + o.cite(Citation.LPAR04)
                        + " we can delete all non-usable rules " + o.cite(Citation.FROCOS05) + " from R.";
            } else {
                if (this.ceRules != null) {
                    res =
                        "We use the Ce-Transformation " + o.cite(Citation.JAR06) + " to delete all non-usable rules "
                            + o.cite(Citation.FROCOS05) + " from R, but "
                            + "we lose minimality and add the following 2 Ce-rules:";
                    afterRes = o.set(this.ceRules, Export_Util.RULES);
                } else {
                    res =
                        "We can use the usable rules and reduction pair processor " + o.cite(Citation.LPAR04)
                            + " with the Ce-compatible extension of the "
                            + "polynomial order that maps every function symbol to the sum of its arguments. "
                            + "Then, we can delete all non-usable rules " + o.cite(Citation.FROCOS05) + " from R.";
                }
            }
            return o.export(res) + (afterRes == null ? "" : afterRes);
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            Element e;
            if (modus.isPositive()) {
                if (this.innermost) {
                    e = CPFTag.USABLE_RULES_PROC.create(doc);
                } else {
                    final Interpretation interpretation = Interpretation.create();
                    final Set<FunctionSymbol> fSyms = this.newQDP.getSignature();
                    for (final FunctionSymbol fSym : fSyms) {
                        VarPolynomial varPol = VarPolynomial.create(0);
                        for (int i = 1; i <= fSym.getArity(); i++) {
                            varPol = varPol.plus(VarPolynomial.createVariable(Interpretation.VARIABLE_PREFIX + i));
                        }
                        interpretation.put(fSym, varPol);
                    }
                    final POLO polo = POLO.create(interpretation);
                    e = CPFTag.MONO_RED_PAIR_UR_PROC.create(doc,
                            polo.toCPF(doc, xmlMetaData),
                            CPFTag.dps(doc, xmlMetaData, this.newQDP.getP()),
                            CPFTag.trs(doc, xmlMetaData, this.newQDP.getR()));
                }
                e.appendChild(CPFTag.USABLE_RULES.create(doc,
                        CPFTag.rules(doc, xmlMetaData, this.origQDP.getUsableRules())));
                e.appendChild(childrenProofs[0]);
                return CPFTag.DP_PROOF.create(doc, e);
            } else {
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.newQDP);
            }
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }


    }

    public static class Arguments {
        public boolean beComplete = true;
        public boolean useApplicativeCeRules = true;
    }
}
