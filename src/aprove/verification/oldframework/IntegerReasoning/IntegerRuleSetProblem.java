package aprove.verification.oldframework.IntegerReasoning;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Just a set of rules with integers, terms, and conditions (without any further restrictions - except those stated in
 * additional attributes).
 * @author cryingshadow
 * @version $Id$
 */
public class IntegerRuleSetProblem extends DefaultBasicObligation {

    /**
     * Can free variables only be instantiated by constructor terms?
     */
    private final boolean constructorRewriting;

    /**
     * The analysis purpose.
     */
    private final IntegerRuleSetPurpose purpose;

    /**
     * Restriction on rewrite positions.
     */
    private final IntegerRuleSetRewritePosition rewritePosition;

    /**
     * The set of rules.
     */
    private final ImmutableSet<IGeneralizedRule> rules;

    /**
     * @param set The set of rules.
     * @param p The analysis purpose.
     * @param r Restriction on rewrite positions.
     * @param c Can free variables only be instantiated by constructor terms?
     */
    public IntegerRuleSetProblem(
        Set<IGeneralizedRule> set,
        IntegerRuleSetPurpose p,
        IntegerRuleSetRewritePosition r,
        boolean c
    ) {
        this.rules = ImmutableCreator.create(set);
        this.purpose = p;
        this.rewritePosition = r;
        this.constructorRewriting = c;
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        res.append("We have the following set of rules to analyze for ");
        res.append(this.getPurpose().getPurpose());
        res.append(":");
        res.append(eu.newline());
        res.append(eu.newline());
        res.append(eu.set(this.getRules(), Export_Util.RULES));
        res.append(eu.newline());
        res.append(eu.newline());
        res.append("We have the following restrictions:");
        res.append(eu.newline());
        List<String> list = new ArrayList<String>();
        if (this.onlyConstructorRewriting()) {
            list.add("constructor rewriting");
        }
        switch (this.getRewritePosition()) {
            case INNERMOST:
                list.add("innermost rewriting");
                break;
            case TOPMOST:
                list.add("top-level rewriting");
                break;
            default:
                // do nothing
        }
        if (list.isEmpty()) {
            res.append("none");
        } else {
            ObjectUtils.binaryStringFold(list, ", ", res);
        }
        return res.toString();
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return
            new ProofPurposeDescriptor() {

                @Override
                public String export(Export_Util eu) {
                    return
                        ProofPurposeDescriptor.export(
                            this.getStatus(),
                            this.getPurpose(),
                            "the given integer rule set",
                            eu
                        );
                }

                @Override
                public String getPurpose() {
                    return IntegerRuleSetProblem.this.getPurpose().getPurpose();
                }

            };
    }

    /**
     * @return The analysis purpose.
     */
    public IntegerRuleSetPurpose getPurpose() {
        return this.purpose;
    }

    /**
     * @return The restriction on rewrite positions.
     */
    public IntegerRuleSetRewritePosition getRewritePosition() {
        return this.rewritePosition;
    }

    /**
     * @return The rules.
     */
    public ImmutableSet<IGeneralizedRule> getRules() {
        return this.rules;
    }

    @Override
    public String getStrategyName() {
        // this obligation should only occur in intermediate steps
        // TODO?
        return null;
    }

    /**
     * @return Can free variables only be instantiated by constructor terms?
     */
    public boolean onlyConstructorRewriting() {
        return this.constructorRewriting;
    }

    /**
     * Analysis purposes for integer rule sets.
     * @author cryingshadow
     * @version $Id$
     */
    public static enum IntegerRuleSetPurpose {

        /**
         * Runtime complexity.
         */
        RUNTIME_COMPLEXITY {

            @Override
            public String getPurpose() {
                return "Runtime Complexity";
            }

        },

        /**
         * Termination.
         */
        TERMINATION {

            @Override
            public String getPurpose() {
                return "Termination";
            }

        };

        /**
         * @return The name of this purpose.
         */
        public abstract String getPurpose();

    }

    /**
     * The positions where rewrite steps are applicable.
     * @author cryingshadow
     * @version $Id$
     */
    public static enum IntegerRuleSetRewritePosition {

        /**
         * Full rewriting.
         */
        FULL,

        /**
         * Only innermost rewriting.
         */
        INNERMOST,

        /**
         * Only top-level rewriting that is also innermost.
         */
        TOPANDINNERMOST,

        /**
         * Only top-level rewriting.
         */
        TOPMOST

    }

}
