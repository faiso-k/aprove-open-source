package aprove.verification.dpframework.Utility;

import java.io.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.newTrs.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import immutables.*;

/**
 * Normalizes a Term t in respect to a TRS.
 *
 * For deterministic results, the TRS should be terminating and confluent.
 *
 */
public class TRSEval implements Immutable {

    private final ImmutableCollection<Rule> rules;

    /**
     * @param rules TRS
     */
    public TRSEval(ImmutableCollection<Rule> rules) {
        this.rules = rules;
    }

    /**
     * @param ruledef TRS in standard tes input format
     */
    public TRSEval(String ruledef) {
        boolean restore = false;
        if (Main.firstObligation) {
            Main.firstObligation = false;
            restore = true;
        }
        Translator translator = new Translator();
        translator.translate(new StringReader(ruledef));
        QTRSProblem qtrs = (QTRSProblem)translator.getState();
        this.rules = qtrs.getR();
        if (restore) {
            Main.firstObligation = true;
        }
    }

    /**
     * Normalizes a Term t in respect to the TRS.
     */
    public TRSTerm normalize(TRSTerm t) {
        if (t == null) {
            return null;
        }
        if (t.isVariable()) {
            return t;
        }

        boolean first = true;
        boolean modified;
        do {
            modified = false;
            for (Rule rule : this.rules) {
                TRSSubstitution sigma = rule.getLeft().getMatcher(t);
                if (sigma != null) {
                    t = this.normalize(rule.getRight().applySubstitution(sigma));

                    if (t.isVariable()) {
                        return t;
                    }

                    modified = true;
                }
            }

            if (!first && !modified) {
                break;
            }
            first = false;

            TRSFunctionApplication fa = (TRSFunctionApplication)t;
            ArrayList<TRSTerm> newArgs =
                new ArrayList<TRSTerm>(fa.getArguments().size());
            boolean modified_args = false;
            for (TRSTerm arg : fa.getArguments()) {
                TRSTerm newArg = this.normalize(arg);
                newArgs.add(newArg);
                modified_args |= (newArg != arg);
            }
            if (modified_args) {
                t = TRSTerm.createFunctionApplication(fa.getRootSymbol(),
                        ImmutableCreator.create(newArgs));
                modified = true;
            }
        } while (modified);

        return t;
    }

}
