package aprove.verification.complexity.CpxTrsProblem.Processors;

import java.util.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxRelTrsProblem.Processors.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.Utility.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * This processor is based on the following observation:
 *
 * If R is constructor based, s is basic, and s -->^n t is the longest sequence starting in s s.t.
 * t is a normal form and no defined symbol is duplicated in the rewrite sequence, then s -i>^n t.
 *
 *
 * Hence, if
 *
 * (A) R-rewrite sequences starting in basic terms do not duplicate defined symbols
 *
 * then rc(R) = irc(R).
 *
 * This class implements three sufficient criteria for (A)
 *
 * (1) For each l -> r in R, l as well as r contains at most one defined symbol.
 * (2) R is non-duplicating.
 * (3) Let duplicatedPositions = {C | C is a basic context and
 *                                    there is an R-step C[t] -> s where t is duplicated}
 *     and let definedPositions = {C | C is a basic context and
 *                                     a term D[C[t]] where t contains defined symbols is reachable from a basic term}.
 *     Then (A) holds if R is left-linear and duplicatedPositions and definedPositions are disjoint.
 *
 * We check (3) by overapproximating the sets duplicatedPositions and definedPositions.
 */
public class CpxTrsRcToIrcProcessor extends RuntimeComplexityRelTrsProcessor {

    public static class Arguments {
        // set this to true to switch from innermost to full (the default is vice versa)
        public boolean innermost = false;
    }

    public Arguments args;

    @ParamsViaArgumentObject
    public CpxTrsRcToIrcProcessor(Arguments args) {
        this.args = args;
    }

    private class RcEqualsIrcProof extends DefaultProof {

    	Proof sparenessProof;

    	public RcEqualsIrcProof(Proof sparenessProof) {
			this.sparenessProof = sparenessProof;
		}

    	@Override
    	public String export(Export_Util o, VerbosityLevel level) {
    		StringBuilder proof = new StringBuilder();
    		if (args.innermost) {
    			proof.append(o.export("Switched from innermost to full rewriting."));
    		} else {
    			proof.append(o.export("Switched from full to innermost rewriting."));
    		}
			proof.append(o.paragraph());
    		proof.append(o.escape("The system is spare. As it is also an overlay system, we have rc=irc."));
    		proof.append(o.newline());
    		proof.append(o.escape("Proof of spareness:"));
    		proof.append(o.paragraph());
    		proof.append(sparenessProof.export(o, level));
    		return proof.toString();
    	}

    }

    @Override
    protected Result processRuntimeComplexityRelTrs(RuntimeComplexityRelTrsProblem obl, Abortion aborter) {
        Set<Rule> rules = new LinkedHashSet<>();
        rules.addAll(obl.getR());
        rules.addAll(obl.getS());
        var ruleSet = new RuleSet(ImmutableCreator.create(rules), obl.getDefinedSymbols());
        if (!ruleSet.isOverlaySystem()) {
            return ResultFactory.unsuccessful();
        }
        Optional<DefaultProof> proof = new SparenessApproximation(ruleSet).run(false);
        if (proof.isPresent()) {
            RewriteStrategy newRewriteStrategy;
            switch (obl.getRewriteStrategy()) {
            case FULL:
                newRewriteStrategy = RewriteStrategy.INNERMOST;
                break;
            case INNERMOST:
                newRewriteStrategy = RewriteStrategy.FULL;
                break;
            default:
                throw new NotYetHandledException("Don't know what to do with rewrite strategy "
                        + obl.getRewriteStrategy() + '!');
            }
            RuntimeComplexityRelTrsProblem newRelTrs = RuntimeComplexityRelTrsProblem.create(obl.getR(), obl.getS(),
                newRewriteStrategy, obl.STerminatesInnermost());
            return ResultFactory.proved(newRelTrs, BothBounds.create(), new RcEqualsIrcProof(proof.get()));
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    @Override
    protected boolean isRuntimeComplexityRelTrsApplicable(RuntimeComplexityRelTrsProblem obl) {
        return Options.certifier == Certifier.NONE
                && (args.innermost ? obl.getRewriteStrategy() == RewriteStrategy.INNERMOST : obl.getRewriteStrategy() == RewriteStrategy.FULL)
                && obl.STerminatesInnermost();
    }

}
