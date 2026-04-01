package aprove.verification.complexity.LowerBounds.EquationalRewriting;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.dpframework.BasicStructures.*;

/** rewriting can be ordinary term rewriting, narrowing... */
public class TermRewriter {

    @SuppressWarnings("serial")
    class OverlappingRewritingException extends Exception{}

    private static int MAX_DEPTH = 100;
    LowerBoundsToolbox toolbox;
    private SingleStepRewriter rewriter;

    public TermRewriter(LowerBoundsToolbox toolbox) {
        this.toolbox = toolbox;
        this.rewriter = new SingleStepRewriter(toolbox);
    }

    public Set<RewriteSequence> normalize(TRSFunctionApplication startTerm) throws AbortionException {
        Set<RewriteSequence> todo = new LinkedHashSet<>();
        Set<RewriteSequence> res = new LinkedHashSet<>();
        todo.add(new RewriteSequence(startTerm, this.toolbox));
        for (int i = TermRewriter.MAX_DEPTH; i > 0 && !todo.isEmpty(); --i) {
            Set<RewriteSequence> newTodo = new LinkedHashSet<>();
            for (RewriteSequence seq: todo) {
                Set<RewriteSequence> s;
                try {
                    s = this.oneStep(seq, this.rewriter);
                } catch (OverlappingRewritingException e) {
                    s = Collections.emptySet();
                }
                if (s.isEmpty()) {
                    res.add(seq);
                } else {
                    newTodo.addAll(s);
                }
            }
            todo = newTodo;
        }
        return res;
    }

    private Set<RewriteSequence> oneStep(RewriteSequence seq, SingleStepRewriter rewriter) throws OverlappingRewritingException, AbortionException {
        Set<RewriteSequence> res = new LinkedHashSet<>();
        TRSTerm t = seq.getResult();
        this.toolbox.aborter.checkAbortion();
        // enforce innermost rewriting.
        Set<Position> sortedPositions = new TreeSet<>(new InnerMostPositionComparator());
        sortedPositions.addAll(t.getPositions());
        for (Position pos : sortedPositions) {
            TRSTerm s = t.getSubterm(pos);
            if (s.getFunctionSymbols().contains(this.toolbox.arbitraryTerm.getRootSymbol()) || s.isVariable()) {
                continue;
            }
            Set<RewriteStep> steps = rewriter.rewrite(t, pos);
            if (this.toolbox.trs.isInnermost() && steps.isEmpty() && !s.isVariable()) {
                switch (this.toolbox.trs.unifiesWithLhs((TRSFunctionApplication) s, this.toolbox)) {
                    case NO:
                        break;
                    // if we cannot guarantee that there is no overlapping rule, then we have to stop rewriting
                    default:
                        throw new OverlappingRewritingException();
                }
            }
            for (RewriteStep step: steps) {
                RewriteSequence toAdd = seq.addStep(step);
                res.add(toAdd);
            }
            if (!res.isEmpty()) {
                return res;
            }
        }
        return res;
    }

}
