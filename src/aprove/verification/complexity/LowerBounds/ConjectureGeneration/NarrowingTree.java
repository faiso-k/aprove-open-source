package aprove.verification.complexity.LowerBounds.ConjectureGeneration;

import java.util.*;
import java.util.Map.Entry;

import aprove.strategies.Abortions.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class NarrowingTree {

    private Map<RewriteStep, NarrowingTree> children;
    private LowerBoundsToolbox toolbox;
    private SingleStepNarrower singleStepNarrower;
    private TRSTerm term;
    private Abortion abortion;

    private NarrowingTree(LowerBoundsToolbox toolbox, SingleStepNarrower singleStepNarrower, TRSTerm term, Abortion abortion) {
        this.toolbox = toolbox;
        this.singleStepNarrower = singleStepNarrower;
        this.term = term;
        this.abortion = abortion;
    }

    public NarrowingTree(LowerBoundsToolbox toolbox, TRSFunctionApplication startTerm, Abortion abortion) {
        this(toolbox, new SingleStepNarrower(toolbox), startTerm, abortion);
    }

    public boolean enlarge(int depth) {
        boolean finished = this.finished();
        // build the narrowing tree, but stop heuristically to avoid timeouts and out-of-memory errors
        while (!finished
                // make sure that the narrowing tree is only extended up to the given depth
                && this.depth() < depth
                // if the narrowing tree gets large (>= 250 nodes) only continue if it is 'slim' (not too many leaves)
                && !(this.size() >= 250 && this.numLeaves() * 10 >= this.size())
                // if there are 40 nodes or more to expand, stop
                && this.numToExpand() < 40) {
            this.abortion.checkAbortion();
            this.extend();
            finished = this.finished();
        }
        return finished;
    }

    private boolean finished() {
        List<NarrowingTree> todo = new ArrayList<>();
        todo.add(this);
        while (!todo.isEmpty()) {
            NarrowingTree current = todo.remove(0);
            if (current.children == null) {
                return false;
            } else {
                todo.addAll(current.children.values());
            }
        }
        return true;
    }

    private int depth() {
        List<Pair<NarrowingTree, Integer>> todo = new ArrayList<>();
        todo.add(new Pair<>(this, 1));
        int max = 1;
        while (!todo.isEmpty()) {
            Pair<NarrowingTree, Integer> current = todo.remove(0);
            NarrowingTree currentNode = current.x;
            int currentDepth = current.y;
            if (currentNode.children != null && !currentNode.children.isEmpty()) {
                if (currentDepth >= max) {
                    max = currentDepth + 1;
                }
                for (NarrowingTree child: currentNode.children.values()) {
                    todo.add(new Pair<>(child, currentDepth + 1));
                }
            }
        }
        return max;
    }

    public int numLeaves() {
        List<NarrowingTree> todo = new ArrayList<>();
        int res = 0;
        todo.add(this);
        while (!todo.isEmpty()) {
            NarrowingTree current = todo.remove(0);
            if (current.children == null || current.children.isEmpty()) {
                res++;
            } else if (current.children != null) {
                todo.addAll(current.children.values());
            }
        }
        return res;
    }

    public List<RewriteSequence> all() {
        List<Pair<RewriteSequence, NarrowingTree>> todo = new ArrayList<>();
        List<RewriteSequence> res = new ArrayList<>();
        todo.add(new Pair<>(new RewriteSequence((TRSFunctionApplication) this.term, this.toolbox), this));
        while (!todo.isEmpty()) {
            Pair<RewriteSequence, NarrowingTree> p = todo.remove(0);
            RewriteSequence seq = p.x;
            NarrowingTree current = p.y;
            res.add(seq);
            if (current.children != null) {
                for (Entry<RewriteStep, NarrowingTree> e: current.children.entrySet()) {
                    RewriteStep step = e.getKey();
                    NarrowingTree child = e.getValue();
                    todo.add(new Pair<>(seq.addStep(step), child));
                }
            }
        }
        return res;
    }

    public int numToExpand() {
        List<NarrowingTree> todo = new ArrayList<>();
        int res = 0;
        todo.add(this);
        while (!todo.isEmpty()) {
            NarrowingTree current = todo.remove(0);
            if (current.children == null) {
                res++;
            } else {
                todo.addAll(current.children.values());
            }
        }
        return res;
    }

    public int size() {
        List<NarrowingTree> todo = new ArrayList<>();
        todo.add(this);
        int size = 0;
        while (!todo.isEmpty()) {
            NarrowingTree current = todo.remove(0);
            size++;
            if (current.children != null) {
                todo.addAll(current.children.values());
            }
        }
        return size;
    }

    public List<RewriteSequence> normalForms() {
        List<Pair<RewriteSequence, NarrowingTree>> todo = new ArrayList<>();
        List<RewriteSequence> res = new ArrayList<>();
        todo.add(new Pair<>(new RewriteSequence((TRSFunctionApplication) this.term, this.toolbox), this));
        while (!todo.isEmpty()) {
            Pair<RewriteSequence, NarrowingTree> p = todo.remove(0);
            RewriteSequence seq = p.x;
            NarrowingTree current = p.y;
            if (current.children != null) {
                if (current.children.isEmpty()) {
                    res.add(seq);
                } else {
                    for (Entry<RewriteStep, NarrowingTree> e: current.children.entrySet()) {
                        RewriteStep step = e.getKey();
                        NarrowingTree child = e.getValue();
                        todo.add(new Pair<>(seq.addStep(step), child));
                    }
                }
            }
        }
        return res;
    }

    private void extend() {
        getChildren().stream().forEach(x -> x.narrow());
    }

    private List<NarrowingTree> getChildren() {
        Stack<NarrowingTree> todo = new Stack<>();
        List<NarrowingTree> res = new ArrayList<>();
        todo.add(this);
        while (!todo.isEmpty()) {
            NarrowingTree current = todo.pop();
            if (current.children == null) {
                res.add(current);
            } else {
                current.children.values().stream().forEach(todo::push);
            }
        }
        return res;
    }

    private void narrow() {
        this.children = new LinkedHashMap<>();
        this.toolbox.aborter.checkAbortion();
        // enforce innermost rewriting.
        Set<Position> sortedPositions = new TreeSet<>(new InnerMostPositionComparator());
        sortedPositions.addAll(this.term.getPositions());
        for (Position pos : sortedPositions) {
            this.abortion.checkAbortion();
            TRSTerm s = this.term.getSubterm(pos);
            // Do not try to rewrite a variable.
            if (s.isVariable()) {
                continue;
            }
            Set<RewriteStep> steps = this.singleStepNarrower.rewrite(this.term, pos);
            if (!steps.isEmpty()) {
                for (RewriteStep step : steps) {
                    TRSTerm newTerm = this.toolbox.pfHelper.normalize(step.getResult());
                    this.children.put(step, new NarrowingTree(this.toolbox, this.singleStepNarrower, newTerm, this.abortion));
                }
                break;
            }
        }
    }

}
