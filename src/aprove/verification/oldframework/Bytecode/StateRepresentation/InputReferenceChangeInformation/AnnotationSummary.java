package aprove.verification.oldframework.Bytecode.StateRepresentation.InputReferenceChangeInformation;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class AnnotationSummary {

    private boolean isMaybeExisting = false;
    private boolean isNonTree = false;
    private Set<HeapEdge> cyclicNeededEdges; //null means not cyclic, empty set means cyclic with no needed edges

    private Set<AbstractVariableReference> equalRefs = new HashSet<>();
    private Set<AbstractVariableReference> reachableRefs = new HashSet<>();

    protected AnnotationSummary() {}

    protected AnnotationSummary(AnnotationSummary original) {
        this.isMaybeExisting = original.isMaybeExisting;
        this.isNonTree = original.isNonTree;
        if (original.cyclicNeededEdges != null) {
            this.cyclicNeededEdges = new HashSet<>(original.cyclicNeededEdges);
        }
        this.equalRefs = new HashSet<>(original.equalRefs);
        this.reachableRefs = new HashSet<>(original.reachableRefs);
    }

    public static AnnotationSummary empty() {
        return new AnnotationSummary();
    }

    public static AnnotationSummary of(AbstractVariableReference ref, State state, HeapPositions heapPos) {
        AnnotationSummary res = new AnnotationSummary();
        if (ref.isNULLRef()) {
            res.setMaybeExisting(true);
            return res;
        }
        Pair<Set<AbstractVariableReference>, Set<AbstractVariableReference>> reachableRefs = AnnotationFixups.getRightSquigArrow(ref, false, state);
        if (state.getHeapAnnotations().isMaybeExisting(ref)) {
            res.setMaybeExisting(true);
        }
        res.reachabilityAnalysis(state, ref, reachableRefs.x, reachableRefs.y);
        res.shapeAnalysis(state, heapPos, ref, reachableRefs.x);
        return res;
    }

    private void reachabilityAnalysis(State state, AbstractVariableReference ref,
            Collection<AbstractVariableReference> concreteReachableRefs,
            Collection<AbstractVariableReference> abstractReachableRefs) {
        HeapAnnotations annotations = state.getHeapAnnotations();

        //first look at the annotations of the reference itself
        this.equalRefs.addAll(annotations.getEqualityGraph().getPartners(ref));
        this.reachableRefs.addAll(annotations.getJoiningStructures().getReferencesWithPartner(ref));

        //second all reachable through concrete links
        this.reachableRefs.addAll(concreteReachableRefs);
        //finally those reachable through concrete links and one equality or joins annotations
        this.reachableRefs.addAll(abstractReachableRefs);
    }

    private void shapeAnalysis(State state, HeapPositions heapPos, AbstractVariableReference ref, Collection<AbstractVariableReference> reachableRefs) {
        reachableRefs = new HashSet<>(reachableRefs);
        reachableRefs.add(ref);
        HeapAnnotations annotations = state.getHeapAnnotations();
        CyclicStructures cyclicStructures = annotations.getCyclicStructures();

        //first check the annotaions of the reference and reachable references
        for (AbstractVariableReference r : reachableRefs) {
            if (annotations.isPossiblyNonTree(r)) {
                this.isNonTree = true;
            }
            if (cyclicStructures.isCyclic(r)) {
                this.setCyclic(cyclicStructures.getNeededEdgesOf(r));
            }
        }

        //next look for concrete nonTree and Cyclic Shapes, code adapted from PathMerger
        final CollectionMap<AbstractVariableReference, StatePosition> refsWithMultiplePositions =
                heapPos.getRefsWithMultiplePositions();
        for (final Map.Entry<AbstractVariableReference, Collection<StatePosition>> e : refsWithMultiplePositions
                .entrySet())
        {
            if (!reachableRefs.contains(e.getKey())) {
                continue;
            }

            for (final Pair<StatePosition, StatePosition> pair : Collection_Util.getPairs(e.getValue())) {
                final StatePosition posOne = pair.x;
                final StatePosition posTwo = pair.y;

                final StatePosition nonTreeStartPos = posOne.getMaxCommonPrefix(posTwo);

                if (nonTreeStartPos == null) {
                    /*
                     * No common prefix, just two paths leading to the
                     * same reference. This is handled when introducing
                     * possible equality/joins (Def. 2g)
                     */
                    continue;
                }

                if (!reachableRefs.contains(heapPos.getReferenceForPos(nonTreeStartPos))) {
                    continue;
                }

                this.isNonTree = true;
                if (nonTreeStartPos.equals(posOne)) {
                    this.setCyclic(posTwo.getEdgesTo(nonTreeStartPos));
                } else if (nonTreeStartPos.equals(posTwo)) {
                    this.setCyclic(posOne.getEdgesTo(nonTreeStartPos));
                }
            }
        }
    }

    public AnnotationSummary copy() {
        return new AnnotationSummary(this);
    }

    public AnnotationSummary merge(AnnotationSummary other) {
        AnnotationSummary res = this.copy();
        if (other.isMaybeExisting()) {
            res.setMaybeExisting(true);
        }
        if (other.isNonTree()) {
            res.setNonTree();
        }
        if (other.isCyclic()) {
            res.setCyclic(other.getCyclicNeededEdges());
        }
        res.addEqualRefs(other.getEqualRefs());
        res.addReachableRefs(other.getReachableRefs());
        return res;
    }

    public boolean isMaybeExisting() {
        return this.isMaybeExisting;
    }

    public void setMaybeExisting(boolean maybeExisting) {
        this.isMaybeExisting = maybeExisting;
    }

    public boolean isNonTree() {
        return this.isNonTree;
    }

    public void setNonTree() {
        this.isNonTree = true;
    }

    public boolean isCyclic() {
        return this.cyclicNeededEdges != null;
    }

    public Set<HeapEdge> getCyclicNeededEdges() {
        return this.cyclicNeededEdges;
    }

    public void setCyclic(Collection<HeapEdge> cyclicNeededEdges) {
        this.isNonTree = true;
        if (this.cyclicNeededEdges == null) {
            this.cyclicNeededEdges = new HashSet<>(cyclicNeededEdges);
        } else {
            this.cyclicNeededEdges.retainAll(cyclicNeededEdges);
        }
    }

    public Set<AbstractVariableReference> getEqualRefs() {
        return this.equalRefs;
    }

    public void addEqualRef(AbstractVariableReference equalRef) {
        this.equalRefs.add(equalRef);
    }

    public void addEqualRefs(Collection<AbstractVariableReference> equalRefs) {
        this.equalRefs.addAll(equalRefs);
    }

    public Set<AbstractVariableReference> getReachableRefs() {
        return this.reachableRefs;
    }

    public void addReachableRef(AbstractVariableReference reachableRef) {
        this.reachableRefs.add(reachableRef);
    }
    public void addReachableRefs(Collection<AbstractVariableReference> reachableRefs) {
        this.reachableRefs.addAll(reachableRefs);
    }

    public void addAnnotationsTo(AbstractVariableReference ref, State state) {
        HeapAnnotations annotations = state.getHeapAnnotations();
        if (this.isMaybeExisting) {
            annotations.setMaybeExisting(ref);
        }
        if (this.isNonTree) {
            annotations.setPossiblyNonTree(ref);
        }
        if (this.isCyclic()) {
            annotations.setPossiblyCyclic(ref, this.cyclicNeededEdges);
        }
        for (AbstractVariableReference partner : this.equalRefs) {
            annotations.getEqualityGraph().addPossibleEquality(state, ref, partner);
        }
        for (AbstractVariableReference partner : this.reachableRefs) {
            annotations.getJoiningStructures().add(ref, partner);
        }
    }

    public boolean contains(AnnotationSummary other) {
        if (other.isMaybeExisting() && !this.isMaybeExisting()) {
            return false;
        }
        if (other.isNonTree() && !this.isNonTree()) {
            return false;
        }
        if (other.isCyclic() && !this.isCyclic()) {
            return false;
        }
        if (other.isCyclic() && !other.getCyclicNeededEdges().containsAll(this.getCyclicNeededEdges())) {
            return false;
        }
        if (!this.equalRefs.containsAll(other.equalRefs)) {
            return false;
        }
        if (!this.reachableRefs.containsAll(other.reachableRefs)) {
            return false;
        }
        return true;
    }

    public AnnotationSummary withEqualsAsReachable() {
        AnnotationSummary res = this.copy();
        res.reachableRefs.addAll(res.equalRefs);
        res.equalRefs.clear();
        return res;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.cyclicNeededEdges == null) ? 0 : this.cyclicNeededEdges.hashCode());
        result = prime * result + ((this.equalRefs == null) ? 0 : this.equalRefs.hashCode());
        result = prime * result + (this.isMaybeExisting ? 1231 : 1237);
        result = prime * result + (this.isNonTree ? 1231 : 1237);
        result = prime * result + ((this.reachableRefs == null) ? 0 : this.reachableRefs.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        AnnotationSummary other = (AnnotationSummary) obj;
        if (this.cyclicNeededEdges == null) {
            if (other.cyclicNeededEdges != null) {
                return false;
            }
        } else if (!this.cyclicNeededEdges.equals(other.cyclicNeededEdges)) {
            return false;
        }
        if (this.equalRefs == null) {
            if (other.equalRefs != null) {
                return false;
            }
        } else if (!this.equalRefs.equals(other.equalRefs)) {
            return false;
        }
        if (this.isMaybeExisting != other.isMaybeExisting) {
            return false;
        }
        if (this.isNonTree != other.isNonTree) {
            return false;
        }
        if (this.reachableRefs == null) {
            if (other.reachableRefs != null) {
                return false;
            }
        } else if (!this.reachableRefs.equals(other.reachableRefs)) {
            return false;
        }
        return true;
    }

}
