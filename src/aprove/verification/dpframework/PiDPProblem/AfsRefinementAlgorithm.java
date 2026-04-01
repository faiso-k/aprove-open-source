package aprove.verification.dpframework.PiDPProblem;

import java.util.*;

import aprove.*;
import aprove.input.Programs.prolog.processors.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class AfsRefinementAlgorithm {
    /*- refinement algorithm -------------------------------------------------*/

    public static Afs refineArgumentFilter(Afs Pi,
        Set<GeneralizedRule> P,
        Set<GeneralizedRule> R,
        RefinementHeuristic tau) {
        if (Globals.useAssertions) {
            assert Pi != null && P != null && R != null && tau != null;
        }
        Afs Pi_prime = new Afs();
        Pi_prime.setFiltering(Pi);

        Set<GeneralizedRule> PcupR = new LinkedHashSet<GeneralizedRule>(P);
        PcupR.addAll(R);

        boolean tryToRefine = true;
        while (tryToRefine) {
            tryToRefine = false;
            for (GeneralizedRule rule : PcupR) {
                tryToRefine =
                    AfsRefinementAlgorithm.refineArgumentFilter(Pi_prime, rule,
                        tau)
                        || tryToRefine;
            }
        }

        return Pi_prime;
    }

    private static boolean refineArgumentFilter(Afs Pi,
        GeneralizedRule rule,
        RefinementHeuristic tau) {
        Set<TRSVariable> lvars = Pi.filterTerm(rule.getLeft()).getVariables();
        Set<TRSVariable> rvars = Pi.filterTerm(rule.getRight()).getVariables();
        Set<TRSVariable> evilVars = new LinkedHashSet<TRSVariable>(rvars);
        evilVars.removeAll(lvars);
        if (!evilVars.isEmpty()
            && rule.getRight() instanceof TRSFunctionApplication) {
            Set<Pair<FunctionSymbol, Integer>> refinedPositions =
                new LinkedHashSet<Pair<FunctionSymbol, Integer>>();
            AfsRefinementAlgorithm.refineArgumentFilter(Pi,
                (TRSFunctionApplication) rule.getRight(), evilVars, tau,
                refinedPositions);
            AfsRefinementAlgorithm.removeUnnecessaryFiltering(Pi,
                rule.getRight(), evilVars, refinedPositions);
            return true;
        }
        return false;
    }

    private static void refineArgumentFilter(Afs Pi,
        TRSFunctionApplication rhs,
        Set<TRSVariable> evilVars,
        RefinementHeuristic tau,
        Set<Pair<FunctionSymbol, Integer>> refinedPositions) {
        Set<Position> evilPositions =
            AfsRefinementAlgorithm.getEvilPositions(rhs, evilVars);

        for (Position pos : evilPositions) {
            Pair<FunctionSymbol, Integer> refinePosition =
                tau.getSymbolArgumentToFilter(rhs, pos);
            refinedPositions.add(refinePosition);
            Pi.setFiltering(refinePosition.x, refinePosition.y.intValue(),
                YNM.NO);
        }
    }

    public static void removeUnnecessaryFiltering(Afs Pi,
        TRSTerm t,
        Set<TRSVariable> evilVariables,
        Set<Pair<FunctionSymbol, Integer>> refinedPositions) {
        Set<TRSVariable> variables;
        for (Pair<FunctionSymbol, Integer> refinedPosition : refinedPositions) {
            Pi.setFiltering(refinedPosition.x, refinedPosition.y.intValue(),
                YNM.YES);
            variables = Pi.filterTerm(t).getVariables();
            variables.retainAll(evilVariables);
            if (!variables.isEmpty()) {
                Pi.setFiltering(refinedPosition.x,
                    refinedPosition.y.intValue(), YNM.NO);
            }
        }
    }

    private static Set<Position> getEvilPositions(TRSFunctionApplication rhs,
        Set<TRSVariable> evilVars) {
        Set<Position> positions = rhs.getPositions(), evilPositions =
            new LinkedHashSet<Position>();
        for (Position pos : positions) {
            TRSTerm t = rhs.getSubterm(pos);
            if (t.isVariable() && evilVars.contains(t)) {
                evilPositions.add(pos);
            }
        }
        return evilPositions;
    }

    /*- refinement heuristic -------------------------------------------------*/

    public interface RefinementHeuristic {
        public Pair<FunctionSymbol, Integer> getSymbolArgumentToFilter(TRSFunctionApplication t,
            Position pos);
    }

    public static class ImprovedTypeBasedRefinementHeuristic implements
            RefinementHeuristic {
        private TypeGraph graph;

        public ImprovedTypeBasedRefinementHeuristic(TypeGraph graph) {
            this.graph = graph;
        }

        @Override
        public Pair<FunctionSymbol, Integer> getSymbolArgumentToFilter(TRSFunctionApplication t,
            Position pos) {
            int regardedDepth = 0;
            FunctionSymbol root = t.getRootSymbol();
            if (!root.getName().toLowerCase().contains(PrologFNG.IN)
                && !root.getName().toLowerCase().contains(PrologFNG.OUT)
                && pos.firstIndex() + 1 == root.getArity()) {
                /* never filter last argument of u_i or U_i */
                regardedDepth = 1;
            }

            Position parent = pos.shorten(1);
            FunctionSymbol f =
                ((TRSFunctionApplication) t.getSubterm(parent)).getRootSymbol();
            int i = pos.lastIndex();

            while (parent.getDepth() > regardedDepth
                && this.graph.isRecursive(f, pos.lastIndex())) {
                pos = parent;
                parent = parent.shorten(1);
                f =
                    ((TRSFunctionApplication) t.getSubterm(parent)).getRootSymbol();
                i = pos.lastIndex();
            }

            return new Pair<FunctionSymbol, Integer>(f, i);
        }
    }

    /*- type -----------------------------------------------------------------*/

    public static class TypeGraph {
        private Graph<TypeEntity, Object> graph;
        private Set<FuncPosEntity> recursive;

        public TypeGraph(Set<GeneralizedRule> R) {
            this.graph = new Graph<TypeEntity, Object>();
            this.buildGraph(R);
        }

        public TypeGraph(Set<GeneralizedRule> P, Set<GeneralizedRule> R) {
            this.graph = new Graph<TypeEntity, Object>();
            Set<GeneralizedRule> PcupR = new LinkedHashSet<GeneralizedRule>(P);
            PcupR.addAll(R);
            this.buildGraph(PcupR);
        }

        private void buildGraph(Set<GeneralizedRule> R) {
            for (GeneralizedRule rule : R) {
                this.buildGraph(rule.getLeft(), rule);
                this.buildGraph(rule.getRight(), rule);
            }
        }

        private void buildGraph(TRSTerm term, GeneralizedRule rule) {
            if (!term.isVariable()) {
                TRSFunctionApplication fApp = (TRSFunctionApplication) term;
                FunctionSymbol fSym = fApp.getRootSymbol();
                ImmutableList<? extends TRSTerm> args = fApp.getArguments();
                for (int i = 0; i < fSym.getArity(); i++) {
                    TRSTerm arg = args.get(i);
                    TypeEntity e1 = new FuncPosEntity(fSym, i);
                    TypeEntity e2 = this.getEntity(arg, rule);
                    Node<TypeEntity> n1 = this.graph.getNodeFromObject(e1);
                    Node<TypeEntity> n2 = this.graph.getNodeFromObject(e2);
                    if (n1 == null) {
                        n1 = new Node<TypeEntity>(e1);
                    }
                    if (n2 == null) {
                        n2 = new Node<TypeEntity>(e2);
                    }
                    this.graph.addEdge(n1, n2);
                    this.graph.addEdge(n2, n1);
                    this.buildGraph(arg, rule);
                }
            }
        }

        private TypeEntity getEntity(TRSTerm term, GeneralizedRule rule) {
            if (term.isVariable()) {
                return new VarRuleEntity((TRSVariable) term, rule);
            }
            return new FuncEntity(((TRSFunctionApplication) term).getRootSymbol());
        }

        public Set<FuncPosEntity> getRecursiveFuncPos() {
            if (this.recursive != null) {
                return this.recursive;
            }
            Set<FuncPosEntity> recursive = new LinkedHashSet<FuncPosEntity>();
            Set<FunctionSymbol> recursiveFuncs =
                new LinkedHashSet<FunctionSymbol>();
            Map<TypeEntity, Set<TypeEntity>> classes =
                this.getEquivalenceClasses();
            boolean changed = true;
            while (changed) {
                changed = false;
                for (Map.Entry<TypeEntity, Set<TypeEntity>> entry : classes.entrySet()) {
                    TypeEntity key = entry.getKey();
                    if (key instanceof FuncPosEntity) {
                        FuncPosEntity fpKey = (FuncPosEntity) key;
                        if (!recursive.contains(fpKey)) {
                            for (TypeEntity entity : entry.getValue()) {
                                if (entity instanceof FuncEntity) {
                                    FuncEntity fValue = (FuncEntity) entity;
                                    if (fpKey.f.equals(fValue.f)
                                        || recursiveFuncs.contains(fValue.f)) {
                                        recursive.add(fpKey);
                                        recursiveFuncs.add(fpKey.f);
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            this.recursive = recursive;
            return recursive;
        }

        public Map<TypeEntity, Set<TypeEntity>> getEquivalenceClasses() {
            Map<TypeEntity, Set<TypeEntity>> result =
                new LinkedHashMap<TypeEntity, Set<TypeEntity>>();
            for (Cycle<TypeEntity> cycle : this.graph.getSCCs(false)) {
                Set<TypeEntity> eClass = new LinkedHashSet<TypeEntity>();
                for (Node<TypeEntity> node : cycle) {
                    TypeEntity entity = node.getObject();
                    if (entity instanceof FuncEntity
                        || entity instanceof FuncPosEntity) {
                        eClass.add(entity);
                    }
                }
                for (TypeEntity entity : eClass) {
                    result.put(entity, eClass);
                }
            }
            return result;
        }

        public boolean isRecursive(FunctionSymbol f, int pos) {
            return this.getRecursiveFuncPos().contains(
                new FuncPosEntity(f, pos));
        }

        @Override
        public String toString() {
            return this.graph.toDOT();
        }
    }

    public interface TypeEntity {
    }

    public static class FuncPosEntity implements TypeEntity {
        private FunctionSymbol f;
        private int pos;

        public FuncPosEntity(FunctionSymbol f, int pos) {
            this.f = f;
            this.pos = pos;
        }

        @Override
        public String toString() {
            return this.f.getName() + "/" + this.pos;
        }

        @Override
        public boolean equals(Object o) {
            FuncPosEntity other = (FuncPosEntity) o;
            return this.pos == other.pos && this.f.equals(other.f);
        }

        @Override
        public int hashCode() {
            return this.pos + 101 * this.f.hashCode();
        }
    }

    public static class FuncEntity implements TypeEntity {
        private FunctionSymbol f;

        public FuncEntity(FunctionSymbol f) {
            this.f = f;
        }

        @Override
        public String toString() {
            return this.f.getName();
        }

        @Override
        public boolean equals(Object o) {
            FuncEntity other = (FuncEntity) o;
            return this.f.equals(other.f);
        }

        @Override
        public int hashCode() {
            return this.f.hashCode();
        }
    }

    public static class VarRuleEntity implements TypeEntity {
        private TRSVariable v;
        private GeneralizedRule rule;

        public VarRuleEntity(TRSVariable v, GeneralizedRule rule) {
            this.v = v;
            this.rule = rule;
        }

        @Override
        public String toString() {
            return this.v.getName() + "/" + this.rule;
        }

        @Override
        public boolean equals(Object o) {
            VarRuleEntity other = (VarRuleEntity) o;
            return this.v.equals(other.v) && this.rule.equals(other.rule);
        }

        @Override
        public int hashCode() {
            return this.v.hashCode() + 101 * this.rule.hashCode();
        }
    }

}
