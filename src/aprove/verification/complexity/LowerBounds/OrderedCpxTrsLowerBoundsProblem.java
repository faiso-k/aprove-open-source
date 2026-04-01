package aprove.verification.complexity.LowerBounds;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.GeneratorEquations.*;
import aprove.verification.complexity.LowerBounds.Util.Renaming.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.complexity.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;


public class OrderedCpxTrsLowerBoundsProblem extends CpxTrsLowerBoundsProblem {

    private DependencyGraph<LowerBoundsTrs> order;
    private GeneratorEquations generatorEquations;
    private Cycle<FunctionSymbol> scc;
    private LinkedHashSet<FunctionSymbol> todo;
    private TRSFunctionApplication arbitraryTerm;

    public OrderedCpxTrsLowerBoundsProblem(LowerBoundsTrs trs,
            RenamingCentral renamingCentral,
            DependencyGraph<LowerBoundsTrs> order,
            GeneratorEquations generatorEquations,
            TRSFunctionApplication arbitraryTerm) {
        super(trs, renamingCentral);
        this.order = order;
        this.generatorEquations = generatorEquations;
        this.todo = new LinkedHashSet<>();
        this.arbitraryTerm = arbitraryTerm;
        this.init();
    }

    private OrderedCpxTrsLowerBoundsProblem(LowerBoundsTrs trs,
            RenamingCentral renamingCentral,
            DependencyGraph<LowerBoundsTrs> order,
            Cycle<FunctionSymbol> scc,
            LinkedHashSet<FunctionSymbol> todo,
            GeneratorEquations generatorEquations,
            TRSFunctionApplication arbitraryTerm) {
        super(trs, renamingCentral);
        this.order = order;
        this.scc = scc;
        this.todo = todo;
        this.generatorEquations = generatorEquations;
        this.arbitraryTerm = arbitraryTerm;
        if (scc == null) {
            assert todo.isEmpty();
            this.init();
        }
    }

    private void init() {
        FunctionSymbol current = this.lookForLeaf();
        if (current == null) {
            this.scc = this.lookForSCC();
            if (this.scc != null) {
                this.todo.addAll(this.scc.getNodeObjects());
            }
        } else {
            this.todo.add(current);
        }
    }

    public GeneratorEquations getGeneratorEquations() {
        return this.generatorEquations;
    }

    @Override
    public String getStrategyName() {
        return "cpxlowerboundsiterative";
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new ComplexityProofPurposeDescriptor(this, "Lowerbounds for Runtime Complexity (innermost)");
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder sb = new StringBuilder(super.export(eu));
        sb.append(eu.paragraph());
        sb.append(eu.escape("Generator Equations:"));
        sb.append(eu.linebreak());
        sb.append(this.generatorEquations.export(eu));
        sb.append(eu.paragraph());
        if (this.isEmpty()) {
            sb.append(eu.escape("No more defined symbols left to analyse."));
            return sb.toString();
        }
        sb.append(eu.escape("The following defined symbols remain to be analysed:"));
        sb.append(eu.linebreak());
        Iterator<Node<FunctionSymbol>> it = this.order.getNodes().iterator();
        FunctionSymbol current = this.getCurrent();
        sb.append(current.export(eu));
        while (it.hasNext()) {
            Node<FunctionSymbol> n = it.next();
            FunctionSymbol f = n.getObject();
            if (f.equals(current)) {
                continue;
            }
            if (this.scc != null && this.scc.contains(n) && !this.todo.contains(f)) {
                continue;
            }
            sb.append(eu.escape(", "));
            sb.append(f.export(eu));
        }
        String orderStr = this.order.export(eu);
        if (!orderStr.isEmpty()) {
            sb.append(eu.paragraph());
            sb.append(eu.escape("They will be analysed ascendingly in the following order:"));
            sb.append(eu.linebreak());
            sb.append(orderStr);
        }
        return sb.toString();
    }

    private FunctionSymbol lookForLeaf() {
        for (Node<FunctionSymbol> node : this.order.getNodes()) {
            if (this.order.getOut(node).isEmpty()) {
                return node.getObject();
            }
        }
        return null;
    }

    private Cycle<FunctionSymbol> lookForSCC() {
        Set<Cycle<FunctionSymbol>> sccs = this.order.getSCCs();
        if (!sccs.isEmpty()) {
            return sccs.iterator().next();
        } else {
            return null;
        }
    }

    public OrderedCpxTrsLowerBoundsProblem next(LowerBoundsTrs newTrs) {
        FunctionSymbol current = this.getCurrent();
        LinkedHashSet<FunctionSymbol> newTodo = new LinkedHashSet<>(this.todo);
        newTodo.remove(current);
        Cycle<FunctionSymbol> newScc = this.scc;
        DependencyGraph<LowerBoundsTrs> newGraph = this.order.clone();
        if (newScc != null) {
            if (newTrs.numberOfLemmas() > this.getTrs().numberOfLemmas()) {
                newTodo.addAll(newScc.getNodeObjects());
                newTodo.remove(current);
            }
            if (newTodo.isEmpty()) {
                newGraph.removeAllNodes(newScc);
                newScc = null;
            }
        } else {
            newGraph.remove(current);
        }
        OrderedCpxTrsLowerBoundsProblem res = new OrderedCpxTrsLowerBoundsProblem(newTrs, this.getRenamingCentral(), newGraph, newScc, newTodo, this.generatorEquations, this.arbitraryTerm);
        return res;
    }

    public OrderedCpxTrsLowerBoundsProblem empty(LowerBoundsTrs newTrs) {
        LinkedHashSet<FunctionSymbol> newTodo = new LinkedHashSet<>();
        return new OrderedCpxTrsLowerBoundsProblem(newTrs, this.getRenamingCentral(), new DependencyGraph<>(), null, newTodo, this.generatorEquations, this.arbitraryTerm);
    }

    public boolean isEmpty() {
        return this.order.getNodes().isEmpty();
    }

    public FunctionSymbol getCurrent() {
        return this.todo.iterator().next();
    }

    public ComplexityValue getRes() {
        return this.getTrs().getComplexity();
    }

    public TRSFunctionApplication getArbitraryTerm() {
        return this.arbitraryTerm;
    }

}
