package aprove.verification.dpframework.PiDPProblem;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import immutables.*;

public final class PiDPProblem extends AbstractPiDPProblem {

    /**
     * creates a QDP-problem
     * @param P
     * @param rWithQ
     * @param graph - the graph should be the (P,Q,R) dependency graph
     */
    private PiDPProblem(ImmutableSet<GeneralizedRule> P,
            AbstractPiTRSProblem rWithPi, PiDependencyGraph graph) {
        super("PiDP", "Pi-DP-Problem", P, rWithPi, graph);
    }

    public static PiDPProblem create(ImmutableSet<GeneralizedRule> P,
        AbstractPiTRSProblem rWithPi) {
        if (Globals.useAssertions) {
            assert rWithPi instanceof PiTRSProblem;
        }
        PiDependencyGraph graph = PiDependencyGraph.create(P, rWithPi);
        return new PiDPProblem(P, rWithPi, graph);
    }

    public PiDPProblem getSubProblem(ImmutableSet<GeneralizedRule> P) {
        Set<PiDPProblem> subProblems =
            (Set<PiDPProblem>) this.getSubProblems(P);
        return subProblems.iterator().next();
    }

    public PiDPProblem getSubProblem(PiDependencyGraph graph) {
        Set<PiDPProblem> subProblems =
            (Set<PiDPProblem>) this.getSubProblems(graph);
        return subProblems.iterator().next();
    }

    @Override
    public String export(Export_Util o) {
        StringBuffer s = new StringBuffer();
        s.append(o.export("Pi DP problem:"));
        s.append(o.cond_linebreak());
        if (this.getP().isEmpty()) {
            s.append("P is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS P consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.getP(), Export_Util.RULES));
            s.append(o.cond_linebreak());
        }
        if (this.getRwithPi().getR().isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.getRwithPi().getR(), Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        if (this.getRwithPi().getPi().isEmpty()) {
            s.append("Pi is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The argument filtering Pi contains the following mapping:"));
            s.append(o.cond_linebreak());
            s.append(o.export(this.getRwithPi().getPi()));
            s.append(o.cond_linebreak());
        }

        s.append(o.export("We have to consider all (P,R,Pi)-chains"));

        return s.toString();
    }

    @Override
    protected AbstractPiDPProblem createProblem(ImmutableSet<GeneralizedRule> P,
        AbstractPiTRSProblem rWithPi,
        PiDependencyGraph graph) {
        return new PiDPProblem(P, rWithPi, graph);
    }

    @Override
    protected Set<PiDPProblem> getSubProblems(ImmutableSet<GeneralizedRule> P,
        PiDependencyGraph graph) {
        if (Globals.useAssertions) {
            assert (graph.getP().equals(P));
            assert (this.getP().containsAll(P));
            assert (this.getP().size() != P.size());
        }
        Set<FunctionSymbol> sig =
            CollectionUtils.getFunctionSymbols(this.getRwithPi().getR());
        sig.addAll(CollectionUtils.getFunctionSymbols(P));
        Afs newPi = this.getRwithPi().getPi().reduceToSignature(sig);
        PiTRSProblem pitrs =
            PiTRSProblem.create(this.getRwithPi().getR(), new ImmutableAfs(
                newPi));
        Set<PiDPProblem> subProblems = new LinkedHashSet<PiDPProblem>();
        subProblems.add(new PiDPProblem(P, pitrs, graph));
        return subProblems;
    }

    /**
     * returns the same problem with a smaller argument filtering
     */
    @Override
    public AbstractPiDPProblem getSameProblem(ImmutableAfs Pi) {
        if (Globals.useAssertions) {
            assert Pi.isRefinementOf(this.getRwithPi().getPi()) == YNM.YES;
        }
        AbstractPiTRSProblem rWithPi =
            PiTRSProblem.create(this.getRwithPi().getR(), Pi);
        return this.createProblem(this.getP(), rWithPi,
            this.getDependencyGraph());
    }

    /**
     * returns a subproblem with smaller R
     */
    @Override
    public AbstractPiDPProblem getSubProblemWithSmallerR(ImmutableSet<GeneralizedRule> R) {
        if (Globals.useAssertions) {
            assert (this.getRwithPi().getR().containsAll(R));
        }
        Set<FunctionSymbol> sig = CollectionUtils.getFunctionSymbols(R);
        sig.addAll(CollectionUtils.getFunctionSymbols(this.getP()));
        Afs newPi = this.getRwithPi().getPi().reduceToSignature(sig);
        AbstractPiTRSProblem pitrs =
            PiTRSProblem.create(R, new ImmutableAfs(newPi));
        PiDependencyGraph subGraph =
            this.getDependencyGraph().getSubGraph(this.getP(), pitrs.getR());
        return this.createProblem(this.getP(), pitrs, subGraph);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return null;
    }
}
