package aprove.verification.complexity.CdtProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.AcdtProblem.Utils.*;
import aprove.verification.complexity.CdpProblem.Processors.Util.QtrsDirectGcdp.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CdtProblem.Utils.*;
import aprove.verification.complexity.CdtProblem.Utils.IcapCalculator;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class CdtNarrowingProcessor extends CdtTransformationProcessor{

    private final boolean normalCheck;

    private final boolean strongSubsumes;

    @ParamsViaArgumentObject
    public CdtNarrowingProcessor(Arguments args) {
        super(args);
        this.normalCheck = args.normalCheck;
        this.strongSubsumes = args.strongSubsumes;
    }

    @Override
    protected Transformation computeTransformation(State st, Node<Cdt> node) {
        BitSet allowedRhsArgs = this.findAllowedRhsArgs(st, node);

        if (allowedRhsArgs.isEmpty()) {
            return null;
        }

        UsableRulesCalculator urCalc= st.cdtProblem.getURCalc();
        IcapCalculator icap = st.cdtGraph.getIcap();
        Cdt nodeCdt = icap.renameWithCapInput(node.getObject());

        Pair<Integer, List<NarrowingPos>> narrowables =
            this.getNarrowables(nodeCdt, allowedRhsArgs, urCalc);
        if (narrowables == null) {
            return null;
        }

        Set<Cdt> tupleNarrowings = new LinkedHashSet<Cdt>();
        for (NarrowingPos narrowable : narrowables.y) {
            Cdt tupleNarrowing = this.computeNarrowing(nodeCdt, narrowable);
            tupleNarrowings.add(tupleNarrowing);
        }

        BitSet bs = this.findSubsumed(st.cdtProblem, nodeCdt, narrowables);
        if (bs.cardinality() < nodeCdt.getRuleRHSArgs().size()) {
            tupleNarrowings.add(nodeCdt.filter(bs));
        }

        Transformation result = new Transformation(false,
                GraphHistory.Technique.Narrowing, node, tupleNarrowings,
                new CdtNarrowingProof(node.getObject(), tupleNarrowings));
        return result;
    }

    private BitSet findSubsumed(CdtProblem cdtProblem, Cdt nodeCdt,
            Pair<Integer, List<NarrowingPos>> narrowed) {
        BitSet bs = new BitSet();
        bs.set(narrowed.x);
        if (!this.strongSubsumes) {
            return bs;
        }

        UsableRulesCalculator urCalc = cdtProblem.getGraph().getIcap().getURCalc();
        RuleSet<Rule> tupleRules = new RuleSet<Rule>();
        for (Cdt tuple : cdtProblem.getTuples()) {
            tupleRules.add(tuple.getRule().getWithRenumberedVariables(IcapAlgorithm.PREFIX_NOTCAP));
        }

        Set<TRSSubstitution> mgus = new HashSet<TRSSubstitution>();
        for (NarrowingPos np : narrowed.y) {
            mgus.add(np.mgu);
        }

        for (int i = 0; i < nodeCdt.getRuleRHSArgs().size(); i++) {
            if (i == narrowed.x) {
                continue;
            }
            TRSFunctionApplication rhsI = nodeCdt.getRuleRHSArgs().get(i);
            Rule cdtWithRhsI = Rule.create(nodeCdt.getRuleLHS(), rhsI);

            RuleSet<Rule> usableRules =
                new RuleSet<Rule>(urCalc.estimateUsableRules(cdtWithRhsI));

            List<NarrowingPos> narrowables = this.getNarrowables(nodeCdt, i, usableRules);
            narrowables = this.filterNormalForms(narrowables, nodeCdt, usableRules);

            /* Consider also tuples for computing the narrowables. We want
             * to know if _any_ rewrite step for this rhs needs a substitution
             * which is not an instance of any substitution used for the
             * narrowing transformation.
             *
             * Note that we may not filter non-normal forms w.r.t. tuples. */
            narrowables.addAll(this.getNarrowables(nodeCdt, i, tupleRules));

            boolean subsumed = true;
            outer: for (NarrowingPos np : narrowables) {
                for (TRSSubstitution mgu : mgus) {
                    if (np.mgu.isInstanceOf(mgu)) {
                        continue outer;
                    }
                }
                subsumed = false;
                break;
            }
            bs.set(i, subsumed);
        }
        return bs;
    }

    /**
     * Returns the indices of the RhsArgs of the Cdt in node, which do not
     * unify with any LHS of another Cdt in the graph
     * (in a way that the unified LHS is in normal form).
     */
    private BitSet findAllowedRhsArgs(State st, Node<Cdt> node) {
        BitSet allowedRhsArgs = new BitSet();
        Cdt nodeCdt = node.getObject();
        Cdt nodeCdtRen = Cdt.create(nodeCdt.getRule().getWithRenumberedVariables("x"));

        /* Which RHSArgs may be narrowed? */
        ImmutableList<TRSFunctionApplication> nodeCdtRenRhsArgs = nodeCdtRen.getRuleRHSArgs();
        allowedRhsArgs.set(0, nodeCdtRenRhsArgs.size());
        Set<Edge<BitSet,Cdt>> outEdges = st.graph.getOutEdges(node);
        for (Edge<BitSet,Cdt> edge : outEdges) {
            Cdt outNodeCdt = edge.getEndNode().getObject();
            TRSTerm outRenLhs = outNodeCdt.getRuleLHS().renumberVariables("y");
            BitSet conn = edge.getObject();
            for (int i = conn.nextSetBit(0); i >= 0; i = conn.nextSetBit(i+1)) {
                TRSSubstitution mgu = nodeCdtRenRhsArgs.get(i).getMGU(outRenLhs);
                if (mgu != null) {
                    TRSTerm substOutRenLhs = outRenLhs.applySubstitution(mgu);
                    if (!this.normalCheck
                            || st.cdtProblem.getR().termIsNormal(substOutRenLhs)) {
                        allowedRhsArgs.clear(i);
                    }
                }
            }
        }
        return allowedRhsArgs;
    }

    /**
     * Finds the first narrowable RHS and computes the position where this RHS
     * needs to be narrowed.
     *
     * Considers the normal form condition for lhs.
     */
    private Pair<Integer, List<NarrowingPos>> getNarrowables(Cdt cdt,
            BitSet allowedArgs, UsableRulesCalculator urCalc) {
        for (int i=allowedArgs.nextSetBit(0); i >= 0; i=allowedArgs.nextSetBit(i+1)) {
            Rule cdtWithRhsI = Rule.create(cdt.getRuleLHS(), cdt.getRuleRHSArgs().get(i));
            ImmutableRuleSet<Rule> usableRules =
                new ImmutableRuleSet<Rule>(urCalc.estimateUsableRules(cdtWithRhsI));

            List<NarrowingPos> narrowables = this.getNarrowables(cdt, i, usableRules);
            narrowables = this.filterNormalForms(narrowables, cdt, usableRules);
            if (narrowables != null) {
                return new Pair<Integer, List<NarrowingPos>>(i, narrowables);
            }
        }
        return null;
    }

    /**
     * Computes the positions where we need to narrow.
     */
    private List<NarrowingPos> getNarrowables(Cdt nodeCdt,
            int rhsArgIdx, RuleSet<Rule> usableRules) {
        List<NarrowingPos> narrowables =
            new ArrayList<NarrowingPos>();

        TRSFunctionApplication rhsArg = nodeCdt.getRuleRHSArgs().get(rhsArgIdx);
        for (TermIterator it = new TermIterator(rhsArg); it.hasNext();) {
            TermIterator.Entry e = it.next();
            TRSTerm t = e.getTerm();
            if (t.isVariable()) {
                continue;
            }

            TRSFunctionApplication fa = (TRSFunctionApplication)t;
            Set<Rule> rules =
                usableRules.getSubsetByRootSymbol(fa.getRootSymbol());
            for (Rule r : rules) {
                if (Globals.useAssertions) {
                    assert(Collections.disjoint(r.getLeft().getVariables(), fa.getVariables()));
                }
                TRSSubstitution mgu = r.getLeft().getMGU(fa);
                if (mgu != null) {
                    narrowables.add(new NarrowingPos(
                            rhsArgIdx, e.getPosition(), fa, r, mgu));
                }
            }
        }
        return narrowables;
    }

    private List<NarrowingPos> filterNormalForms(List<NarrowingPos> narrowables,
            Cdt nodeCdt, RuleSet<Rule> usableRules) {
        if (!this.normalCheck) {
            return narrowables;
        }

        List<NarrowingPos> result = new ArrayList<NarrowingPos>();
        TRSFunctionApplication lhs = nodeCdt.getRuleLHS();
        for (NarrowingPos np : narrowables) {
            TRSFunctionApplication substLhs = lhs.applySubstitution(np.mgu);
            if (usableRules.termIsNormal(substLhs)) {
                result.add(np);
            }
        }
        return result;
    }

    private Cdt computeNarrowing(Cdt cdt, NarrowingPos narrowable) {
        TRSTerm substRuleRhs = narrowable.r.getRight().applySubstitution(narrowable.mgu);
        TRSFunctionApplication substTupleLhs = cdt.getRuleLHS().applySubstitution(narrowable.mgu);
        TRSFunctionApplication substTupleRhs = cdt.getRuleRHS().applySubstitution(narrowable.mgu);
        Position p = narrowable.pos.prepend(narrowable.rhsArgNo);
        TRSTerm narrowedTupleRhs = substTupleRhs.replaceAt(p, substRuleRhs);
        return Cdt.create(Rule.create(substTupleLhs, narrowedTupleRhs));
    }

    static class CdtNarrowingProof extends CpxProof {

        private final Cdt oldCdt;
        private final Set<Cdt> newCdts;

        public CdtNarrowingProof(Cdt old, Set<Cdt> instantiations) {
            this.oldCdt = old;
            this.newCdts = instantiations;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append(o.escape("Use narrowing to replace "));
            sb.append(o.export(this.oldCdt));
            sb.append(o.escape(" by "));
            sb.append(o.set(this.newCdts, Export_Util.RULES));
            return sb.toString();
        }

    }

    static class NarrowingPos {
        public final int rhsArgNo;
        public final Position pos;
        public final TRSFunctionApplication t;
        public final Rule r;
        public final TRSSubstitution mgu;

        public NarrowingPos(int rhsArgNo, Position pos, TRSFunctionApplication t, Rule r, TRSSubstitution mgu) {
            this.rhsArgNo = rhsArgNo;
            this.pos = pos;
            this.t = t;
            this.r = r;
            this.mgu = mgu;

        }
    }

    public static class Arguments extends CdtTransformationProcessor.Arguments {
        /**
         * XXX: Only for benchmarking purposes. Can be removed later.
         */
        public boolean normalCheck = true;

        /**
         * XXX: Only for benchmarking purposes. Can be removed later.
         */
         public boolean strongSubsumes = true;
    }
}
