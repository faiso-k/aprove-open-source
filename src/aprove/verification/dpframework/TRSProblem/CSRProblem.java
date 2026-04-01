package aprove.verification.dpframework.TRSProblem;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Output.*;
import aprove.xml.*;
import immutables.*;

public class CSRProblem extends DefaultBasicObligation {

    // real values

    private final ImmutableSet<Rule> R;
    private final boolean innermost;
    private final ImmutableMap<FunctionSymbol, ImmutableSet<Integer>> replacementMap;

    // computed / cached values

    private volatile YNM orthogonal;

    private CSRProblem(final ImmutableSet<Rule> R, final ImmutableMap<FunctionSymbol, ImmutableSet<Integer>> replacementMap, final boolean innermost, final YNM orthogonal) {
        super("CSR", "CSR");
        this.R = ImmutableCreator.create(R);
        this.innermost = innermost;
        this.replacementMap = replacementMap;
        this.orthogonal = orthogonal;
    }

    private final static ImmutableSet<Integer> EMPTY_SET = ImmutableCreator.create(new TreeSet<Integer>());

    /**
     * creates a new CSR provided that all function symbols occurring in R are also present
     * in the replacement map. If some entry is missing, a runtime exception is thrown
     * @param R
     * @param replacementMap
     * @param innermost
     * @return
     */
    public static CSRProblem create(final Set<Rule> R, final Map<FunctionSymbol, Set<Integer>> replacementMap, final boolean innermost) {
        final Map<FunctionSymbol, ImmutableSet<Integer>> map = new LinkedHashMap<FunctionSymbol, ImmutableSet<Integer>>();
        for (final FunctionSymbol f : CollectionUtils.getFunctionSymbols(R)) {
            final Set<Integer> replacement = replacementMap.get(f);
            ImmutableSet<Integer> immReplacement;
            if (replacement == null) {
                if (f.getArity() == 0) {
                    immReplacement = CSRProblem.EMPTY_SET;
                } else {
                    throw new RuntimeException("invalid CSR for creation, missing rep-map entry for function symbol "+f);
                }
            } else {
                immReplacement = ImmutableCreator.create(new TreeSet<Integer>(replacement));
            }
            map.put(f, immReplacement);
        }
        return new CSRProblem(ImmutableCreator.create(R), ImmutableCreator.create(map), innermost, YNM.MAYBE);
    }

    /**
     * creates an innermost problem from an original problem, where
     * only the strategy is modified to innermost.
     * @param origin
     * @return
     */
    public static CSRProblem createInnermost(final CSRProblem origin) {
        return new CSRProblem(origin.R, origin.replacementMap, true, origin.orthogonal);
    }

    /**
     * Creates a subproblem of this (the rule set gets smaller, everthing else is
     * unchanged).
     *
     * @param rule a subset of the set of rules of this, to be used as the set
     *  of rules of the new subproblem
     * @return
     */
    public CSRProblem createSubProblem(final ImmutableSet<Rule> rules) {
        if (Globals.useAssertions) {
            assert(this.R.containsAll(rules));
        }
        if (this.R.size() == rules.size()) {
            if (Globals.DEBUG_THIEMANN || Globals.DEBUG_FUHS) {
                System.out.println("Warning: createSubProblem in CSR produces identity");
            }
            return this;
        }

        // reduce mu to remaining function symbols
        final Set<FunctionSymbol> fSyms = CollectionUtils.getFunctionSymbols(rules);
        Map<FunctionSymbol, ImmutableSet<Integer>> newMu;
        newMu = new LinkedHashMap<FunctionSymbol, ImmutableSet<Integer>>(this.replacementMap);
        newMu.keySet().retainAll(fSyms);

        ImmutableMap<FunctionSymbol, ImmutableSet<Integer>> newImmMu;
        newImmMu = newMu.size() == this.replacementMap.size()
            ? this.replacementMap : ImmutableCreator.create(newMu);

        // deleting a rule might lead to orthogonality,
        // but it cannot destroy orthogonality
        final YNM newOrthogonal = this.orthogonal == YNM.YES ? YNM.YES : YNM.MAYBE;
        return new CSRProblem(rules, newImmMu, this.innermost, newOrthogonal);
    }

    public ImmutableSet<Rule> getR() {
        return this.R;
    }

    public Set<FunctionSymbol> getSignature() {
        return this.replacementMap.keySet();
    }

    /**
     * computes (or returns cached value) whether this CSR is orthogonal,
     * i.e. left-linear and non-overlapping.
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public boolean isOrthogonal(final Abortion aborter) throws AbortionException {
        if (this.orthogonal == YNM.MAYBE) {
            synchronized(this) {
                if (this.orthogonal == YNM.MAYBE) {
                    // left-linear
                    for (final Rule rule : this.R) {
                        if (! rule.getLeft().isLinear()) {
                            this.orthogonal = YNM.NO;
                            return false;
                        }
                    }

                    // and no critical pairs
                    this.orthogonal = YNM.fromBool(!GeneralizedRule.getCriticalPairs(this.R).hasNext(aborter));

                }
            }
        }

        return this.orthogonal.toBool();
    }

    /**
     * Returns the replacementMap.
     * The positions in the replacements are guaranteed to be iterated in order.
     * @return
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<Integer>> getReplacementMap() {
        return this.replacementMap;
    }

    public boolean getInnermost() {
        return this.innermost;
    }


    @Override
    public String export(final Export_Util o) {
        final StringBuilder s = new StringBuilder();
        s.append(o.export("Context-sensitive rewrite system:"));
        s.append(o.cond_linebreak());
        if (this.R.isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.R, Export_Util.RULES));
            s.append(o.cond_linebreak());
            s.append("The replacement map contains the following entries:"+o.paragraph());
            for (final Map.Entry<FunctionSymbol, ? extends Set<Integer>> repMapEntry : this.replacementMap.entrySet()) {
                final Set<Integer> repl = repMapEntry.getValue();
                final ArrayList<Integer> shiftSet = new ArrayList<Integer>(repl.size());
                for (final Integer i : repl) {
                    shiftSet.add(i+1);
                }
                s.append(repMapEntry.getKey().export(o)+": "+o.set(shiftSet, Export_Util.SIMPLESET)+o.cond_linebreak());
            }
        }

        if (this.innermost) {
            s.append(o.paragraph()+"Innermost Strategy."+o.linebreak());
        }

        return s.toString();
    }

    public String toExternString() {
        final TRSGenerator trsGen =  new TRSGenerator();
        trsGen.writeRules(this.R);
        return trsGen.getTRSString(this.innermost, this.replacementMap);
    }

    public String externName() {
        return "trs";
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public String toHTML() {
        return this.export(new HTML_Util());
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this,
                (this.getInnermost() ? "Innermost " : "") + "Termination");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "csr";
    }

    @Override
    public Element getCPFInput(final Document doc, final XMLMetaData xmlMetaData, final TruthValue tv) {
        final Element cs = CPFTag.CONTEXT_SENSITIVE.create(doc);
        for (final Map.Entry<FunctionSymbol, ImmutableSet<Integer>> entry : this.replacementMap.entrySet()) {
            final FunctionSymbol f = entry.getKey();
            final Element repl =
                CPFTag.REPLACEMENT_MAP_ENTRY.create(
                    doc,
                    f.toCPF(doc, xmlMetaData),
                    CPFTag.ARITY.create(doc, doc.createTextNode("" + f.getArity())));
            for (final Integer i : entry.getValue()) {
                repl.appendChild(CPFTag.POSITION.create(doc, doc.createTextNode("" + (i + 1))));
            }
            cs.appendChild(repl);
        }
        return CPFTag.TRS_INPUT.create(doc, CPFTag.trs(doc, xmlMetaData, this.getR()), CPFTag.STRATEGY.create(doc, cs));
    }

    @Override
    public Element getCPFAssumption(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final CPFModus modus,
        final TruthValue tv)
    {
        if (modus.isPositive()) {
            return CPFTag.UNKNOWN_INPUT_PROOF.create(
                doc,
                CPFTag.UNKNOWN_ASSUMPTION.create(doc, CPFTag.UNKNOWN_INPUT.create(doc, "CSR termination problem")));

        } else {
            return CPFTag.TRS_NONTERMINATION_PROOF.create(
                doc,
                CPFTag.NONTERMINATION_ASSUMPTION.create(doc, this.getCPFInput(doc, xmlMetaData, tv)));
        }
    }

    @Override
    public boolean offersCertifiableTechniques() {
        return true;
    }

}
