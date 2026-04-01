package aprove.verification.dpframework.DPConstraints;

import java.io.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.AbstractInductionCalculus.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

public class InductionCalculusProof extends QDPProof {

    Map<GeneralizedRule, List<Simplification>> simpPerPair = new LinkedHashMap<GeneralizedRule, List<Simplification>>();
    Simplification curSimp;
    List<Simplification> curSimpList;
    public int fixedPosition;
    boolean empty = true;
    Set<? extends GeneralizedRule> dps;
    TRSFunctionApplication c;
    Options options;

    //debug
    FileWriter fw = null;
    private final boolean idpMode;

    public InductionCalculusProof(final IDPProblem idp, final Options options) {
        this.options = options;
        this.dps = idp.getP();
        this.init(idp.getRuleAnalysis().getFunctionSymbolsPRNoHead());
        this.idpMode = true;
    }

    public InductionCalculusProof(final QDPProblem qdp, final Options options) {
        this.options = options;
        this.dps = qdp.getP();
        this.init(qdp.getSignature());
        this.idpMode = false;
    }

    protected void init(final Set<FunctionSymbol> signature) {
        final String prefix = "c_";
        int count = 0;
        String fullName = "c";
        while (true) {
            final FunctionSymbol cSym = FunctionSymbol.create(fullName, 0);
            if (!signature.contains(cSym)) {
                final TRSTerm[] array = new TRSTerm[0];
                this.c = TRSTerm.createFunctionApplication(cSym, array);
                break;
            }
            count++;
            fullName = prefix + count;
        }
    }

    public InductionCalculusProof createCopyForOutput(final QDPProblem qdp) {
        final InductionCalculusProof copy = new InductionCalculusProof(qdp, this.options);
        this.initCopy(copy);
        return copy;
    }

    public InductionCalculusProof createCopyForOutput(final IDPProblem idp) {
        final InductionCalculusProof copy = new InductionCalculusProof(idp, this.options);
        this.initCopy(copy);
        return copy;
    }

    protected void initCopy(final InductionCalculusProof copy) {
        copy.simpPerPair = this.simpPerPair;
        copy.empty = this.empty;
    }

    public TRSFunctionApplication getC() {
        return this.c;
    }

    public void forPairTheFollowingChainsWhereCreated(final GeneralizedRule pair) {
        this.empty = false;
        this.curSimpList = new LinkedList<>();
        this.simpPerPair.put(pair, this.curSimpList);
        if (Globals.DEBUG_SWISTE) {
            //debug
            //if (this.fw != null){
            try {
                this.fw = new FileWriter("/home/swiste/proofs/pair+" + pair + ".html");
            } catch (final IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
            //}
            //end debug
        }
    }

    public void forChainTheFollowingConstrainsWhereCreated(final List<GeneralizedRule> chain) {
        this.curSimp = new Simplification(chain);
        this.curSimpList.add(this.curSimp);
        //debug
        if (this.fw != null) {
            try {
                final Export_Util o = new HTML_Util();
                this.fw.append("For chain ");
                final List<String> strs = new LinkedList<String>();
                strs.clear();
                int k = 0;
                for (final GeneralizedRule cp : chain) {
                    strs.add((k == this.fixedPosition) ? o.bold(cp.export(o)) : cp.export(o));
                    k++;
                }
                this.fw.append(o.set(chain, Export_Util.RULES));
                this.fw.append("the following constraints were created:");
                this.fw.append(o.linebreak());
            } catch (final IOException e) {
                e.printStackTrace();
            }
        }
        //end debug
    }

    public void resultForChain(final List<Implication> cs) {
        this.curSimp.appliedRule(null, cs, null, null, null, 0);
        //debug
        if (this.fw != null) {
            try {
                final StringBuilder sb = new StringBuilder();
                InductionCalculusProof.writeToSB(sb, new HTML_Util(), new LinkedList<String>(), cs, null, null, 0, VerbosityLevel.HIGH);
                this.fw.append(sb);
            } catch (final IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }
        //end debug
    }

    public void resultForPair() {
        //debug
        if (this.fw != null) {
            try {
                this.fw.close();
            } catch (final IOException e) {
                e.printStackTrace();
            }
        }
        //end debug
    }

    public void appliedRule(
        final Implication imp,
        final InfRule rule,
        final List<Implication> cs,
        final Exportable mark,
        final InfProofStepInfo info,
        final int i)
    {
        this.curSimp.appliedRule(imp, cs, rule, mark, info, i);
        //debug
        if (this.fw != null) {
            try {
                final StringBuilder sb = new StringBuilder();
                InductionCalculusProof.writeToSB(sb, new HTML_Util(), new LinkedList<String>(), cs, rule, mark, i, VerbosityLevel.HIGH);
                this.fw.append(sb);
            } catch (final IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }
        //end debug
    }

    @Override
    public String export(final Export_Util o, final VerbosityLevel level) {
        final StringBuilder sb = new StringBuilder();

        if (this.empty) {
            // TODO ...because only some constraints were removed?
            sb.append("Please refer to a previous processor for the proof.");
        } else {
            final Map<GeneralizedRule, Set<Implication>> allFinals =
                new LinkedHashMap<GeneralizedRule, Set<Implication>>();
            sb.append("Note that ");
            sb.append(o.bold("final constraints"));
            sb.append(" are written in ");
            sb.append(o.bold("bold face"));
            sb.append(".");
            sb.append(o.newline());
            sb.append(o.linebreak());
            sb.append(o.linebreak());
            for (final Map.Entry<GeneralizedRule, List<Simplification>> entry : this.simpPerPair.entrySet()) {
                final GeneralizedRule pair = entry.getKey();
                if (this.dps.contains(pair)) {
                    final Set<Implication> finals = new LinkedHashSet<Implication>();
                    sb.append("For Pair ");
                    sb.append(pair.export(o));
                    sb.append(" the following chains were created:");
                    sb.append(o.linebreak());
                    final List<String> ul = new ArrayList<String>();
                    simpLoop: for (final Simplification simp : entry.getValue()) {
                        for (final GeneralizedRule dp : simp.chain) {
                            if (!this.dps.contains(dp)) {
                                continue simpLoop;
                            }
                        }
                        // simp.sbexport(sb, this.fixedPosition, o, level);
                        InductionCalculusProof.restructureExport(simp, o, ul, 1, finals, this.idpMode);
                    }
                    sb.append(o.set(ul, Export_Util.ITEMIZE));
                    sb.append(o.linebreak());
                    sb.append(o.linebreak());
                    sb.append(o.linebreak());
                    sb.append(o.newline());
                    allFinals.put(entry.getKey(), finals);
                }
            }

            sb.append("To summarize, we get the following constraints P"
                + o.sub(o.nonStrictRelativ())
                + " for the following pairs."
                + o.newline());
            final List<String> ulOuter = new ArrayList<String>();
            for (final Map.Entry<GeneralizedRule, Set<Implication>> entry : allFinals.entrySet()) {
                final StringBuilder sbOuter = new StringBuilder();
                final List<String> ulInner = new ArrayList<String>();
                sbOuter.append(entry.getKey().export(o) + o.newline());
                for (final Implication implication : entry.getValue()) {
                    ulInner.add(implication.export(o) + o.newline());
                }
                sbOuter.append(o.set(ulInner, Export_Util.ITEMIZE) + o.newline());
                ulOuter.add(sbOuter.toString());
            }
            sb.append(o.set(ulOuter, Export_Util.ITEMIZE));
            sb.append(o.newline() + o.newline());
            sb.append(o.linebreak()
                + "The constraints for P"
                + o.sub(o.gtSign())
                + " respective P"
                + o.sub("bound")
                + " are"
                + " constructed from P"
                + o.sub(o.nonStrictRelativ())
                + " where we just replace every "
                + "occurence of \"t "
                + o.nonStrictRelativ()
                + " s\" in "
                + "P"
                + o.sub(o.nonStrictRelativ())
                + " by "
                + " \"t "
                + o.gtSign()
                + " s\" respective \"t "
                + o.nonStrictRelativ()
                + " "
                + this.c.export(o)
                + "\". ");
            sb.append("Here " + this.c.export(o) + " stands for the fresh constant used for P" + o.sub("bound") + ". ");

        }
        return sb.toString();
    }

    public static Element toDOM(
        final Document doc,
        final Constraint con,
        final Kind kind,
        final TRSTerm fc,
        final XMLMetaData xmlMetaData)
    {
        if (con instanceof Predicate) {
            final Predicate p = (Predicate) con;
            final Element cc = doc.createElement(InductionCalculusProof.CC);
            final Element c = doc.createElement(InductionCalculusProof.C);
            c.appendChild(p.left.toDOM(doc, xmlMetaData));
            switch (kind) {
            case Strict:
                c.appendChild(doc.createElement(InductionCalculusProof.S));
                break;
            case NonStrict:
                c.appendChild(doc.createElement(InductionCalculusProof.NS));
                break;
            case Bound:
                c.appendChild(doc.createElement(InductionCalculusProof.NS));
                break;
            }
            final TRSTerm r = (kind == Kind.Bound ? fc : p.right);
            c.appendChild(r.toDOM(doc, xmlMetaData));
            cc.appendChild(c);
            return cc;
        }
        if (con instanceof ReducesTo) {
            final ReducesTo p = (ReducesTo) con;
            final Element cc = doc.createElement(InductionCalculusProof.CC);
            final Element c = doc.createElement(InductionCalculusProof.C);
            c.appendChild(p.left.toDOM(doc, xmlMetaData));
            c.appendChild(doc.createElement(InductionCalculusProof.R));
            c.appendChild(p.right.toDOM(doc, xmlMetaData));
            cc.appendChild(c);
            return cc;
        }
        if (con instanceof Implication) {
            return InductionCalculusProof.toDOM(doc, (Implication) con, kind, fc, xmlMetaData);
        }
        return null;
    }

    public static Element toCPF(
        final Document doc,
        final Constraint con,
        final Kind kind,
        final TRSTerm fc,
        final XMLMetaData xmlMetaData)
    {
        if (con instanceof Predicate) {
            final Predicate p = (Predicate) con;
            final Element cc = doc.createElement(InductionCalculusProof.CC);
            final Element c = doc.createElement(InductionCalculusProof.C);
            c.appendChild(p.left.toCPF(doc, xmlMetaData));
            switch (kind) {
            case Strict:
                c.appendChild(doc.createElement(InductionCalculusProof.S));
                break;
            case NonStrict:
                c.appendChild(doc.createElement(InductionCalculusProof.NS));
                break;
            case Bound:
                c.appendChild(doc.createElement(InductionCalculusProof.NS));
                break;
            }
            final TRSTerm r = (kind == Kind.Bound ? fc : p.right);
            c.appendChild(r.toCPF(doc, xmlMetaData));
            cc.appendChild(c);
            return cc;
        }
        if (con instanceof ReducesTo) {
            final ReducesTo p = (ReducesTo) con;
            final Element cc = doc.createElement(InductionCalculusProof.CC);
            final Element c = doc.createElement(InductionCalculusProof.C);
            c.appendChild(p.left.toCPF(doc, xmlMetaData));
            c.appendChild(doc.createElement(InductionCalculusProof.R));
            c.appendChild(p.right.toCPF(doc, xmlMetaData));
            cc.appendChild(c);
            return cc;
        }
        if (con instanceof Implication) {
            return InductionCalculusProof.toCPF(doc, (Implication) con, kind, fc, xmlMetaData);
        }
        return CPFTag.createError(doc);
    }

    public static Element toDOM(
        final Document doc,
        final Implication imp,
        final Kind kind,
        final TRSTerm fc,
        final XMLMetaData xmlMetaData)
    {
        Element e = InductionCalculusProof.toDOM(doc, imp.conclusion, kind, fc, xmlMetaData);
        if (!imp.conditions.isEmpty()) {
            final Element i = doc.createElement(InductionCalculusProof.CC);
            final Element im = doc.createElement(InductionCalculusProof.I);
            for (final Constraint c : imp.conditions) {
                im.appendChild(InductionCalculusProof.toDOM(doc, c, kind, fc, xmlMetaData));
            }
            im.appendChild(e);
            i.appendChild(im);
            e = i;
        }
        final Set<TRSVariable> quantor = imp.quantor;
        int n = quantor.size();
        final TRSVariable[] revQuantor = new TRSVariable[n];
        for (final TRSVariable v : quantor) {
            n--;
            revQuantor[n] = v;
        }
        for (final TRSVariable v : revQuantor) {
            final Element aa = doc.createElement(InductionCalculusProof.CC);
            final Element a = doc.createElement(InductionCalculusProof.A);
            a.appendChild(v.toDOM(doc, xmlMetaData));
            a.appendChild(e);
            aa.appendChild(a);
            e = aa;
        }
        return e;
    }

    public static Element toCPF(
        final Document doc,
        final Implication imp,
        final Kind kind,
        final TRSTerm fc,
        final XMLMetaData xmlMetaData)
    {
        Element e = InductionCalculusProof.toCPF(doc, imp.conclusion, kind, fc, xmlMetaData);
        if (!imp.conditions.isEmpty()) {
            final Element i = doc.createElement(InductionCalculusProof.CC);
            final Element im = doc.createElement(InductionCalculusProof.I);
            for (final Constraint c : imp.conditions) {
                im.appendChild(InductionCalculusProof.toCPF(doc, c, kind, fc, xmlMetaData));
            }
            im.appendChild(e);
            i.appendChild(im);
            e = i;
        }
        final Set<TRSVariable> quantor = imp.quantor;
        int n = quantor.size();
        final TRSVariable[] revQuantor = new TRSVariable[n];
        for (final TRSVariable v : quantor) {
            n--;
            revQuantor[n] = v;
        }
        for (final TRSVariable v : revQuantor) {
            final Element aa = doc.createElement(InductionCalculusProof.CC);
            final Element a = doc.createElement(InductionCalculusProof.A);
            a.appendChild(v.toCPF(doc, xmlMetaData));
            a.appendChild(e);
            aa.appendChild(a);
            e = aa;
        }
        return e;
    }

    static enum Kind {
        Strict, NonStrict, Bound
    };

    private final static String CC = "conditionalConstraint";
    private final static String C = "constraint";
    private final static String F = "final";
    private final static String S = "strict";
    private final static String NS = "nonStrict";
    private final static String R = "rewrite";
    private final static String I = "implication";
    private final static String A = "all";

    private void toDOM(
        final Document doc,
        final Element conditions,
        final Rule st,
        final Kind kind,
        final XMLMetaData xmlMetaData)
    {
        for (final Simplification simp : this.simpPerPair.get(st)) {
            simp.toDOM(doc, conditions, kind, this.c, xmlMetaData);
        }
    }

    private void toCPF(
        final Document doc,
        final Element conditions,
        final Rule st,
        final Kind kind,
        final XMLMetaData xmlMetaData)
    {
        for (final Simplification simp : this.simpPerPair.get(st)) {
            simp.toCPF(doc, conditions, kind, this.c, xmlMetaData);
        }
    }

    public Element toDOM(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final Set<Rule> strict,
        final Set<Rule> bound,
        final Set<Rule> all)
    {
        final Element e = XMLTag.BOUNDED_INCREASE_PROOF.createElement(doc);

        e.appendChild(this.c.getRootSymbol().toDOM(doc, xmlMetaData));

        final Element bef = doc.createElement("before");
        bef.setTextContent("" + this.options.leftChainCounter);
        e.appendChild(bef);

        final Element aft = doc.createElement("after");
        aft.setTextContent("" + this.options.rightChainCounter);
        e.appendChild(aft);

        final Element conditions = doc.createElement("conditions");
        for (final Rule st : bound) {
            this.toDOM(doc, conditions, st, Kind.Bound, xmlMetaData);
        }
        for (final Rule st : all) {
            if (strict.contains(st)) {
                this.toDOM(doc, conditions, st, Kind.Strict, xmlMetaData);
            } else {
                this.toDOM(doc, conditions, st, Kind.NonStrict, xmlMetaData);
            }

        }
        e.appendChild(conditions);
        return e;
    }

    public Element toCPF(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final Set<Rule> strict,
        final Set<Rule> bound,
        final Set<Rule> all)
    {
        final Element conditions = CPFTag.CONDITIONS.create(doc);
        for (final Rule st : bound) {
            this.toCPF(doc, conditions, st, Kind.Bound, xmlMetaData);
        }
        for (final Rule st : all) {
            if (strict.contains(st)) {
                this.toCPF(doc, conditions, st, Kind.Strict, xmlMetaData);
            } else {
                this.toCPF(doc, conditions, st, Kind.NonStrict, xmlMetaData);
            }

        }
        return CPFTag.COND_RED_PAIR_PROOF.create(
            doc,
            this.c.getRootSymbol().toCPF(doc, xmlMetaData),
            CPFTag.BEFORE.create(doc, doc.createTextNode("" + this.options.leftChainCounter)),
            CPFTag.AFTER.create(doc, doc.createTextNode("" + this.options.rightChainCounter)),
            conditions);
    }

    private static Integer restructureExport(
        final Simplification simplification,
        final Export_Util o,
        final List<String> ul,
        Integer id,
        final Set<Implication> finals,
        final boolean idpMode)
    {
        final StringBuilder sb = new StringBuilder();
        final int initId = id;
        final Map<Implication, Integer> implToId = new LinkedHashMap<Implication, Integer>();
        final Map<Implication, ExportStep> implToSuccessors = new LinkedHashMap<Implication, ExportStep>();
        final Map<Implication, Implication> predecessors = new LinkedHashMap<Implication, Implication>();

        final Iterator<List<Implication>> implicationsLists = simplification.steps.iterator();
        final Iterator<InfRule> appliedRules = simplification.stepRule.iterator();
        final Iterator<Exportable> marks = simplification.marks.iterator();
        final Iterator<Integer> indices = simplification.redIndices.iterator();

        List<Implication> currentImplications = implicationsLists.next();

        for (final Implication implication : currentImplications) {
            implToId.put(implication, id);
            id++;
        }

        while (implicationsLists.hasNext()) {

            final List<Implication> nextImplications = implicationsLists.next();
            final int index = indices.next();
            final Exportable mark = marks.next();
            final InfRule appliedRule = appliedRules.next();
            final Implication implication = currentImplications.get(index);
            final InfRuleID ruleNr = appliedRule.getID();

            // the list of new Implications that have been generated by appliedRule
            final List<Implication> newImplications = new ArrayList<Implication>(4);
            for (final Implication impl : nextImplications) {
                if (!currentImplications.contains(impl)) {
                    newImplications.add(impl);
                    implToId.put(impl, id);
                    id++;

                }
            }

            final boolean rule56 =
                ruleNr == InfRuleID.V
                    || ruleNr == InfRuleID.VI
                    || ruleNr == InfRuleID.IDP_SMT_SPLIT
                    || ruleNr == InfRuleID.POLY_CONSTRAINTS
                    || ruleNr == InfRuleID.POLY_REMOVE_MIN_MAX;
            boolean done = false;
            if (!rule56) {
                if (!idpMode) {
                    assert (newImplications.size() <= 1);
                }
                final Implication predecessor = predecessors.get(implication);
                if (predecessor != null) {
                    final ExportStep expStep = implToSuccessors.get(predecessor);
                    if (expStep.mergable) {
                        if (ruleNr == InfRuleID.I_II) {
                            expStep.appliedRules.add(InfRuleID.I);
                            expStep.appliedRules.add(InfRuleID.II);
                        } else {
                            expStep.appliedRules.add(ruleNr);
                        }
                        if (!idpMode) {
                            assert (expStep.successors.size() == 1);
                        }
                        for (final Implication impl : expStep.successors) {
                            implToId.remove(impl);
                        }

                        expStep.successors = newImplications;
                        for (final Implication newImpl : newImplications) {
                            predecessors.put(newImpl, predecessor);
                        }
                        done = true;
                    }
                }
            }

            if (!done) {
                for (final Implication newImpl : newImplications) {
                    predecessors.put(newImpl, implication);
                }
                final Set<InfRuleID> ruleNrs = new TreeSet<InfRuleID>();
                if (ruleNr == InfRuleID.I_II) {
                    ruleNrs.add(InfRuleID.I);
                    ruleNrs.add(InfRuleID.II);
                } else {
                    ruleNrs.add(ruleNr);
                }
                final ExportStep expStep =
                    new ExportStep(newImplications, ruleNrs, rule56 ? mark : null, !rule56, implication);
                implToSuccessors.put(implication, expStep);
            }

            currentImplications = nextImplications;

        }

        for (final Implication impl : implToId.keySet()) {
            if (!implToSuccessors.containsKey(impl)) {
                finals.add(impl);
            }
        }

        // now we have build our helper sets, so lets do the output

        // first reset the nr
        final Pair<Integer, ?> global = new Pair<Integer, Object>(initId, null);
        final Map<Integer, Integer> lookup = new HashMap<Integer, Integer>();

        sb.append("We consider the chain ");
        boolean first = true;
        for (final GeneralizedRule rule : simplification.chain) {
            if (first) {
                first = false;
            } else {
                sb.append(", ");
            }
            sb.append(rule.export(o));
        }

        sb.append(" which results in the following constraint:");
        sb.append(o.newline());
        {
            final Map.Entry<Implication, Integer> e = implToId.entrySet().iterator().next();
            final Implication impl = e.getKey();
            final Integer implNr = InductionCalculusProof.lookupNr(e.getValue(), global, lookup);
            sb.append(o.indent("(" + implNr + ") " + o.appSpace() + o.appSpace() + " " + impl.export(o))); //TODO indent? appSpace?
            sb.append(o.newline());
            sb.append(o.newline());
        }
        for (final Map.Entry<Implication, Integer> e : implToId.entrySet()) {
            final Implication impl = e.getKey();
            final Integer implNr = InductionCalculusProof.lookupNr(e.getValue(), global, lookup);
            final ExportStep expStep = implToSuccessors.get(impl);
            if (expStep != null) {
                final List<Implication> succs = expStep.successors;
                final int size = succs.size();
                if (size == 0) {
                    sb.append("We solved constraint (" + implNr + ") using rule" + InductionCalculusProof.showNrs(expStep.appliedRules) + ".");
                } else {
                    sb.append("We simplified constraint (" + implNr + ") using rule" + InductionCalculusProof.showNrs(expStep.appliedRules));
                    if (expStep.mark != null) {
                        if (expStep.appliedRules.contains(InfRuleID.V)) {
                            sb.append(" using induction on " + expStep.mark.export(o));
                        }
                        if (expStep.appliedRules.contains(InfRuleID.VI)) {
                            sb.append(" where we applied the induction hypothesis " + expStep.mark.export(o));
                        }
                    }
                    sb.append(" which results in the following new constraint" + (size > 1 ? "s:" : ":") + o.newline());
                    for (final Implication succ : succs) { // TODO indent? appSpace? list?
                        final Integer nr = InductionCalculusProof.lookupNr(implToId.get(succ), global, lookup);
                        if (finals.contains(succ)) {
                            sb.append(o.indent(o.bold("("
                                + nr
                                + ") "
                                + o.appSpace()
                                + o.appSpace()
                                + o.appSpace()
                                + succ.export(o))));
                        } else {
                            sb.append(o.indent("("
                                + nr
                                + ") "
                                + o.appSpace()
                                + o.appSpace()
                                + o.appSpace()
                                + succ.export(o)));
                        }
                        sb.append(o.newline());
                    }
                    sb.append(o.newline());
                }
            }
        }

        ul.add(new String(sb.toString()));

        return global.x;
    }

    private static
        Integer
        lookupNr(final Integer old, final Pair<Integer, ?> global, final Map<Integer, Integer> lookup)
    {
        Integer newNr = lookup.get(old);
        if (newNr == null) {
            newNr = global.x;
            global.x = newNr + 1;
            lookup.put(old, newNr);
        }
        return newNr;
    }

    private static String showNrs(final Set<InfRuleID> set) {
        String s = set.size() > 1 ? "s " : " ";
        boolean first = true;
        for (final InfRuleID id : set) {
            if (first) {
                first = false;
            } else {
                s += ", ";
            }
            s += id.toString();
        }
        return s;
    }

    private static class ExportStep {
        private List<Implication> successors;
        private final Set<InfRuleID> appliedRules;
        private final Exportable mark;
        private final boolean mergable;
        private final Implication predecessor;

        public ExportStep(
            final List<Implication> succs,
            final Set<InfRuleID> appliedRules,
            final Exportable mark,
            final boolean mergable,
            final Implication predecessor)
        {
            this.successors = succs;
            this.appliedRules = appliedRules;
            this.mark = mark;
            this.mergable = mergable;
            this.predecessor = predecessor;
        }
    }

    public static class Simplification {
        List<List<Implication>> steps;
        List<InfRule> stepRule;
        List<Exportable> marks;
        List<Integer> redIndices;
        List<GeneralizedRule> chain;
        Map<Implication, InfProofStepInfo> treeProof;

        public Simplification(final List<GeneralizedRule> chain) {
            this.steps = new LinkedList<>();
            this.stepRule = new LinkedList<>();
            this.marks = new LinkedList<>();
            this.redIndices = new LinkedList<>();
            this.chain = chain;
            this.treeProof = new LinkedHashMap<>();
        }

        void appliedRule(
            final Implication imp,
            final List<Implication> cs,
            final InfRule rule,
            final Exportable mark,
            final InfProofStepInfo info,
            final int i)
        {
            this.steps.add(cs);
            this.stepRule.add(rule);
            this.marks.add(mark);
            this.redIndices.add(i);
            if (imp != null) {
                this.treeProof.put(imp, info);
            }
        }

        public void sbexport(
            final StringBuilder sb,
            final int fixedPosition,
            final Export_Util o,
            final VerbosityLevel level)
        {
            final Iterator<List<Implication>> its = this.steps.iterator();
            final Iterator<InfRule> itsr = this.stepRule.iterator();
            final Iterator<Exportable> mit = this.marks.iterator();
            final Iterator<Integer> iit = this.redIndices.iterator();
            sb.append("For chain ");
            final List<String> strs = new LinkedList<String>();
            strs.clear();
            int k = 0;
            for (final GeneralizedRule cp : this.chain) {
                strs.add((k == fixedPosition) ? o.bold(cp.export(o)) : cp.export(o));
                k++;
            }
            sb.append(o.set(this.chain, Export_Util.RULES));
            sb.append("the following constraints were created:");
            sb.append(o.linebreak());
            while (its.hasNext()) {
                final List<Implication> step = its.next();
                final InfRule ir = itsr.next();
                final Exportable mark = mit.next();
                final int i = iit.next();
                InductionCalculusProof.writeToSB(sb, o, strs, step, ir, mark, i, level);
            }
        }

        private Element prfToDOM(
            final Document doc,
            final Implication imp,
            final Kind kind,
            final TRSTerm fc,
            final XMLMetaData xmlMetaData)
        {
            final InfProofStepInfo info = this.treeProof.get(imp);
            if (info == null) {
                final Element e = doc.createElement(InfProofStepConstants.CCP);
                final Element ee = doc.createElement(InductionCalculusProof.F);
                e.appendChild(ee);
                return e;
            } else {
                final List<Implication> imps = info.result();
                final List<Element> prfs = new ArrayList<>(imps.size());
                for (final Implication i : imps) {
                    prfs.add(this.prfToDOM(doc, i, kind, fc, xmlMetaData));
                }
                return info.toDOM(doc, xmlMetaData, prfs, kind, fc);
            }
        }

        private Element prfToCPF(
            final Document doc,
            final Implication imp,
            final Kind kind,
            final TRSTerm fc,
            final XMLMetaData xmlMetaData)
        {
            final InfProofStepInfo info = this.treeProof.get(imp);
            if (info == null) {
                final Element e = doc.createElement(InfProofStepConstants.CCP);
                final Element ee = doc.createElement(InductionCalculusProof.F);
                e.appendChild(ee);
                return e;
            } else {
                final List<Implication> imps = info.result();
                final List<Element> prfs = new ArrayList<>(imps.size());
                for (final Implication i : imps) {
                    prfs.add(this.prfToCPF(doc, i, kind, fc, xmlMetaData));
                }
                return info.toCPF(doc, xmlMetaData, prfs, kind, fc);
            }
        }

        public void toDOM(
            final Document doc,
            final Element conditions,
            final Kind kind,
            final TRSTerm fc,
            final XMLMetaData xmlMetaData)
        {
            for (final Implication imp : this.steps.get(0)) {
                final Element e = doc.createElement("condition");
                e.appendChild(InductionCalculusProof.toDOM(doc, imp, kind, fc, xmlMetaData));
                final Element dps = XMLTag.DPS.createElement(doc);
                for (final GeneralizedRule gr : this.chain) {
                    dps.appendChild(gr.toDOM(doc, xmlMetaData));
                }
                e.appendChild(dps);
                e.appendChild(this.prfToDOM(doc, imp, kind, fc, xmlMetaData));
                conditions.appendChild(e);
            }
        }

        public void toCPF(
            final Document doc,
            final Element conditions,
            final Kind kind,
            final TRSTerm fc,
            final XMLMetaData xmlMetaData)
        {
            for (final Implication imp : this.steps.get(0)) {
                final Element e =
                    CPFTag.CONDITION.create(
                        doc,
                        InductionCalculusProof.toCPF(doc, imp, kind, fc, xmlMetaData),
                        CPFTag.DP_SEQUENCE.create(doc, CPFTag.rules(doc, xmlMetaData, this.chain)),
                        this.prfToCPF(doc, imp, kind, fc, xmlMetaData));
                conditions.appendChild(e);
            }
        }

    }

    private static void writeToSB(
        final StringBuilder sb,
        final Export_Util o,
        final List<String> strs,
        final List<Implication> step,
        final InfRule ir,
        final Exportable mark,
        final int i,
        final VerbosityLevel level)
    {
        strs.clear();
        int j = 0;
        for (final Implication imp : step) {
            if (i == j) {
                strs.add(o.bold(imp.export(o)));
            } else {
                strs.add(imp.export(o));
            }
            j++;
        }
        if (strs.isEmpty()) {
            strs.add("no remaining constraints");
            sb.append(o.set(strs, Export_Util.ITEMIZE));
        } else {
            sb.append(o.set(strs, Export_Util.ITEMIZE));
        }
        if (ir != null) {
            final String name = (level == VerbosityLevel.HIGH) ? ir.getLongName() : ir.getName();
            sb.append(name);
            if (mark != null) {
                sb.append(" applied on ");
                sb.append(mark.export(o));
            }
            sb.append(o.linebreak());
        }
        sb.append(o.cond_linebreak());
    }

    public Options getOptions() {
        return this.options;
    }

}
