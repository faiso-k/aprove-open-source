package aprove.verification.oldframework.Rewriting.SemanticLabelling;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.MaxMinPolynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

public class MyFiniteLabeller implements Labeller {
    private final Collection<Rule> oldRules;
    //private final Set<String> usedNames;
    private final ImmutableMap<FunctionSymbol, MaxMinPolynomial> interpretation;
    private final int css;
    private final Map<TRSFunctionApplication, TRSFunctionApplication> termMap;
    private final Map<FunctionSymbol, FunctionSymbol> labelToOriginMap;
    private final Set<FunctionSymbol> signature;
    private Set<TRSFunctionApplication> labQ = null;
    private Set<Rule> decrRules = null;
    private final Map<Integer, LinkedList<Pair<String, String>>> decrPairsMap =
        new HashMap<Integer, LinkedList<Pair<String, String>>>();
    private final Map<Integer, ImmutableArrayList<TRSTerm>> arityToxsMap =
        new HashMap<Integer, ImmutableArrayList<TRSTerm>>();
    private final Map<Rule, Rule> labRuleToRule = new HashMap<Rule, Rule>();

    public MyFiniteLabeller(final Collection<Rule> rules, final Map<TRSFunctionApplication, TRSFunctionApplication> termMap,
            final MyModel model) {
        this.oldRules = rules;
        this.interpretation = model.getInterpretation();
        this.css = model.getCarrierSize();
        this.labelToOriginMap = new HashMap<FunctionSymbol, FunctionSymbol>();
        if (Globals.useAssertions) {
            assert (this.css > 1) : "MyFiniteLabeller : You must not call a finite labeller with a model over an infinite carrier!";
        }
        this.termMap = termMap;
        this.signature = MyFiniteLabeller.calculateSignature(this.oldRules, new LinkedHashSet<FunctionSymbol>());
        final Map<TRSTerm, List<TRSTerm>> TermToLabTermCache = new HashMap<TRSTerm, List<TRSTerm>>();
    }

    private static LinkedHashSet<FunctionSymbol> calculateSignature(final Collection<Rule> rules,
        final LinkedHashSet<FunctionSymbol> signature) {
        for (final Rule r : rules) {
            signature.addAll(r.getFunctionSymbols());
        }
        return signature;
    }

    @Override
    public Map<FunctionSymbol, FunctionSymbol> getLabelToOriginMap() {
        return this.labelToOriginMap;
    }

    /**
     * <b> NOTE: Not implemented! Just for interface compliance!! </b>
     */
    @Override
    public void addQuasiLabeledPairs(final Rule rule,
        final Collection<Rule> addHere,
        final Set<FunctionSymbol> headSyms,
        final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {

    }

    @Override
    public void addLabeled(final TRSFunctionApplication term,
        final Set<TRSFunctionApplication> addHere,
        final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        final Set<TRSFunctionApplication> fApps = new HashSet<TRSFunctionApplication>(1);
        fApps.add(term);
        addHere.addAll(this.labelQterms(fApps));
    }

    @Override
    public void addLabeled(final Rule rule,
        final Collection<Rule> addHere,
        final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        final TRSFunctionApplication fApp = rule.getLeft();
        final TRSTerm t = rule.getRight();
        final Set<TRSVariable> vars = rule.getVariables();
        final Map<TRSVariable, Integer> varMapping = new HashMap<TRSVariable, Integer>();
        final ElementVectorIterator vIter = new ElementVectorIterator(vars.size(), this.css);
        while (vIter.hasNext()) {
            varMapping.clear();
            final int[] values = vIter.next();
            int pos = 0;
            final Iterator<TRSVariable> varIter = vars.iterator();
            while (varIter.hasNext()) {
                final TRSVariable v = varIter.next();
                varMapping.put(v, values[pos]);
                pos++;
            }
            final TRSFunctionApplication labLhs = (TRSFunctionApplication) this.labelTerm(fApp, varMapping).x;
            final TRSTerm labRhs = this.labelTerm(t, varMapping).x;
            final Rule labRule = Rule.create(labLhs, labRhs);
            addHere.add(labRule);
            this.labRuleToRule.put(labRule, rule);
        }
    }

    private Pair<TRSTerm, Integer> labelTerm(final TRSTerm t, final Map<TRSVariable, Integer> vMap) {

        if (t.isVariable()) {
            Integer val = vMap.get(t);
            if (val != null) {
                val = val % this.css;
            }
            return new Pair<TRSTerm, Integer>(t, val);
        } else {
            final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
            final FunctionSymbol fSym = fApp.getRootSymbol();
            final int arity = fSym.getArity();
            final MaxMinPolynomial intOffSym = this.interpretation.get(fSym);
            if (arity == 0) {
                return new Pair<TRSTerm, Integer>(t,
                    intOffSym.getVarPolynomial().getConstantPart().getNumericalAddend().intValue());
            }
            final ArrayList<TRSTerm> labelledArgs = new ArrayList<TRSTerm>(arity);
            final StringBuilder sb = new StringBuilder();
            StringBuilder varBuff;
            Pair<TRSTerm, Integer> actPair;
            if (arity < 3) {
                sb.append(fSym.getName());
                final Map<String, Integer> valueMap = new HashMap<String, Integer>(2);
                for (int i = 0; i < arity; i++) {
                    varBuff = new StringBuilder(3);
                    varBuff.append("x_");
                    final String varName = varBuff.append(i).toString();
                    actPair = this.labelTerm(fApp.getArgument(i), vMap);
                    labelledArgs.add(actPair.x);
                    sb.append(actPair.y);
                    valueMap.put(varName, actPair.y);

                }
                final FunctionSymbol labfSym = FunctionSymbol.create(sb.toString(), arity);
                final TRSTerm labT = TRSTerm.createFunctionApplication(labfSym, ImmutableCreator.create(labelledArgs));
                final int valueOfT = intOffSym.evaluate(valueMap).intValue() % this.css;
                return new Pair<TRSTerm, Integer>(labT, valueOfT);
            }
            final TRSFunctionApplication transfApp = this.termMap.get(fApp);
            final Integer originalTvalue = this.labelTerm(transfApp, vMap).y;
            sb.append(fSym.getName());
            for (int i = 0; i < arity; i++) {
                actPair = this.labelTerm(fApp.getArgument(i), vMap);
                labelledArgs.add(actPair.x);
                sb.append(actPair.y);
            }
            final FunctionSymbol labfSym = FunctionSymbol.create(sb.toString(), arity);
            final TRSTerm labT = TRSTerm.createFunctionApplication(labfSym, ImmutableCreator.create(labelledArgs));
            return new Pair<TRSTerm, Integer>(labT, originalTvalue);
        }
    }

    /**
     * @param qTerms
     * @return
     */
    public Set<TRSFunctionApplication> labelQterms(final Set<TRSFunctionApplication> qTerms) {
        if (this.labQ == null) {
            this.labQ = new HashSet<TRSFunctionApplication>();
            final Map<TRSVariable, Integer> varMapping = new HashMap<TRSVariable, Integer>();
            for (final TRSFunctionApplication fApp : qTerms) {
                final Set<TRSVariable> vars = fApp.getVariables();
                final ElementVectorIterator vIter = new ElementVectorIterator(vars.size(), this.css);
                while (vIter.hasNext()) {
                    varMapping.clear();
                    final int[] values = vIter.next();
                    int pos = 0;
                    final Iterator<TRSVariable> varIter = vars.iterator();
                    while (varIter.hasNext()) {
                        final TRSVariable v = varIter.next();
                        varMapping.put(v, values[pos]);
                        pos++;
                    }
                    final TRSFunctionApplication labfApp = (TRSFunctionApplication) this.labelTerm(fApp, varMapping).x;
                    this.labQ.add(labfApp);
                }
            }
        }
        return this.labQ;
    }

    @Override
    public Set<Rule> getDecreasingRules(final Collection<FunctionSymbol> fs,
        final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        final Set<Rule> decrRules = new HashSet<Rule>();
        for (final FunctionSymbol fSym : fs) {
            final int arity = fSym.getArity();
            if (arity > 0) {
                LinkedList<Pair<String, String>> decrPairs = this.decrPairsMap.get(arity);
                if (decrPairs == null) {
                    decrPairs = this.calcDecrPairs(arity);
                    this.decrPairsMap.put(arity, decrPairs);
                }
                ImmutableArrayList<TRSTerm> xs = this.arityToxsMap.get(arity);
                if (xs == null) {
                    final ArrayList<TRSTerm> ys = new ArrayList<TRSTerm>(arity);
                    for (int i = 0; i < arity; i++) {
                        ys.add(TRSTerm.createVariable("x" + i));
                    }
                    xs = ImmutableCreator.create(ys);
                    this.arityToxsMap.put(arity, xs);
                }
                for (final Pair<String, String> decrPair : decrPairs) {
                    StringBuilder name = new StringBuilder(fSym.getName());
                    final FunctionSymbol leftF = FunctionSymbol.create((name.append(decrPair.x).toString()), arity);
                    this.labelToOriginMap.put(leftF, fSym);
                    name = new StringBuilder(fSym.getName());
                    final FunctionSymbol rightF = FunctionSymbol.create((name.append(decrPair.x).toString()), arity);
                    this.labelToOriginMap.put(rightF, fSym);
                    final TRSFunctionApplication left = TRSTerm.createFunctionApplication(leftF, xs);
                    final TRSFunctionApplication right = TRSTerm.createFunctionApplication(rightF, xs);
                    decrRules.add(Rule.create(left, right));
                }
            }
        }
        return decrRules;
    }

    @Override
    public Set<Rule> getDecreasingRules(final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        if (this.decrRules == null) {
            this.decrRules = new HashSet<Rule>();
            for (final FunctionSymbol fSym : this.signature) {
                final int arity = fSym.getArity();
                if (arity > 0) {
                    LinkedList<Pair<String, String>> decrPairs = this.decrPairsMap.get(arity);
                    if (decrPairs == null) {
                        decrPairs = this.calcDecrPairs(arity);
                        this.decrPairsMap.put(arity, decrPairs);
                    }
                    ImmutableArrayList<TRSTerm> xs = this.arityToxsMap.get(arity);
                    if (xs == null) {
                        final ArrayList<TRSTerm> ys = new ArrayList<TRSTerm>(arity);
                        for (int i = 0; i < arity; i++) {
                            ys.add(TRSTerm.createVariable("x" + i));
                        }
                        xs = ImmutableCreator.create(ys);
                        this.arityToxsMap.put(arity, xs);
                    }
                    for (final Pair<String, String> decrPair : decrPairs) {
                        StringBuilder name = new StringBuilder(fSym.getName());
                        final FunctionSymbol leftF = FunctionSymbol.create((name.append(decrPair.x).toString()), arity);
                        this.labelToOriginMap.put(leftF, fSym);
                        name = new StringBuilder(fSym.getName());
                        final FunctionSymbol rightF =
                            FunctionSymbol.create((name.append(decrPair.y).toString()), arity);
                        this.labelToOriginMap.put(rightF, fSym);
                        final TRSFunctionApplication left = TRSTerm.createFunctionApplication(leftF, xs);
                        final TRSFunctionApplication right = TRSTerm.createFunctionApplication(rightF, xs);
                        this.decrRules.add(Rule.create(left, right));
                    }
                }
            }
        }
        return new HashSet<Rule>(this.decrRules);
    }

    private LinkedList<Pair<String, String>> calcDecrPairs(final int arity) {
        final LinkedList<int[]> workinglist = new LinkedList<int[]>();
        final LinkedHashSet<int[]> allCalculatedPreds = new LinkedHashSet<int[]>();
        final LinkedList<Pair<String, String>> result = new LinkedList<Pair<String, String>>();
        StringBuilder sb;
        final int[] maxValue = new int[arity];
        for (int i = 0; i < arity; i++) {
            maxValue[i] = this.css - 1;
        }
        workinglist.add(maxValue);
        int pos = 0;
        while (pos < workinglist.size()) {
            sb = new StringBuilder(arity);
            final int[] actElem = workinglist.get(pos);
            for (int i = 0; i < arity; i++) {
                sb.append(actElem[i]);
            }
            final String bigValue = sb.toString();
            final LinkedList<Pair<int[], String>> preds = this.calcDirectPreds(actElem);
            final Iterator<Pair<int[], String>> iter = preds.iterator();
            while (iter.hasNext()) {
                final Pair<int[], String> actPair = iter.next();
                if (allCalculatedPreds.contains(actPair.x)) {
                    continue;
                }
                allCalculatedPreds.add(actPair.x);
                workinglist.add(actPair.x);
                result.add(new Pair<String, String>(bigValue, actPair.y));
            }
            pos++;
        }
        return result;
    }

    private LinkedList<Pair<int[], String>> calcDirectPreds(final int[] elem) {
        final LinkedList<Pair<int[], String>> results = new LinkedList<Pair<int[], String>>();
        for (int i = 0; i < elem.length; i++) {
            final int actValue = elem[i];
            if (actValue > 0) {
                final int[] smallValue = new int[elem.length];
                System.arraycopy(elem, 0, smallValue, 0, elem.length);
                smallValue[i] = actValue - 1;
                final StringBuilder sb = new StringBuilder(smallValue.length);
                for (final int val : smallValue) {
                    sb.append(val);
                }
                results.add(new Pair<int[], String>(smallValue, sb.toString()));
            }
        }
        return results;
    }

    public Set<Rule> unlabelRules(final Set<Rule> labRules) {
        final Set<Rule> rules = new HashSet<Rule>();
        for (final Rule r : labRules) {
            rules.add(this.unlabel(r));
        }
        return rules;
    }

    @Override
    public Rule unlabel(final Rule rule) {
        Rule r = this.labRuleToRule.get(rule);
        if (r == null) {
            r = Rule.create((TRSFunctionApplication) this.unlabel(rule.getLeft()), this.unlabel(rule.getRight()));
        }
        return r;
    }

    public TRSTerm unlabel(final TRSTerm t) {
        if (t.isVariable()) {
            return t;
        } else {
            final TRSFunctionApplication ft = (TRSFunctionApplication) t;
            final FunctionSymbol f = this.labelToOriginMap.get(ft.getRootSymbol());
            final List<? extends TRSTerm> args = ft.getArguments();
            final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size());
            for (final TRSTerm arg : args) {
                newArgs.add(this.unlabel(arg));
            }
            return TRSTerm.createFunctionApplication(f, ImmutableCreator.create(newArgs));
        }
    }

    @Override
    public String toString() {
        return this.interpretation.toString();
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder builder = new StringBuilder();
        builder.append("Interpretation over the domain with elements from 0 to " + (this.css - 1) + ".");
        builder.append(o.linebreak());
        for (final Map.Entry<FunctionSymbol, MaxMinPolynomial> entry : this.interpretation.entrySet()) {
            builder.append(entry.getKey().export(o) + ": " + entry.getValue().export(o));
            builder.append(o.cond_linebreak());
        }
        return builder.toString();
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element model = XMLTag.MODEL.createElement(doc);
        for (final Map.Entry<FunctionSymbol, MaxMinPolynomial> entry : this.interpretation.entrySet()) {
            final Element interpret = XMLTag.INTERPRET.createElement(doc);
            interpret.appendChild(entry.getKey().toDOM(doc, xmlMetaData));
            interpret.appendChild(entry.getValue().toDOM(doc, xmlMetaData));
            model.appendChild(interpret);
        }
        return model;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData, final int carrierSize, final boolean quasi)
    {
        final Element finiteModel = CPFTag.FINITE_MODEL.createElement(doc);

        final Element carrierSizeTag = CPFTag.CARRIER_SIZE.createElement(doc);
        carrierSizeTag.appendChild(doc.createTextNode("" + carrierSize));
        finiteModel.appendChild(carrierSizeTag);

        if (quasi) {
            final Element tupleOrder = CPFTag.TUPLE_ORDER.createElement(doc);
            final Element pointWise = CPFTag.POINT_WISE.createElement(doc);
            tupleOrder.appendChild(pointWise);
            finiteModel.appendChild(tupleOrder);
        }

        for (final Map.Entry<FunctionSymbol, MaxMinPolynomial> entry : this.interpretation.entrySet()) {
            final Element interpret = CPFTag.INTERPRET.createElement(doc);
            interpret.appendChild(entry.getKey().toCPF(doc, xmlMetaData));
            final Element arity = CPFTag.ARITY.createElement(doc);
            arity.appendChild(doc.createTextNode("" + entry.getKey().getArity()));
            interpret.appendChild(arity);
            throw new RuntimeException("interpret.appendChild(entry.getValue().toCPF(doc, xmlMetaData));"
                + "finiteModel.appendChild(interpret);");
        }

        return finiteModel;
    }

    @Override
    public String isCPFSupported() {
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Collection<FunctionSymbol> labelFS(final FunctionSymbol funcSym,
        final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        assert (false);
        return null;
    }

}
