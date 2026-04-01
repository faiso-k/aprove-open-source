package aprove.verification.oldframework.Rewriting.SemanticLabelling;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

public class FiniteLabeller implements Labeller {

    private final Map<FunctionSymbol, FunctionRepresentation> interpretation;
    private final Map<FunctionSymbol, FunctionSymbol> labelToOriginMap;
    private final FunctionRepresentation aFunctionalRepresentation;
    private final int carrierSetSize;

    public FiniteLabeller(final Map<FunctionSymbol, FunctionRepresentation> interpretation) {
        this.interpretation = interpretation;
        this.labelToOriginMap = new HashMap<FunctionSymbol, FunctionSymbol>();
        this.aFunctionalRepresentation = interpretation.values().iterator().next();
        this.carrierSetSize = this.aFunctionalRepresentation.getCarrierSetSize();
    }

    @Override
    public Map<FunctionSymbol, FunctionSymbol> getLabelToOriginMap() {
        return this.labelToOriginMap;
    }

    @Override
    public void addLabeled(final Rule rule,
        final Collection<Rule> addHere,
        final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {

        final Set<TRSVariable> variables = rule.getVariables();
        final int variableCount = variables.size();

        final Pair<ElementValue, TRSTerm> result = new Pair<ElementValue, TRSTerm>(null, null);

        final ElementVectorIterator valueIter = new ElementVectorIterator(variableCount, this.carrierSetSize);
        while (valueIter.hasNext()) {

            final Iterator<TRSVariable> variableIter = variables.iterator();
            final Map<TRSVariable, ElementValue> varMap = new HashMap<TRSVariable, ElementValue>(variableCount);
            for (final int value : valueIter.next()) {
                varMap.put(variableIter.next(), this.aFunctionalRepresentation.getElementValue(value));
            }

            this.generateLabeled(rule.getLeft(), varMap, result, xmlLabelMap);
            final TRSFunctionApplication lLeft = (TRSFunctionApplication) result.y;

            this.generateLabeled(rule.getRight(), varMap, result, xmlLabelMap);
            addHere.add(Rule.create(lLeft, result.y));
        }

    }

    @Override
    public void addQuasiLabeledPairs(final Rule rule,
        final Collection<Rule> addHere,
        final Set<FunctionSymbol> headSyms,
        final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        final TRSTerm rhs = rule.getRight();
        if (rhs.isVariable()) {
            this.addLabeled(rule, addHere, xmlLabelMap);
        } else {
            final TRSFunctionApplication fr = (TRSFunctionApplication) rhs;
            final FunctionSymbol f = fr.getRootSymbol();
            if (headSyms.contains(f)) {
                // okay we have to build pairs lab(l) -> t where t is like lab(r) but
                // the label for the outermost f is decreased in all possible ways
                final Set<TRSVariable> variables = rule.getVariables();
                final int variableCount = variables.size();

                final Pair<ElementValue, TRSTerm> result = new Pair<ElementValue, TRSTerm>(null, null);

                final ElementVectorIterator valueIter = new ElementVectorIterator(variableCount, this.carrierSetSize);
                while (valueIter.hasNext()) {

                    final Iterator<TRSVariable> variableIter = variables.iterator();
                    final Map<TRSVariable, ElementValue> varMap = new HashMap<TRSVariable, ElementValue>(variableCount);
                    for (final int value : valueIter.next()) {
                        varMap.put(variableIter.next(), this.aFunctionalRepresentation.getElementValue(value));
                    }

                    this.generateLabeled(rule.getLeft(), varMap, result, xmlLabelMap);
                    final TRSFunctionApplication lLeft = (TRSFunctionApplication) result.y;

                    final List<? extends TRSTerm> args = fr.getArguments();
                    final ArrayList<TRSTerm> labArgs = new ArrayList<TRSTerm>(args.size());
                    final List<ElementValue> interArgs = new ArrayList<ElementValue>(args.size());
                    for (final TRSTerm arg : args) {
                        this.generateLabeled(arg, varMap, result, xmlLabelMap);
                        labArgs.add(result.y);
                        interArgs.add(result.x);
                    }

                    final ImmutableArrayList<? extends TRSTerm> finalArgs = ImmutableCreator.create(labArgs);

                    // now iterate over all smaller or equal elements of lab(f)
                    final Iterator<List<ElementValue>> smallerI =
                        this.aFunctionalRepresentation.getSmallerElements(interArgs);
                    while (smallerI.hasNext()) {
                        final FunctionSymbol smallerF = this.generateLabeledSymbol(f, smallerI.next(), xmlLabelMap);
                        addHere.add(Rule.create(lLeft, TRSTerm.createFunctionApplication(smallerF, finalArgs)));
                    }
                }
            } else {
                this.addLabeled(rule, addHere, xmlLabelMap);
            }
        }

    }

    @Override
    public void addLabeled(final TRSFunctionApplication term,
        final Set<TRSFunctionApplication> addHere,
        final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {

        final Set<TRSVariable> variables = term.getVariables();
        final int variableCount = variables.size();

        final Pair<ElementValue, TRSTerm> result = new Pair<ElementValue, TRSTerm>(null, null);

        final ElementVectorIterator valueIter = new ElementVectorIterator(variableCount, this.carrierSetSize);
        while (valueIter.hasNext()) {

            final Iterator<TRSVariable> variableIter = variables.iterator();
            final Map<TRSVariable, ElementValue> varMap = new HashMap<TRSVariable, ElementValue>(variableCount);
            for (final int value : valueIter.next()) {
                varMap.put(variableIter.next(), this.aFunctionalRepresentation.getElementValue(value));
            }

            this.generateLabeled(term, varMap, result, xmlLabelMap);
            addHere.add((TRSFunctionApplication) result.y);
        }

    }

    private void generateLabeled(final TRSTerm t,
        final Map<TRSVariable, ElementValue> varMap,
        final Pair<ElementValue, TRSTerm> result,
        final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        if (t.isVariable()) {
            result.x = varMap.get(t);
            result.y = t;
        } else {
            final TRSFunctionApplication ft = (TRSFunctionApplication) t;
            final FunctionSymbol f = ft.getRootSymbol();
            final FunctionRepresentation repr = this.interpretation.get(f);
            final List<? extends TRSTerm> args = ft.getArguments();
            final List<ElementValue> interList = new ArrayList<ElementValue>(args.size());
            final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size());
            for (final TRSTerm arg : args) {
                this.generateLabeled(arg, varMap, result, xmlLabelMap);
                interList.add(result.x);
                newArgs.add(result.y);
            }
            result.x = repr.evaluate(interList);
            final FunctionSymbol labelF = this.generateLabeledSymbol(f, interList, xmlLabelMap);
            result.y = TRSTerm.createFunctionApplication(labelF, ImmutableCreator.create(newArgs));
        }
    }

    private FunctionSymbol generateLabeledSymbol(final FunctionSymbol f,
        final List<ElementValue> interList,
        final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        final Pair<String, List<IntLabel>> pair = this.generateLabel(interList);
        final String s = pair.x;
        final List<IntLabel> labels = pair.y;
        // as we currently have an injective mapping, we just create the labelled symbol
        // and do not check on clashes.
        final FunctionSymbol labelF = FunctionSymbol.create(f.getName() + "." + s, f.getArity());
        final Pair<FunctionSymbol, FunctionSymbolAnnotator> labelMapping =
            new Pair<FunctionSymbol, FunctionSymbolAnnotator>(f, FunctionSymbolAnnotator.createNumlabAnnotator(labels));
        assert (xmlLabelMap != null);
        xmlLabelMap.put(labelF, labelMapping);
        this.labelToOriginMap.put(labelF, f);
        return labelF;
    }

    private Pair<String, List<IntLabel>> generateLabel(final List<ElementValue> interList) {
        String s = "";
        boolean first = true;
        final List<IntLabel> labels = new ArrayList<>(interList.size());
        for (final ElementValue value : interList) {
            if (first) {
                first = false;
            } else {
                s += "-";
            }
            s += value;
            labels.add(new IntLabel(value.getIntValue()));
        }
        return new Pair<>(s, labels);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Collection<FunctionSymbol> labelFS(final FunctionSymbol funcSym,
        final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        final Collection<FunctionSymbol> res = new LinkedHashSet<>();

        final ElementVectorIterator valueIter = new ElementVectorIterator(funcSym.getArity(), this.carrierSetSize);
        while (valueIter.hasNext()) {
            final List<ElementValue> interList = new ArrayList<>(funcSym.getArity());
            final int[] value = valueIter.next();
            for (final int v : value) {
                interList.add(this.aFunctionalRepresentation.getElementValue(v));
            }
            final Pair<String, List<IntLabel>> labelPair = this.generateLabel(interList);
            final String label = labelPair.x;
            final List<IntLabel> labels = labelPair.y;
            final FunctionSymbol labelF = FunctionSymbol.create(funcSym.getName() + "." + label, funcSym.getArity());
            final Pair<FunctionSymbol, FunctionSymbolAnnotator> labelMapping =
                new Pair<FunctionSymbol, FunctionSymbolAnnotator>(funcSym, FunctionSymbolAnnotator.createNumlabAnnotator(labels));
            xmlLabelMap.put(labelF, labelMapping);
            res.add(labelF);
        }

        return res;
    }

    @Override
    public Rule unlabel(final Rule rule) {
        return Rule.create((TRSFunctionApplication) this.unlabel(rule.getLeft()), this.unlabel(rule.getRight()));
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
    public Set<Rule> getDecreasingRules(final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        return this.getDecreasingRules(this.interpretation.keySet(), xmlLabelMap);
    }

    @Override
    public Set<Rule> getDecreasingRules(final Collection<FunctionSymbol> fs,
        final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        final Set<Rule> result = new LinkedHashSet<Rule>(fs.size());
        final Map<Integer, ImmutableArrayList<TRSTerm>> arityToXs = new HashMap<Integer, ImmutableArrayList<TRSTerm>>();
        for (final FunctionSymbol f : fs) {
            final int n = f.getArity();
            if (n != 0) {
                final Integer arity = n;
                ImmutableArrayList<TRSTerm> xs = arityToXs.get(arity);
                if (xs == null) {
                    final ArrayList<TRSTerm> ys = new ArrayList<TRSTerm>(arity);
                    for (int i = 0; i < n; i++) {
                        ys.add(TRSTerm.createVariable("x" + i));
                    }
                    xs = ImmutableCreator.create(ys);
                    arityToXs.put(arity, xs);
                }
                for (final ElementPair pair : this.aFunctionalRepresentation.getDecrElementPairs(n)) {
                    final FunctionSymbol leftF = this.generateLabeledSymbol(f, pair.getLeft(), xmlLabelMap);
                    final FunctionSymbol rightF = this.generateLabeledSymbol(f, pair.getRight(), xmlLabelMap);
                    final TRSFunctionApplication left = TRSTerm.createFunctionApplication(leftF, xs);
                    final TRSFunctionApplication right = TRSTerm.createFunctionApplication(rightF, xs);
                    result.add(Rule.create(left, right));
                }
            }
        }
        return result;
    }

    @Override
    public String toString() {
        return this.interpretation.toString();
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder builder = new StringBuilder();
        builder.append("Interpretation over the domain with elements from 0 to " + (this.carrierSetSize - 1) + ".");
        builder.append(o.linebreak());
        for (final Map.Entry<FunctionSymbol, FunctionRepresentation> entry : this.interpretation.entrySet()) {
            builder.append(entry.getKey().export(o) + ": " + entry.getValue().export(o));
            builder.append(o.cond_linebreak());
        }
        return builder.toString();
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element model = XMLTag.MODEL.createElement(doc);
        for (final Map.Entry<FunctionSymbol, FunctionRepresentation> entry : this.interpretation.entrySet()) {
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

        for (final Map.Entry<FunctionSymbol, FunctionRepresentation> entry : this.interpretation.entrySet()) {
            final Element interpret = CPFTag.INTERPRET.createElement(doc);
            interpret.appendChild(entry.getKey().toCPF(doc, xmlMetaData));
            final Element arity = CPFTag.ARITY.createElement(doc);
            arity.appendChild(doc.createTextNode("" + entry.getKey().getArity()));
            interpret.appendChild(arity);
            interpret.appendChild(entry.getValue().toCPF(doc, xmlMetaData));
            finiteModel.appendChild(interpret);
        }

        return finiteModel;
    }

    @Override
    public String isCPFSupported() {
        return null;
    }

}
