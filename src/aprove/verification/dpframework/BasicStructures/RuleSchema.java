package aprove.verification.dpframework.BasicStructures;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * A rule schema is a rule l -> _ with no restrictions on the rhs at all,
 * i.e., it is a pair of objects where the lhs is a term that is not a variable
 * and the rhs is some arbitrary object.
 * Currently this includes a term or a collection of terms.
 * 
 * In order to compare two rule schema, we store its
 * standard representation in stdL -> _.
 *
 * @author Jan-Christoph Kassing
 */
public abstract class RuleSchema 
	implements
		Immutable,
		Exportable,
		XMLObligationExportable,
        CPFAdditional,
        Comparable<RuleSchema>,
        HasVariables,
        HasTRSTerms,
        HasRootSymbol,
        HasLHS,
        HasFunctionSymbols
		{
	
	/*
     * real values
     */
    protected TRSFunctionApplication l;

    protected int hashCode;

    /**
     * returns the hashcode
     */
    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public abstract boolean equals(Object other);

    @Override
    public abstract int compareTo(RuleSchema other);

    /**
     * returns the lhs
     */
    @Override
    public TRSFunctionApplication getLeft() {
        return this.l;
    }

    @Override
    public abstract Set<TRSTerm> getTerms();

    /**
     * returns the set of variables occurring in this rule
     */
    @Override
    public abstract Set<TRSVariable> getVariables();

    /**
     * returns the set of functionSymbols occurring in this rule.
     * the resulting set may be modified
     */
    @Override
    public abstract Set<FunctionSymbol> getFunctionSymbols();

    /**
     * returns the root symbol of this rule,
     * i.e. the root symbol of the lhs.
     */
    @Override
    public FunctionSymbol getRootSymbol() {
        return this.getLeft().getRootSymbol();
    }

    /**
     * returns the lhs in standardRepresentation.
     * (constant time)
     */
    public abstract TRSFunctionApplication getLhsInStandardRepresentation();

    /**
     * returns the rhs in standardRepresentation.
     * (constant time)
     */
    public abstract Object getRhsInStandardRepresentation();

    /**
     * returns a the standard representation of this
     * rule where l = stdL and r = stdR.
     * (constant time)
     * @see getWithRenumberedVariables
     */
    public abstract RuleSchema getStandardRepresentation();

    public static Map<FunctionSymbol, Set<TRSFunctionApplication>> computeLhsOfRulesAsMapInStandardRepresentation(
        Map<FunctionSymbol, ? extends Set<? extends RuleSchema>> ruleMap
    ) {
        final Map<FunctionSymbol, Set<TRSFunctionApplication>> res =
            new LinkedHashMap<FunctionSymbol, Set<TRSFunctionApplication>>();
        for (Map.Entry<FunctionSymbol, ? extends Set<? extends RuleSchema>> entry : ruleMap.entrySet()) {
            final Set<TRSFunctionApplication> lhss = new LinkedHashSet<TRSFunctionApplication>();
            for (RuleSchema rule : entry.getValue()) {
                lhss.add(rule.getLhsInStandardRepresentation());
            }
            res.put(entry.getKey(), lhss);
        }
        return res;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }
    
    @Override
    public abstract String export(Export_Util eu);

    @Override
    public abstract Element toDOM(Document doc, XMLMetaData xmlMetaData);

    @Override
    public abstract Element toCPF(Document doc, XMLMetaData xmlMetaData);

}
