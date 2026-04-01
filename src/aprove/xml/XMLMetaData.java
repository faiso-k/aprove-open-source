package aprove.xml;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IRSwT.Filters.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class XMLMetaData implements Immutable {

    // maps symbols to their original representation before they were labeled with a List of their labels
    private final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> labelMap;
    
    // maps rules to identifier
    private final Map<IGeneralizedRule, String> ltsMap;
    
    // maps function symbols to list of lts-variables
    private final Map<FunctionSymbol, List<String>> ltsVars;

    // this MetaData is the last recently changed
    private final XMLMetaData preData;

    public static XMLMetaData createEmptyMetaData() {
        return null;
    }

    public Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> getLabelMap(){
        return this.labelMap;
    }

    public XMLMetaData getPreData(){
        return this.preData;
    }

    private XMLMetaData(Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> labelMap, Map<IGeneralizedRule, String> ltsMap, final XMLMetaData preData,
	    Map<FunctionSymbol, List<String>> ltsVars) {
        this.labelMap = labelMap;
        this.preData = preData;
        this.ltsMap = ltsMap;
        this.ltsVars = ltsVars;
    }

    /** create a new XMLMetaData
     * @param labelMap - a map which should contain mappings for all symbols of the new obligation
     * @param preData - the previous metadata
     */
    public XMLMetaData(Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> labelMap, final XMLMetaData preData) {
        this(labelMap, null, preData, null); 
    }

    /** create a new XMLMetaData
     * @param labelMap - a map which should contain mappings for all transitions of the new obligation
     */
    public XMLMetaData(Map<IGeneralizedRule, String> ltsMap, Map<FunctionSymbol, List<String>> ltsVars) {
        this(null, ltsMap, null, ltsVars);
    }
    
    public String getLtsId(IGeneralizedRule rule) {
        String id = this.ltsMap.get(rule);
        if (id == null) {
            throw new RuntimeException("Could not find ID for lts-rule " + rule);
        }
        return id;
    }
    
    public XMLMetaData adjustOldNew(Map<IGeneralizedRule, IGeneralizedRule> oldNewMap) {
        Map<IGeneralizedRule, String> map = new HashMap<>();
        for (Map.Entry<IGeneralizedRule, IGeneralizedRule> entry : oldNewMap.entrySet()) {
            map.put(entry.getValue(), this.ltsMap.get(entry.getKey()));
        }
        return new XMLMetaData(map, this.ltsVars);
    }
    
    public XMLMetaData integrateFilter(ArgumentFilterResult filter) {
	Map<FunctionSymbol, List<String>> map = new HashMap<>();
	Map<FunctionSymbol, FunctionSymbol> fMap = filter.x.y;
	for (Map.Entry<FunctionSymbol, List<String>> entry : this.ltsVars.entrySet()) {
	    FunctionSymbol fOld = entry.getKey();
	    List<String> oldVars = entry.getValue();
	    Collection<Integer> is = filter.y.get(fOld);
	    if (is == null) { // filter does not change f
		map.put(fOld, oldVars); 
	    } else {
		FunctionSymbol fNew = fMap.get(fOld);
		List<String> newVars = new ArrayList<>(fNew.getArity());
		int i = 0;
		for (String x : oldVars) {
		    if (!is.contains(i)) {
			newVars.add(x);
		    }
		    i++;
		}
		assert (newVars.size() == fNew.getArity()) : "var map creation failed";
		map.put(fNew, newVars);
	    }
	}
	return new XMLMetaData(this.ltsMap, map);
    }
    
    public XMLMetaData integrateFilter(AbstractFilter filter) {
	Map<FunctionSymbol, List<String>> map = new HashMap<>();	
	for (Map.Entry<FunctionSymbol, List<String>> entry : this.ltsVars.entrySet()) {
	    FunctionSymbol f = entry.getKey();
	    List<String> vars = entry.getValue();
	    if (filter.isFunctionSymbolKnown(f)) {
		int n = f.getArity();
		TRSTerm[] args = new TRSTerm[n];
		int i = 0;
		for (String x : vars) {
		    args[i] = TRSVariable.createVariable(x);
		    i++;
		}
		TRSFunctionApplication fxs = TRSFunctionApplication.createFunctionApplication(f, args);
		TRSFunctionApplication gys = (TRSFunctionApplication) filter.filterTerm(fxs);
		List<TRSTerm> ys = gys.getArguments(); 
		List<String> yss = new ArrayList<>(ys.size());
		for (TRSTerm y : ys) {
		    yss.add(((TRSVariable) y).getName());
		}
		map.put(gys.getFunctionSymbol(), yss);
	    } else {
		map.put(f, vars);
	    }
	}
	return new XMLMetaData(this.ltsMap, map);
    }
    
    public List<String> getVarsForFS(FunctionSymbol f) {
	List<String> list = this.ltsVars.get(f);
	if (list == null) {
	    throw new RuntimeException("could not lookup variables for " + f + " in " + this.ltsVars);
	}
	if (list.size() != f.getArity()) {
	    throw new RuntimeException("length mismatch for " + f + " in " + list);
	}
	return list;
    }

}
