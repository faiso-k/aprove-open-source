package aprove.verification.dpframework.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * continuously generate a mapping from function symbols and
 * parameter lists to labeled function symbols
 *
 * @author Andreas Kelle-Emden
 *
 */
public class RootLabelingNameArray {

    private Map<Pair<FunctionSymbol, List<FunctionSymbol>>, FunctionSymbol> symMap;

    private RootLabelingNameArray() {
        this.symMap = new LinkedHashMap<Pair<FunctionSymbol, List<FunctionSymbol>>, FunctionSymbol>();
    }

    public static RootLabelingNameArray create() {
        return new RootLabelingNameArray();
    }

    public FunctionSymbol getLabeled(Pair<FunctionSymbol, List<FunctionSymbol>> original, Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        FunctionSymbol symRes;
        synchronized(this) {
            symRes = this.symMap.get(original);
        }
        if (symRes == null) {
            // Create new entry with a copy of original
            // and generate labeled name
            StringBuilder newName = new StringBuilder();
            FunctionSymbol sym = original.x;
            newName.append(sym.getName());
            int arity = sym.getArity();
            List<FunctionSymbol> params = new ArrayList<FunctionSymbol>(arity);
            if (arity > 0) {
                newName.append("_{");
                boolean comma = false;
                for (FunctionSymbol p : original.y) {
                    params.add(p);
                    if (comma) {
                        newName.append(',');
                    } else {
                        comma = true;
                    }
                    // newName += p.getName() + (p.getArity() == 0 ? "" : "_"+p.getArity())
                    newName.append(p.getName());
                    if(p.getArity()> 0){
                        newName.append("_");
                        newName.append(p.getArity());
                    }
                }
                newName.append('}');
            }
            symRes = FunctionSymbol.create(newName.toString(), arity);

            FunctionSymbolAnnotator xmlSymLabel = FunctionSymbolAnnotator.createSymlabAnnotator(params);
            Pair<FunctionSymbol, FunctionSymbolAnnotator> xmlOrigLabelPair = new Pair<>(sym, xmlSymLabel);

            Pair<FunctionSymbol, List<FunctionSymbol>> newKey = new Pair<>(original.x, params);
            synchronized (this) {
                xmlLabelMap.put(symRes, xmlOrigLabelPair);
                this.symMap.put(newKey, symRes);
            }
        }
        return symRes;
    }
}
