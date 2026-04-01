package aprove.verification.oldframework.IRSwT.Sorts;

import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Maps symbols and direct successor position to sorts that can occur there.
 * @author Matthias Hoelzel
 *
 */
public class SortDictionary implements Exportable {
    /**
     * Stores the information.
     */
    private final LinkedHashMap<FunctionSymbol, ArrayList<Sort>> dictionary;
    
    /**
     * Creates a new dictionary.
     * @param dict maps symbols to lists of sorts
     */
    public SortDictionary(final LinkedHashMap<FunctionSymbol, ArrayList<Sort>> dict) {
        this.dictionary = new LinkedHashMap<>(dict);
    }
    
    public boolean isFunctionSymbolKnown(FunctionSymbol f) {
	return this.dictionary.containsKey(f);
    }

    /**
     * Returns the sort of some argument.
     * @param sym some function symbols
     * @param pos position of the argument
     * @return a sort
     */
    public Sort getSort(final FunctionSymbol sym, final int pos) {
        final ArrayList<Sort> sortArray = this.dictionary.get(sym);
        if (sortArray == null || sortArray.size() <= pos || pos < 0) {
            assert false : "Invalid symbol, position or array!";
            return null;
        }
        return sortArray.get(pos);
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        sb.append("SortDictionary: ");
        final Iterator<Entry<FunctionSymbol, ArrayList<Sort>>> entryIter = this.dictionary.entrySet().iterator();
        while (entryIter.hasNext()) {
            final Entry<FunctionSymbol, ArrayList<Sort>> e = entryIter.next();
            sb.append(e.getKey().toString());
            sb.append('(');
            final Iterator<Sort> iter = e.getValue().iterator();
            while (iter.hasNext()) {
                final Sort s = iter.next();
                sb.append(s.toString());
                if (iter.hasNext()) {
                    sb.append(", ");
                }
            }
            sb.append(')');
            if (entryIter.hasNext()) {
                sb.append("; ");
            }
        }
        return sb.toString();
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder sb = new StringBuilder();
        sb.append(eu.linebreak());
        final Iterator<Entry<FunctionSymbol, ArrayList<Sort>>> entryIter = this.dictionary.entrySet().iterator();
        while (entryIter.hasNext()) {
            final Entry<FunctionSymbol, ArrayList<Sort>> e = entryIter.next();
            sb.append(e.getKey().export(eu));
            sb.append(eu.escape("("));
            final Iterator<Sort> iter = e.getValue().iterator();
            while (iter.hasNext()) {
                final Sort s = iter.next();
                sb.append(eu.tttext(s.toString()));
                if (iter.hasNext()) {
                    sb.append(eu.escape(", "));
                }
            }
            sb.append(eu.escape(")"));
            if (entryIter.hasNext()) {
                sb.append(eu.linebreak());
            }
        }
        return sb.toString();
    }
}
