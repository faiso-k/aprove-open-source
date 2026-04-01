package aprove.verification.idpframework.Processors.Filters;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class FilterReplacement implements IDPExportable {

    /**
     * function symbol key is replaced by function symbol value.x retaining those positions i where value.y[i] == true
     */
    public final FunctionSymbolReplacement functionSymbolReplacement;

    public final VarRenaming variableReplacement;


    public FilterReplacement() {
        this(new FunctionSymbolReplacement(),
            VarRenaming.EMPTY_RENAMING);
    }

    public FilterReplacement(final FunctionSymbolReplacement functionSymbolReplacement,
        final VarRenaming variableReplacement) {
            this.functionSymbolReplacement = functionSymbolReplacement;
            this.variableReplacement = variableReplacement;
    }

    public FilterReplacement appendFilter(final FilterReplacement appended) {
        final FunctionSymbolReplacement composedFSReplacement = this.functionSymbolReplacement.compose(appended.functionSymbolReplacement);
        final VarRenaming composedVariableReplacement = this.variableReplacement.compose(appended.variableReplacement);

        return new FilterReplacement(composedFSReplacement, composedVariableReplacement);
    }

    @Override
    public final String export(final Export_Util o) {
        return this.export(o, IDPExportable.DEFAULT_LEVEL);
    }

    @Override
    public final String export(final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        final StringBuilder sb = new StringBuilder();
        this.export(sb, o, verbosityLevel);
        return sb.toString();
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel level) {

        if (this.functionSymbolReplacement.isEmpty()) {
            sb.append("No function symbols are changed.");
        } else {
            final List<List<String>> tableEntries = new LinkedList<List<String>>();
            for (final IFunctionSymbol<?> oldSym : this.functionSymbolReplacement.keySet()) {
                final ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>> p = this.functionSymbolReplacement.get(oldSym);

                final IFunctionSymbol<?> newSym = p.x;
                if (oldSym.equals(newSym)) {
                    continue;
                }

                final StringBuilder leftSb = new StringBuilder();
                leftSb.append(oldSym.getName()).append("(");
                boolean first = true;
                int i = 1;
                for (final Boolean usedVar : p.y) {
                    if (!first) {
                        leftSb.append(", ");
                    }
                    if (usedVar) {
                        leftSb.append("x" + i++);
                    } else {
                        leftSb.append(o.fontcolor("x" + i++, Color.RED));
                    }
                    first = false;
                }
                leftSb.append(")");

                final StringBuilder rightSb = new StringBuilder();
                rightSb.append(newSym.getName()).append("(");
                first = true;
                i = 1;
                for (final Boolean usedVar : p.y) {
                    if (usedVar) {
                        if (!first) {
                            rightSb.append(", ");
                        }
                        rightSb.append("x" + i);
                        first = false;
                    }
                    i++;
                }
                rightSb.append(")");

                final ArrayList<String> rowEntries = new ArrayList<String>(3);
                rowEntries.add(leftSb.toString());
                rowEntries.add(o.rightarrow());
                rowEntries.add(rightSb.toString());
                tableEntries.add(rowEntries);
            }

            sb.append(o.table(tableEntries));
        }
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result =
            prime
                * result
                + ((this.functionSymbolReplacement == null) ? 0
                    : this.functionSymbolReplacement.hashCode());
        result =
            prime
                * result
                + ((this.variableReplacement == null) ? 0
                    : this.variableReplacement.hashCode());
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final FilterReplacement other = (FilterReplacement) obj;
        if (this.functionSymbolReplacement == null) {
            if (other.functionSymbolReplacement != null) {
                return false;
            }
        } else if (!this.functionSymbolReplacement.equals(other.functionSymbolReplacement)) {
            return false;
        }
        if (this.variableReplacement == null) {
            if (other.variableReplacement != null) {
                return false;
            }
        } else if (!this.variableReplacement.equals(other.variableReplacement)) {
            return false;
        }
        return true;
    }



}
