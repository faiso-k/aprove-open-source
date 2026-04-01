/**
 *
     * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.idpGraph;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class Node implements Exportable, IDPExportable {

    public final GeneralizedRule rule;
    public final int id;
    public final ImmutableMap<TRSVariable, TRSVariable> loopSubstitution;

    public Node (GeneralizedRule rule, int id, ImmutableMap<TRSVariable, TRSVariable> loopSubstitution) {
        this.rule = rule;
        this.id = id;
        this.loopSubstitution = loopSubstitution;
    }

    /**
     * @return the encapsulated rule
     */
    public GeneralizedRule getRule() {
        return this.rule;
    }

    @Override
    public int hashCode() {
        return 31 * this.id;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final Node other = (Node) obj;
        return other.id == this.id && other.rule.getLeft().equals(this.rule.getLeft()) && other.rule.getRight().equals(this.rule.getRight());
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public Object exportId(Export_Util o) {
        return "(" + this.id + ")";
    }

    @Override
    public String export(Export_Util o) {
        return this.export(o, null, VerbosityLevel.MIDDLE);
    }

    @Override
    public String export(Export_Util o, IDPPredefinedMap predefinedMap, VerbosityLevel verbosityLevel) {
        final StringBuilder s = new StringBuilder();
        s.append("(" + this.id + "): ");
        if (Globals.DEBUG_COTTO && o instanceof Dotty_Util) {
            // Only show names of function symbols, I don't care for the arguments (too much information! :)
            s.append(this.rule.getLeft().getRootSymbol().getName());
            final TRSTerm right = this.rule.getRight();
            if (right instanceof TRSFunctionApplication) {
                final TRSFunctionApplication faRight = (TRSFunctionApplication) right;
                s.append(o.rightarrow());
                s.append(faRight.getRootSymbol().getName());
            }
        } else {
            s.append(IDPExport.exportRule(this.rule, o, predefinedMap));
        }
        return s.toString();
    }



}
