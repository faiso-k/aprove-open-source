package aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.xml.*;

public class GAtomicVar implements GPolyVar, XMLObligationExportable, CPFAdditional {

    /**
     * The variable's name.
     */
    private final String varName;

    /**
     * The variable's hashcode.
     */
    private final int hashCode;

    /**
     * Create a new variable with the given name.
     * @param name the variable's name.
     */
    public GAtomicVar(final String name) {
        if (Globals.useAssertions) {
            assert (name != null);
        }
        this.varName = name;
        this.hashCode = name.hashCode() + 3829038;

    }

    /**
     * This atomic variable is affected iff the variable set includes "this".
     * @return true iff the given set includes "this".
     */
    @Override
    public boolean isAffected(final Collection<? extends GPolyVar> vars) {
        return vars.contains(this);
    }

    /**
     * @return the replacement polynomial indexed by "this".
     * @param replacement the replacement map.
     */
    @Override
    public <A extends GPolyCoeff, B extends GPolyVar> GPoly<A, B> replace(final Map<B, ? extends GPoly<A, B>> replacement) {
        return replacement.get(this);
    }

    /**
     * @param name the variable's name.
     * @return a new variable with the given name.
     */
    public static GPolyVar createVariable(final String name) {
        return new GAtomicVar(name);
    }

    /**
     * @return the variable's name.
     */
    @Override
    public String getName() {
        return this.varName;
    }

    /**
     * @return the variable's name.
     */
    @Override
    public String toString() {
        return this.varName;
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element e = XMLTag.VARIABLE.createElement(doc);
        XMLAttribute.VARNAME.setAttribute(e, this.varName);
        return e;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return CPFTag.VARIABLE.create(doc,
                doc.createTextNode(this.varName));
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder buffer = new StringBuilder();
        final String[] splits = this.varName.split("_", 2);
        buffer.append(splits[0]);
        if (splits.length > 1) {
            buffer.append(eu.sub(splits[1]));
        }

        // unlikely though it may (rightfully) seem, there could well be more
        // "_"s in varName; do not omit the corresponding parts of the name
        for (int i = 2; i < splits.length; ++i) {
            buffer.append("_");
            buffer.append(splits[i]);
        }
        return buffer.toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        return this.hashCode;
    }

    /**
     * {@inheritDoc}
     */
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
        final GAtomicVar other = (GAtomicVar) obj;
        if (this.hashCode != other.hashCode) {
            return false;
        }
        if (this.varName == null) {
            if (other.varName != null) {
                return false;
            }
        } else if (!this.varName.equals(other.varName)) {
            return false;
        }
        return true;
    }
}
