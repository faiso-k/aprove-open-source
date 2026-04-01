/*
 * Created on 11.04.2005
 */
package aprove.verification.idpframework.Polynomials;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * A PolyVariable is a String and a Domain and possibly a set of
 * Max-Polynomials.
 * @author Martin Pluecker, copied from thiemann
 */
public final class PolyMaxVariable<C extends SemiRing<C>> implements
        PolyVariable<C> {

    /**
     * a IVariable is constructed by a non-null set of max terms
     * @param name
     */
    static <C extends SemiRing<C>> PolyMaxVariable<C> create(final ImmutableSet<Polynomial<C>> maxs,
        final PolyFactory factory, final C ring) {
        return new PolyMaxVariable<C>(maxs, factory, ring);
    }

    /*
     * real values
     */
    private final ImmutableSet<Polynomial<C>> maxs;

    /*
     * computed / cached values
     */
    private final int hashCode;

    private final PolyFactory factory;

    private volatile ImmutableSet<IVariable<C>> variables;

    private final C ring;

    private PolyMaxVariable(final ImmutableSet<Polynomial<C>> maxs,
            final PolyFactory factory, final C ring) {
        if (Globals.useAssertions) {
            assert (maxs != null);
        }
        this.maxs = maxs;
        this.factory = factory;
        this.ring = ring;
        this.hashCode = ring.zero().hashCode() * 11 + maxs.hashCode() * 121 + +3829038;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public boolean equals(final Object other) {
        if (this == other) {
            return true;
        }
        if (other instanceof PolyMaxVariable) {
            final PolyMaxVariable<?> v = (PolyMaxVariable<?>) other;
            if (this.hashCode != v.hashCode) {
                return false;
            }
            return this.ring.isSameRing(v.ring) && this.maxs.equals(v.maxs);
        }
        return false;
    }

    public void collectVariables(final Set<PolyMaxVariable<C>> vars) {
        vars.add(this);
    }

    @Override
    public final String toString() {
        return this.export(new PLAIN_Util());
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
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        sb.append(eu.fontcolor(eu.escape("MAX"), Color.RED));
        if (this.maxs != null) {
            sb.append("(");
            final Iterator<Polynomial<C>> i = this.maxs.iterator();
            while (i.hasNext()) {
                final Polynomial<C> p = i.next();
                sb.append(p.export(eu));
                if (i.hasNext()) {
                    sb.append(", ");
                }
            }
            sb.append(")");
        }
    }

    public ImmutableSet<IVariable<C>> getVariables() {
        if (this.variables == null) {
            synchronized (this) {
                if (this.variables == null) {
                    final Set<IVariable<C>> res =
                        new LinkedHashSet<IVariable<C>>();

                    for (final Polynomial<C> maxPoly : this.maxs) {
                        res.addAll(maxPoly.getVariables());
                    }

                    return this.variables = ImmutableCreator.create(res);
                }
            }
        }
        return this.variables;
    }


    public PolyMaxVariable<C> applySubstitution(final BasicPolySubstitution sigma) {
        final Set<Polynomial<C>> newMaxs = new LinkedHashSet<Polynomial<C>>();
        boolean changed = false;
        for (final Polynomial<C> poly : this.maxs) {
            final Polynomial<C> newPoly = poly.applySubstitution(sigma);
            newMaxs.add(newPoly);
            if (newPoly != poly) {
                changed = true;
            }
        }

        if (changed) {
            return this.factory.createVariable(this.ring, ImmutableCreator.create(newMaxs));
        } else {
            return this;
        }
    }

    public PolyMaxVariable<C> applyVarSubstitution(final Map<IVariable<C>, C> sigma) {
        final Set<Polynomial<C>> newMaxs = new LinkedHashSet<Polynomial<C>>();
        boolean changed = false;

        for (final Polynomial<C> poly : this.maxs) {
            final Polynomial<C> newPoly = poly.applyVarSubstitution(sigma);
            newMaxs.add(newPoly);

            if (newPoly != poly) {
                changed = true;
            }
        }

        if (changed) {
            return this.factory.createVariable(this.ring, ImmutableCreator.create(newMaxs));
        } else {
            return this;
        }
    }

    @Override
    public String getName() {
        return "";
    }

    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Polynomials.PVariable#isMax()
     */
    @Override
    public boolean isMax() {
        return true;
    }

    @Override
    public boolean isRealVar() {
        return false;
    }

    public ImmutableSet<Polynomial<C>> getArguments() {
        return this.maxs;
    }

    @Override
    public C getRing() {
        return this.ring;
    }

    @Override
    public XmlContentsMap getXmlContents(XmlExporter xe) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Map<String, String> getXmlAttribs(XmlExporter xe) {
        // TODO Auto-generated method stub
        return null;
    }

}

