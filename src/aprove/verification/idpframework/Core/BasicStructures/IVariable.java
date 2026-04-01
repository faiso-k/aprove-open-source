/*
 * Created on 11.04.2005
 */
package aprove.verification.idpframework.Core.BasicStructures;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * A IVariable<?> is a String and a Domain.
 * @author Martin Pluecker, copied from thiemann
 */
public class IVariable<D extends SemiRing<D>> extends ITerm<D> implements HasName, HasSignum, PolyVariable<D> {

    // FIXME try to make package internal (refactoring)
    public static <D extends SemiRing<D>> IVariable<D> create(final String name, final SemiRingDomain<D> domain) {
        return new IVariable<D>(name, domain);
    }

    /*
     * real values
     */
    protected final String varName;

    protected final SemiRingDomain<D> domain;

    /*
     * computed / cached values
     */
    private final int hashCode;

    /**
     * a IVariable<?> is constructed by a non-null string and domain
     * @param name
     */
    protected IVariable(final String name, final SemiRingDomain<D> domain) {
        if (Globals.useAssertions) {
            assert(domain != null);
            assert(name != null && !name.equals(""));
            boolean isInt = true;
            try {
                Integer.parseInt(name);
            } catch (NumberFormatException e) {
                isInt = false;
            }
            assert(!isInt);
        }
        this.varName = name;
        this.domain = domain;
        this.hashCode =
            name.hashCode() + (domain != null ? domain.hashCode() * 11 : 0)
            + 3829038;
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
        if (other instanceof IVariable<?>) {
            final IVariable<?> v = (IVariable<?>) other;
            if (this.hashCode != v.hashCode) {
                return false;
            }
            if (this.domain == null) {
                if (v.domain != null) {
                    return false;
                }
            } else if (!this.domain.equals(v.domain)) {
                return false;
            }
            return this.varName.equals(v.varName);
        }
        return false;
    }

    @Override
    public int compareTo(final ITerm<?> t) {
        if (t.isVariable()) {
            return this.varName.compareTo(((IVariable<?>) t).varName);
        } else {
            return -1;
        }
    }

    @Override
    public void collectVariables(final Set<IVariable<?>> vars) {
        vars.add(this);
    }

    @Override
    protected void collectVariablePositions(final IPosition pos,
        final Map<IVariable<?>, List<IPosition>> varPositions) {
        List<IPosition> positions = varPositions.get(this);
        if (positions == null) {
            positions = new ArrayList<IPosition>();
            positions.add(pos);
            varPositions.put(this, positions);
        } else {
            positions.add(pos);
        }
    }

    @Override
    public void collectFunctionSymbols(final Set<IFunctionSymbol<?>> fs) {
        // nothing todo here
    }

    @Override
    public void computeFunctionSymbolCount(final Map<IFunctionSymbol<?>, Integer> map) {
        // nothing todo here
    }

    @Override
    protected void collectPositions(final IPosition pos,
        final Collection<IPosition> pts) {
        pts.add(pos);
    }

    @Override
    protected void collectPositionsAndSubTerms(final IPosition pos,
        final Collection<Pair<IPosition, ITerm<?>>> pts,
        final boolean dropRoot,
        final boolean dropVars) {
        if (dropRoot || dropVars) {
            // do nothing
        } else {
            pts.add(new Pair<IPosition, ITerm<?>>(pos, this));
        }
    }

    @Override
    protected void collectSortedPositionssWithSubTerms(final IPosition pos,
        final CollectionMap<IFunctionSymbol<?>, Pair<IPosition, ITerm<?>>> res) {
        res.add(null, new Pair<IPosition, ITerm<?>>(pos, this));
    }

    @Override
    protected <E extends SemiRing<E>> boolean collectDeepestFunctionApplication(final Collection<IFunctionSymbol<E>> fs,
        final IPosition pos,
        final Map<IPosition, IFunctionApplication<E>> res) {
        return false;
    }

    public IVariable<D> applyVarSubstitution(final VarRenaming sigma) {
        final IVariable<D> subst = sigma.substituteTerm(this);
        return subst != null ? subst : this;
    }

    @Override
    public ITerm<D> processSubstitution(final BasicTermSubstitution sigma) {
        final ITerm<D> subst = sigma.substituteTerm(this);
        return subst != null ? subst : this;
    }

    @Override
    public ImmutablePair<IVariable<?>, Integer> renumberVariables(final Map<IVariable<?>, IVariable<?>> map,
        final String prefix,
        Integer nr) {
        IVariable<?> replacement = map.get(this);
        if (replacement == null) {
            final String newName = prefix + nr;
            nr++;
            if (this.varName.equals(newName)) {
                replacement = this;
                map.put(this, replacement);
            } else {
                replacement = IVariable.create(newName, this.domain);
                map.put(this, replacement);
            }
        }
        return new ImmutablePair<IVariable<?>, Integer>(replacement, nr);
    }

    @Override
    public ITerm<?> renameVariables(final aprove.verification.idpframework.Core.Utility.FreshVarGenerator gen) {
        return this.renameVariables(gen, new HashMap<IVariable<?>, IVariable<?>>());
    }

    @Override
    public IVariable<D> renameVariables(final aprove.verification.idpframework.Core.Utility.FreshVarGenerator gen,
        final Map<IVariable<?>, IVariable<?>> renameVariables) {
        IVariable<D> renamed = (IVariable<D>) renameVariables.get(this);

        if (renamed == null) {
            renamed = gen.getFreshVariable(this, false);
            renameVariables.put(this, renamed);
        }

        return renamed;
    }

    @Override
    protected boolean testForLessVariables(final Map<IVariable<?>, Integer> map) {
        final int i = map.get(this);
        if (i == 0) {
            return false;
        } else {
            map.put(this, i - 1);
            return true;
        }
    }

    @Override
    public void computeVariableCount(final Map<IVariable<?>, Integer> map) {
        final Integer old = map.put(this, 1);
        if (old != null) {
            map.put(this, old + 1);
        }
    }

    @Override
    public Map<IVariable<?>, ITerm<?>> extendMatchingSubstitution(final Map<IVariable<?>, ITerm<?>> sigma,
        final ITerm<?> that, final boolean weakUnknownDomain) {
        final ITerm<?> thisSigma = sigma.get(this);
        if (thisSigma == null) {
            sigma.put(this, that);
            return sigma;
        } else {
            if (thisSigma.equals(that)) {
                return sigma;
            } else {
                return null;
            }
        }
    }

    @Override
    public boolean linearMatches(final ITerm<?> that) {
        return true;
    }

    @Override
    protected boolean isLinear(final Set<IVariable<?>> alreadyPresent) {
        return alreadyPresent.add(this);
    }

    @Override
    public void collectSubTerms(final Set<ITerm<?>> subs, final boolean dropVars) {
        if (dropVars) {
            // nothing to do
        } else {
            subs.add(this);
        }
    }

    @Override
    public ITerm<?> replaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        return this;
    }

    @Override
    protected ITerm<?> uncheckedreplaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        return this;
    }

    @Override
    public String getBooleanPolyVarName() {
        return this.varName;
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        sb.append(eu.italic(eu.escape(this.varName)));

        if (this.domain != null
            && verbosityLevel.compareTo(VerbosityLevel.HIGH) >= 0) {
            sb.append(": ");
            sb.append(this.domain.export(eu));
        }
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        final Map<String, String> m = new HashMap<String, String>();
        m.put("name", this.varName);
        return m;
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        final XmlContentsMap contents = new XmlContentsMap();

        if (this.domain != null) {
            contents.add(this.domain);
        }

        return contents;
    }

    @Override
    public String getName() {
        return this.varName;
    }

    @Override
    public SemiRingDomain<D> getDomain() {
        return this.domain;
    }

    @Override
    public Signum getSignum() {
        return this.domain.getSignum();
    }

    @Override
    public boolean isVariable() {
        return true;
    }

    @Override
    public boolean isConstant() {
        return false;
    }

    @Override
    public int getDepth() {
        return 0;
    }

    @Override
    public int getDepthConstant() {
        return 0;
    }

    @Override
    public int getSize() {
        return 1;
    }

    /**
     * help-method for the method "linearize(IVariable<?>)" in the super-class
     * "ITerm<?>"
     * @author Martin Pluecker, copied from Sebastian Weise
     */
    @Override
    protected ITerm<D> helpLinearize(final IVariable<?> variable,
        final Set<IVariable<?>> toAvoid) {

        if (!this.equals(variable)) {
            return this; // ITerm.createVariable(getName());
        } else {
            final IVariable<D> result =
                (new aprove.verification.idpframework.Core.Utility.FreshVarGenerator(toAvoid)).getFreshVariable(
                    this, false);
            toAvoid.add(result);
            return result;
        }
    }

    @Override
    public boolean isMax() {
        return false;
    }

    @Override
    public boolean isRealVar() {
        return true;
    }

    @Override
    public D getRing() {
        return this.domain.getRing();
    }

    @Override
    public boolean isGroundTerm() {
        return false;
    }

}
