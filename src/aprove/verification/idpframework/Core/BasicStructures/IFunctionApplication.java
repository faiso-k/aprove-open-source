/*
 * Created on 11.04.2005
 */
package aprove.verification.idpframework.Core.BasicStructures;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * A IFunctionApplication<?> is a term that consists of a function symbol f/n and a
 * list of arguments of size n. Two IFunctionApplication<?>s are equal iff their
 * root-symbol is equal and their arguments are equal.
 * @author Martin Pluecker, copied from Martin Pluecker, copied from thiemann
 */
public final class IFunctionApplication<D extends SemiRing<D>> extends ITerm<D> implements XmlExportable, HasRootSymbol<D> {

    public static <D extends SemiRing<D>> IFunctionApplication<D> create(final IFunctionSymbol<D> f,
        final ImmutableArrayList<? extends ITerm<?>> args) {
        return new IFunctionApplication<D>(f, args);
    }

    public static <D extends SemiRing<D>> IFunctionApplication<D> create(final IFunctionSymbol<D> f,
        final ITerm<?>...args) {
        final ArrayList<ITerm<?>> argsList = new ArrayList<ITerm<?>>(args.length);
        for (final ITerm<?> t : args) {
            argsList.add(t);
        }
        return new IFunctionApplication<D>(f, ImmutableCreator.create(argsList));
    }

    /*
     * real values
     */
    private final IFunctionSymbol<D> f;
    private final ImmutableArrayList<? extends ITerm<?>> args;

    /*
     * cached / computed values
     */
    private final int hashCode;

    /**
     * @param f - a non null function symbol of arity n
     * @param args - a vector of length n where all terms are non-null
     */
    public IFunctionApplication(final IFunctionSymbol<D> f,
        final ImmutableArrayList<? extends ITerm<?>> args) {
        if (Globals.useAssertions) {
            assert (IFunctionApplication.checkValidConstructorArgs(f, args));
        }
        this.f = f;
        this.args = args;
        int hash = f.hashCode() * 93201;
        for (final ITerm<?> arg : args) {
            hash += arg.hashCode() * 323289;
        }
        this.hashCode = hash;
    }

    /**
     * a method for checking whether the arguments for the constructors are
     * okay. Used for assertions
     */
    private static boolean checkValidConstructorArgs(final IFunctionSymbol<?> f,
        final List<? extends ITerm<?>> args) {
        if (f != null && args != null && f.getArity() == args.size()) {
            for (final ITerm<?> arg : args) {
                if (arg == null) {
                    return false;
                }
            }
            return true;
        } else {
            return false;
        }
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
        if (other instanceof IFunctionApplication<?>) {
            final IFunctionApplication<?> t = (IFunctionApplication<?>) other;
            return this.hashCode == t.hashCode && this.f.equals(t.f)
            && this.args.equals(t.args);
        }
        return false;
    }

    @Override
    public int compareTo(final ITerm<?> t) {
        if (t.isVariable()) {
            return 1;
        } else {
            final IFunctionApplication<?> gt = (IFunctionApplication<?>) t;
            int compare = gt.f.compareTo(this.f);
            if (compare == 0) {
                int i = 0;
                final ArrayList<? extends ITerm<?>> otherArgs = gt.args;
                for (final ITerm<?> thisArg : this.args) {
                    compare = thisArg.compareTo(otherArgs.get(i));
                    if (compare == 0) {
                        i++;
                    } else {
                        return compare;
                    }
                }
                return 0;
            } else {
                return compare;
            }
        }
    }

    /**
     * returns the root symbol of this term, i.e. root(f(t_1, ..., t_n)) = f
     */
    @Override
    public IFunctionSymbol<D> getRootSymbol() {
        return this.f;
    }

    /**
     * returns the arguments of this ITerm<?> as immutable vector. (constant time)
     */
    @SuppressWarnings("unchecked")
    public ImmutableArrayList<ITerm<?>> getArguments() {
        /*
         * Casting ImmutableArrayList<? extends ITerm<?>> to ImmutableArrayList<ITerm<?>>
         * is ok here, as the list is immutable, so it can not be compromised
         * by e.g. adding IFunctionApplication<?>s to a ImmutableArrayList<IVariable<?>>.
         */
        return (ImmutableArrayList<ITerm<?>>) this.args;
    }

    /**
     * returns the index'th argument of this ITerm. (constant time)
     */
    public ITerm<?> getArgument(final int index) {
        return this.args.get(index);
    }

    @Override
    public void collectVariables(final Set<IVariable<?>> vars) {
        for (final ITerm<?> arg : this.args) {
            arg.collectVariables(vars);
        }
    }

    @Override
    protected void collectVariablePositions(final IPosition pos,
        final Map<IVariable<?>, List<IPosition>> varPositions) {
        int i = 0;
        for (final ITerm<?> arg : this.args) {
            final IPosition posArg = pos.append(i);
            arg.collectVariablePositions(posArg, varPositions);
            i++;
        }
    }

    @Override
    public void collectFunctionSymbols(final Set<IFunctionSymbol<?>> fs) {
        fs.add(this.f);
        for (final ITerm<?> arg : this.args) {
            arg.collectFunctionSymbols(fs);
        }
    }

    @Override
    public void computeFunctionSymbolCount(final Map<IFunctionSymbol<?>, Integer> map) {
        final Integer old = map.put(this.f, 1);
        if (old != null) {
            map.put(this.f, old + 1);
        }
        for (final ITerm<?> arg : this.args) {
            arg.computeFunctionSymbolCount(map);
        }
    }

    public Set<IFunctionSymbol<?>> getNonRootIFunctionSymbols() {
        final Set<IFunctionSymbol<?>> fs = new LinkedHashSet<IFunctionSymbol<?>>();
        for (final ITerm<?> arg : this.args) {
            arg.collectFunctionSymbols(fs);
        }
        return fs;
    }

    @Override
    protected void collectPositions(final IPosition pos,
        final Collection<IPosition> pts) {
        pts.add(pos);
        int i = 0;
        for (final ITerm<?> arg : this.args) {
            final IPosition posArg = pos.append(i);
            arg.collectPositions(posArg, pts);
            i++;
        }
    }

    @Override
    protected void collectPositionsAndSubTerms(final IPosition pos,
        final Collection<Pair<IPosition, ITerm<?>>> pts,
        final boolean dropRoot,
        final boolean dropVars) {
        if (dropRoot) {
            // do not add this position
        } else {
            pts.add(new Pair<IPosition, ITerm<?>>(pos, this));
        }
        int i = 0;
        for (final ITerm<?> arg : this.args) {
            final IPosition posArg = pos.append(i);
            arg.collectPositionsAndSubTerms(posArg, pts, false, dropVars);
            i++;
        }
    }

    @Override
    protected void collectSortedPositionssWithSubTerms(final IPosition pos,
        final CollectionMap<IFunctionSymbol<?>, Pair<IPosition, ITerm<?>>> res) {
        res.add(this.f, new Pair<IPosition, ITerm<?>>(pos, this));
        int i = 0;
        for (final ITerm<?> arg : this.args) {
            final IPosition posArg = pos.append(i);
            arg.collectSortedPositionssWithSubTerms(posArg, res);
            i++;
        }
    }

    @SuppressWarnings("unchecked")
    @Override
    protected <E extends SemiRing<E>> boolean collectDeepestFunctionApplication(final Collection<IFunctionSymbol<E>> fs,
        final IPosition pos,
        final Map<IPosition, IFunctionApplication<E>> res) {
        boolean foundNested = false;

        final int argsSize = this.args.size();

        for (int i = 0; i < argsSize ; i++) {
            final IPosition posArg = pos.append(i);
            foundNested = this.args.get(i).collectDeepestFunctionApplication(fs, posArg, res) || foundNested;
        }

        if (!foundNested) {
            if (fs.contains(this.f)) {
                res.put(pos, (IFunctionApplication<E>) this);
                return true;
            } else {
                return false;
            }
        } else {
            return true;
        }
    }

    @Override
    public final IFunctionApplication<D> applySubstitution(final BasicTermSubstitution sigma) {
        if (sigma instanceof ISubstitution) {
            if (((ISubstitution) sigma).isEmpty()) {
                return this;
            }
        }
        return this.processSubstitution(sigma);
    }

    @Override
    public IFunctionApplication<D> processSubstitution(final BasicTermSubstitution sigma) {
        ArrayList<ITerm<?>> newArgs = null;

        for (int i = this.args.size() - 1; i >= 0; i--) {
            final ITerm<?> arg = this.args.get(i);
            final ITerm<?> newArg = arg.applySubstitution(sigma);
            if (arg != newArg) {
                if (newArgs == null) {
                    newArgs = new ArrayList<ITerm<?>>(this.args);
                }
                newArgs.set(i, newArg);
            }
        }

        if (newArgs != null) {
            return new IFunctionApplication<D>(this.f,
                ImmutableCreator.create(newArgs));
        } else {
            return this;
        }
    }

    @Override
    public ImmutablePair<IFunctionApplication<D>, Integer> renumberVariables(final Map<IVariable<?>, IVariable<?>> map,
        final String prefix,
        Integer nr) {
        final ArrayList<ITerm<?>> newArgs = new ArrayList<ITerm<?>>(this.args.size());
        boolean changed = false;
        for (final ITerm<?> arg : this.args) {
            final ImmutablePair<? extends ITerm<?>, Integer> resArg =
                arg.renumberVariables(map, prefix, nr);
            changed = changed || resArg.x != arg;
            newArgs.add(resArg.x);
            nr = resArg.y.intValue();
        }
        final IFunctionApplication<D> res =
            changed ? new IFunctionApplication<D>(this.f,
                ImmutableCreator.create(newArgs)) : this;
            return new ImmutablePair<IFunctionApplication<D>, Integer>(res, nr);
    }

    @Override
    public IFunctionApplication<?> renameVariables(final aprove.verification.idpframework.Core.Utility.FreshVarGenerator gen) {
        return this.renameVariables(gen, new HashMap<IVariable<?>, IVariable<?>>());
    }

    @Override
    public IFunctionApplication<D> renameVariables(final aprove.verification.idpframework.Core.Utility.FreshVarGenerator gen,
        final Map<IVariable<?>, IVariable<?>> renamedVars) {
        final ArrayList<ITerm<?>> newArgs = new ArrayList<ITerm<?>>(this.args.size());
        for (final ITerm<?> arg : this.args) {
            newArgs.add(arg.renameVariables(gen, renamedVars));
        }
        final IFunctionApplication<D> res =
            new IFunctionApplication<D>(this.f, ImmutableCreator.create(newArgs));
        return res;
    }

    @Override
    protected boolean testForLessVariables(final Map<IVariable<?>, Integer> map) {
        for (final ITerm<?> arg : this.args) {
            if (!arg.testForLessVariables(map)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public void computeVariableCount(final Map<IVariable<?>, Integer> map) {
        for (final ITerm<?> arg : this.args) {
            arg.computeVariableCount(map);
        }
    }

    @Override
    public Map<IVariable<?>, ITerm<?>> extendMatchingSubstitution(Map<IVariable<?>, ITerm<?>> sigma,
        final ITerm<?> that, final boolean weakUnknownDomain) {
        if (that instanceof IVariable<?>) {
            return null;
        }
        final IFunctionApplication<?> fThat = (IFunctionApplication<?>) that;
        if (this.f.equals(fThat.f)) {
            final int n = this.f.getArity();
            for (int i = 0; i < n; i++) {
                sigma =
                    this.args.get(i).extendMatchingSubstitution(sigma,
                        fThat.args.get(i),
                        weakUnknownDomain);
                if (sigma == null) {
                    return null;
                }
            }
            return sigma;
        } else {
            return null;
        }
    }

    @Override
    public boolean linearMatches(final ITerm<?> that) {
        if (that instanceof IVariable<?>) {
            return false;
        }
        final IFunctionApplication<?> fThat = (IFunctionApplication<?>) that;
        if (this.f.equals(fThat.f)) {
            final int n = this.f.getArity();
            for (int i = 0; i < n; i++) {
                if (!this.args.get(i).linearMatches(fThat.args.get(i))) {
                    return false;
                }
            }
            return true;
        } else {
            return false;
        }
    }

    @Override
    protected boolean isLinear(final Set<IVariable<?>> alreadyPresent) {
        for (final ITerm<?> arg : this.args) {
            if (!arg.isLinear(alreadyPresent)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public void collectSubTerms(final Set<ITerm<?>> subs, final boolean dropVars) {
        if (subs.add(this)) {
            for (final ITerm<?> arg : this.args) {
                arg.collectSubTerms(subs, dropVars);
            }
        } else {
            // nothing todo
        }
    }

    @Override
    public IFunctionApplication<?> replaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        return this.uncheckedreplaceAllFunctionSymbols(replaceMap);
    }

    @Override
    public final IFunctionApplication<?> uncheckedreplaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        final IFunctionApplication<?> fThis = this;
        final ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>> replacement = replaceMap.get(fThis.getRootSymbol());

        IFunctionSymbol<?> newRootSymbol;

        boolean changed;
        if (replacement == null) {
            newRootSymbol = fThis.getRootSymbol();
            changed = false;
        } else {
            newRootSymbol = replacement.x;
            changed = true;
        }

        final ImmutableArrayList<? extends ITerm<?>> args = fThis.getArguments();
        final ArrayList<ITerm<?>> newArgs = new ArrayList<ITerm<?>>(args.size());

        for (int i = 0; i < args.size(); i++) {
            if (replacement == null || replacement.y.get(i)) {
                final ITerm<?> arg = args.get(i);
                final ITerm<?> newArg =
                    arg.uncheckedreplaceAllFunctionSymbols(replaceMap);
                if (newArg != arg) {
                    changed = true;
                }
                newArgs.add(newArg);
            }
        }

        if (changed) {
            return IFunctionApplication.create(newRootSymbol,
                ImmutableCreator.create(newArgs));
        } else {
            return this;
        }
    }

    @Override
    public String getBooleanPolyVarName() {
        return "fApp";
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        // special case for pre-defined FS in infix notation, e.g., +, -, *, /

        if (this.f.getArity() == 2) {
            final PredefinedFunction<?, ?> func =
                PredefinedUtil.getPredefinedFunction(this.f);
            if (func != null
                    && func.getFunc().getName().equals(this.f.getName())) {
                sb.append(this.args.get(0).export(eu));
                sb.append(" ");
                sb.append(this.f.export(eu));
                sb.append(" ");
                sb.append(this.args.get(1).export(eu));
                return;
            }
        }

        sb.append(this.f.export(eu));
        final Iterator<? extends ITerm<?>> i = this.args.iterator();
        if (i.hasNext()) {
            sb.append("(");
            sb.append(i.next().export(eu));
            while (i.hasNext()) {
                sb.append(", ");
                sb.append(i.next().export(eu));
            }
            sb.append(")");
        }
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        return null;
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        final XmlContentsMap contents = new XmlContentsMap();
        contents.add(this.f);
        final Iterator<? extends ITerm<?>> i = this.args.iterator();
        while (i.hasNext()) {
            contents.add("argument", i.next());
        }
        return contents;
    }

    @Override
    public boolean isVariable() {
        return false;
    }

    @Override
    public int getDepth() {
        int currentMaximum = 0;
        for (final ITerm<?> arg : this.args) {
            final int currentDepth = arg.getDepth() + 1;
            if (currentDepth > currentMaximum) {
                currentMaximum = currentDepth;
            }
        }
        return currentMaximum;
    }

    @Override
    public int getDepthConstant() {
        int currentMaximum = 0;
        for (final ITerm<?> arg : this.args) {
            final int currentDepth = arg.getDepthConstant();
            if (currentDepth > currentMaximum) {
                currentMaximum = currentDepth;
            }
        }
        return currentMaximum + 1;
    }

    @Override
    public int getSize() {
        int size = 1;
        for (final ITerm<?> arg : this.args) {
            size += arg.getSize();
        }
        return size;
    }

    public String getName() {
        return this.f.getName();
    }

    @Override
    public SemiRingDomain<D> getDomain() {
        return this.f.getResultDomain();
    }

    @Override
    public boolean isConstant() {
        return this.f.getArity() == 0;
    }

    /**
     * self-speaking method;
     * @author Martin Pluecker, copied from Sebastian Weise
     */
    @Override
    public boolean isGroundTerm() {
        for (final ITerm<?> actSubTerm : this.args) {
            if (!actSubTerm.isGroundTerm()) {
                return false;
            }
        }
        return true;
    }

    /**
     * help-method for the method "linearize(IVariable<?>)" in the super-class
     * "ITerm<?>"
     * @author Martin Pluecker, copied from Sebastian Weise
     */
    @Override
    protected ITerm<D> helpLinearize(final IVariable<?> variable,
        final Set<IVariable<?>> toAvoid) {
        final ArrayList<ITerm<?>> newArgs = new ArrayList<ITerm<?>>(0);
        for (final ITerm<?> actArg : this.getArguments()) {
            newArgs.add(actArg.helpLinearize(variable, toAvoid));
        }
        return IFunctionApplication.create(this.getRootSymbol(),
            ImmutableCreator.create(newArgs));
    }


}
