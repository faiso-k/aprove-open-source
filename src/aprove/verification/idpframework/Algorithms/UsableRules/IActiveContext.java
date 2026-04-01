package aprove.verification.idpframework.Algorithms.UsableRules;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class IActiveContext extends IDPExportable.IDPExportableSkeleton implements Immutable, IDPExportable, XmlExportable, Iterable<IActiveAtom> {

    public static IActiveContext create(final ImmutableList<IActiveAtom> context) {
        return new IActiveContext(context);
    }

    public static IActiveContext create(final IActiveAtom atom) {
        return new IActiveContext(ImmutableCreator.create(Collections.singletonList(atom)));
    }

    public static IActiveContext create(final ITerm<?> term, final IPosition pos) {
        if (pos.isEmptyPosition()) {
            return IActiveContext.EMPTY_CONTEXT;
        }

        IFunctionApplication<?> fa = (IFunctionApplication<?>) term;

        final ArrayList<IActiveAtom> context = new ArrayList<IActiveAtom>(pos.getDepth());

        final Iterator<Integer> posIterator = pos.iterator();
        while(posIterator.hasNext()) {
            final Integer index = posIterator.next();
            context.add(IActiveAtom.create(fa.getRootSymbol(), index));
            if (posIterator.hasNext()) {
                if (Globals.useAssertions) {
                    assert !fa.isVariable() : "invalid position";
                }
                fa = (IFunctionApplication<?>) fa.getArgument(index);
            }
        }

        return IActiveContext.create(ImmutableCreator.create(context));
    }

    public static final IActiveContext EMPTY_CONTEXT = new IActiveContext(ImmutableCreator.create(new ArrayList<IActiveAtom>()));

    private final ImmutableList<IActiveAtom> context;

    private IActiveContext(final ImmutableList<IActiveAtom> context) {
        this.context = context;
    }

    public ImmutableList<IActiveAtom> getContext() {
        return this.context;
    }

    public boolean isEmpty() {
        return this.context.isEmpty();
    }

    public IActiveContext add(final IActiveAtom atom) {
        final ArrayList<IActiveAtom> newList = new ArrayList<IActiveAtom>(this.context);
        newList.add(atom);
        return IActiveContext.create(ImmutableCreator.create(newList));
    }

    public IActiveContext replaceFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        final ArrayList<IActiveAtom> newContext =
            new ArrayList<IActiveAtom>(
                this.context.size());
        boolean changed = false;

        for (final IActiveAtom atom : this.context) {
            final ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>> fsReplacement = replaceMap.get(atom.fs);

            if (fsReplacement != null && !fsReplacement.x.equals(atom.fs)) {
                if (!fsReplacement.y.get(atom.pos)) {
                    return IActiveContext.EMPTY_CONTEXT;
                }

                int newPos = 0;
                for (int i = atom.pos - 1; i >= 0; i--) {
                    if (fsReplacement.y.get(i)) {
                        newPos++;
                    }
                }

                newContext.add(IActiveAtom.create(fsReplacement.x, newPos));
                changed = true;
            } else {
                newContext.add(atom);
            }
        }

        if (changed) {
            return IActiveContext.create(ImmutableCreator.create(newContext));
        } else {
            return this;
        }
    }

    @Override
    public Iterator<IActiveAtom> iterator() {
        return this.context.iterator();
    }

    @Override
    public int hashCode() {
        return this.context.hashCode();
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
        final IActiveContext other = (IActiveContext) obj;
        return this.context.equals(other.context);
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        for (final IActiveAtom atom : this.context) {
            sb.append(eu.escape("("));
            atom.export(sb, eu, verbosityLevel);
            sb.append(eu.escape(")"));
        }
    }

    @Override
    public Map<String, String> getXmlAttribs(XmlExporter xe) {
        return null;
    }

    @Override
    public XmlContentsMap getXmlContents(XmlExporter xe) {
        XmlContentsMap contents = new XmlContentsMap();
        for (final IActiveAtom atom : this.context) {
            contents.add(atom);
        }
        return contents;
    }

}
