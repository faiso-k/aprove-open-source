package aprove.verification.dpframework.Orders.SizeChangeNP;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * Tagged level mappings for SCNP in the spirit of
 * the TACAS'08 paper by Ben-Amram and Codish. See the
 * LPAR-17 paper by Codish, Fuhs, Giesl, Schneider-Kamp
 * for further details.
 *
 * @author Carsten Fuhs
 */
public class LevelMapping implements Exportable, XMLObligationExportable {

    // Which arguments do we consider? Note that if rootArg is set,
    // the "first" argument actually is the root. In that case, the stored
    // function symbol in the Afs has an arity that is 1 greater than the
    // true arity of the used function symbol. (hack conducted because Afs
    // does not do the root as an "argument")
    private final Afs afsWithRootArg;

    // Which arguments do we consider? In this attribute we blissfully
    // ignore the question of the root argument and only look at proper
    // arguments, as one would most probably expect.
    private final Afs afsForOriginalFunctionSymbols;

    // Maps a function symbol to a pair of the tags of the argument tags
    // and of the root tag (which is used after everything else is said
    // and done by the order). Note that here the function symbol is always
    // used with its true arity (as in this.afsForOriginalFunctionSymbols).
    // Note also that if rootArg is set, then the first entry of the int[]
    // stands for the epsilon argument (as in this.afsWithRootArg).
    private final Map<FunctionSymbol, Pair<int[],Integer>> tags;

    // Is the root symbol also an "argument"? That is, are we considering
    // extended size-change graphs (as in Thiemann, Giesl, AAECC'05)?
    private final boolean rootArg;

    /**
     * @param rootArg -- states whether we are working with extended
     *  size-change graphs, where also the whole term gives rise to a node.
     */
    public LevelMapping(final boolean rootArg){
        this.rootArg = rootArg;
        this.tags = new LinkedHashMap<FunctionSymbol, Pair<int[],Integer>>();
        this.afsWithRootArg = new Afs();
        this.afsForOriginalFunctionSymbols = new Afs();
    }

    /**
     * @param f -- a function symbol of arity N
     * @param args -- If this.getRootArg(), then args is assumed to contain
     *  the information which of [argRoot, arg0, ..., argN-1] are regarded
     *  Otherwise the information for [arg0, ..., argN-1] is expected.
     */
    public void putRegarded(final FunctionSymbol f, final boolean[] args) {
        int arity = f.getArity();
        FunctionSymbol fPossiblyWithRootArg = f;
        boolean[] properArgs = args;
        if (this.rootArg) {
            arity++;
            fPossiblyWithRootArg = FunctionSymbol.create(f.getName(), arity);

            // args[0] stands for the root argument
            properArgs = Arrays.copyOfRange(args, 1, args.length);
        }
        if (Globals.useAssertions) {
            assert arity == args.length;
        }
        this.afsWithRootArg.setFiltering(fPossiblyWithRootArg, args);
        this.afsForOriginalFunctionSymbols.setFiltering(f, properArgs);
    }

    /**
     * @param f -- a function symbol of arity N
     * @param tags -- an array with the tags for the arguments
     *  of f (possibly including the epsilon argument if we are
     *  working with extended size-change graphs, i.e., if this.getRootArg())
     * @param rootTag -- the tag for the root of a term headed by f
     */
    public void putTags(final FunctionSymbol f, final int[] tags, final int rootTag) {
        if (Globals.useAssertions) {
            assert f.getArity() == tags.length - (this.rootArg ? 1 : 0);
        }
        this.tags.put(f, new Pair<int[],Integer>(tags,rootTag));
    }

    /**
     * @param f -- a function symbol of arity N
     * @return If this.getRootArg(), then the result contains the
     *  information which of [argRoot, arg0, ..., argN-1] are regarded
     *  Otherwise the information for [arg0, ..., argN-1] is returned.
     */
    public boolean[] getRegarded(final FunctionSymbol f) {
        int arity = f.getArity();
        FunctionSymbol newF = f;
        if (this.rootArg) {
            arity++;
            newF = FunctionSymbol.create(f.getName(), arity);
        }
        return this.afsWithRootArg.getRegardedArgs(newF);
    }

    /**
     * Convenience method.
     *
     * @param f
     * @param arg
     * @return this.getRegarded(f)[arg]
     */
    public boolean getRegarded(final FunctionSymbol f, final int arg) {
        return this.getRegarded(f)[arg];
    }

    /**
     * @param f
     * @return an array with the tags for the arguments of f (possibly
     *  including the epsilon argument if we are working with extended
     *  size-change graphs, i.e., if this.getRootArg())
     */
    public int[] getArgTags(final FunctionSymbol f) {
        return this.tags.get(f).x;
    }

    /**
     * Convenience method.
     *
     * @param f
     * @param arg
     * @return this.getArgTags(f)[arg]
     */
    public int getArgTag(final FunctionSymbol f, final int arg) {
        return this.getArgTags(f)[arg];
    }

    /**
     * @param f
     * @return the tag for the root of a term headed by f
     */
    public int getRootTag(final FunctionSymbol f) {
        return this.tags.get(f).y;
    }

    /**
     * @param f
     * @return if this LevelMapping knows f (via AFS or via tags)
     */
    public boolean knows(final FunctionSymbol f) {
        return this.afsForOriginalFunctionSymbols.hasFilter(f) || this.tags.containsKey(f);
    }

    @Override
    public String export(final Export_Util o) {
        // TODO make prettier
        final StringBuilder s = new StringBuilder();
        if (this.rootArg) {
            s.append("Here we use extended size-change graphs. In the following, the");
            s.append(o.linebreak());
            s.append("first element of the lists of arguments for regarded positions");
            s.append(o.linebreak());
            s.append("and tags thus deals with the argument at position epsilon.");
            s.append(o.linebreak());
            s.append(o.cond_linebreak());
        }
        s.append("Top level AFS:");
        s.append(o.linebreak());
        s.append(this.afsWithRootArg.export(o, 0));
        s.append(o.linebreak());
        s.append("Tags:");
        s.append(o.linebreak());
        for (final Map.Entry<FunctionSymbol, Pair<int[],Integer>> e : this.tags.entrySet()) {
            s.append(e.getKey().export(o));
            s.append(" has argument tags [");
            boolean first = true;
            for (final int t : e.getValue().x) {
                if (!first) {
                    s.append(',');
                }
                else {
                    first = false;
                }
                s.append(t);
            }
            s.append("] and root tag ");
            s.append(e.getValue().y);
            s.append(o.linebreak());
        }
        return s.toString();
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element mapping = XMLTag.LEVEL_MAPPING.createElement(doc);
        for (final Map.Entry<FunctionSymbol, Pair<int[], Integer>> fSymAndTags : this.tags.entrySet()) {
            final Element entry = XMLTag.LEVEL_MAPPING_ENTRY.createElement(doc);
            final FunctionSymbol fSym = fSymAndTags.getKey();
            entry.appendChild(fSym.toDOM(doc, xmlMetaData));
            final FunctionSymbol fSymForAfs =
                this.rootArg
                    ? FunctionSymbol.create(fSym.getName(), fSym.getArity()+1)
                    : fSym;
            final boolean[] regardedArgs = this.afsWithRootArg.getRegardedArgs(fSymForAfs);
            final int[] levels = fSymAndTags.getValue().x;
            for (int i = 0; i < regardedArgs.length; i++) {
                // Proper argument positions start at 1 for the XML export
                // and go up to the arity of the actual function symbol.
                // If the root symbol is an argument, it has "position" 0.
                final boolean regarded = regardedArgs[i];
                if (regarded) {
                    final Element posLevEntry = XMLTag.POSITION_LEVEL_ENTRY
                            .createElement(doc);
                    final Element position = XMLTag.POSITION.createElement(doc);
                    final int positionIndex = this.rootArg ? i : i + 1;
                    XMLAttribute.VALUE.setAttribute(position, positionIndex + "");
                    posLevEntry.appendChild(position);
                    final Element level = XMLTag.LEVEL.createElement(doc);
                    XMLAttribute.VALUE.setAttribute(level, levels[i] + "");
                    posLevEntry.appendChild(level);
                    entry.appendChild(posLevEntry);
                }
            }
            mapping.appendChild(entry);
        }
        return mapping;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    /**
     * @return if we consider the root position of a term also as an
     *  "argument position", i.e., as a node in the size-change graphs;
     *  in other words, the result of this method is <code>true</code>
     *  iff we consider extended size-change graphs
     */
    public boolean getRootArg() {
        return this.rootArg;
    }

    /**
     * @return the afsForOriginalFunctionSymbols -- do not modify!
     */
    public Afs getAfsForOriginalFunctionSymbols() {
        return this.afsForOriginalFunctionSymbols;
    }
}
