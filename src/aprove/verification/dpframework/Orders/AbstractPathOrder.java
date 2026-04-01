package aprove.verification.dpframework.Orders;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * Abstract superclass for accessing and exporting path orders.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
abstract public class AbstractPathOrder implements CPFExportableAfsOrder {

    /**
     * The function symbol status (lex/mult) used by this path order.
     */
    protected StatusMap<FunctionSymbol> statusMap = null;
    /**
     * For caching topsortmap of the precedence.
     */
    protected Map<FunctionSymbol,Integer> precedenceAsMap;

    /**
     * Return the precedence used by this path order.
     */
    abstract public OrderedSet<FunctionSymbol> getPrecedence();
    public Map<FunctionSymbol,Integer> getPrecedenceAsMap() {
        if (this.precedenceAsMap == null) {
            this.precedenceAsMap = this.getPrecedence().getTopSortMap();
        }
        return this.precedenceAsMap;
    }

    /**
     * @return the StatusMap object encapsulated by this path order if such
     *  an object exists explicitly; otherwise a fresh path order object
     *  uniquely determined by the class of this path order
     */
    public StatusMap<FunctionSymbol> getStatusMap() {
        return this.statusMap;
    }

    @Override
    public final Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return this.toCPF(doc, xmlMetaData, this.getPrecedenceAsMap().keySet(), null);
    }

    /**
     * Tries to assign lex or mul to all symbols of arity <= 1.
     * Does this only if there are no symbols of arity > 1 where one
     * of them has mul status and another one has non-mul status.
     *
     * @param statusMap
     * @return the old map if nothing could be done; a new "simpler" status map
     *  otherwise
     */
    private static StatusMap<FunctionSymbol> simplifyStatus(
            final StatusMap<FunctionSymbol> statusMap) {
        boolean wantsLex = false;
        boolean wantsMul = false;
        final Map<FunctionSymbol, Permutation> statusAsMap = statusMap.getMapCopy();
        final Set<FunctionSymbol> signature = statusAsMap.keySet();

        // first determine want kind of adjustments to the status are possible
        // and/or needed
        for (final FunctionSymbol f : signature) {
            if (f.getArity() > 1) {
                if (statusMap.hasMultisetStatus(f)) {
                    wantsMul = true;
                } else {
                    wantsLex = true;
                }
            }
        }

        // Don't adjust if we've seen both mul and lex for symbols of arity > 1
        if (wantsMul && wantsLex) {
            return statusMap;
        }

        // We're still here, so build a flashy new status map
        final StatusMap<FunctionSymbol> res = StatusMap.create(signature);
        for (final FunctionSymbol f : signature) {
            final int n = f.getArity();
            if (n > 1) { // use the old status, whatever it was
                if (statusMap.hasMultisetStatus(f)) {
                    res.assignMultisetStatus(f);
                } else {
                    final Permutation perm = statusMap.getPermutation(f);
                    res.assignPermutation(f, perm);
                }
            } else { // simplify!
                if (wantsMul) {
                    res.assignMultisetStatus(f);
                } else {
                    final Permutation leftToRight = Permutation.createLeftToRight(n);
                    res.assignPermutation(f, leftToRight);
                }
            }
        }
        return res;
    }


    @Override
    public final Element toCPF(
            final Document doc,
            final XMLMetaData xmlMetaData,
            final Iterable<FunctionSymbol> fs,
            final Afs afs) {
        StatusMap<FunctionSymbol> statusMap = this.getStatusMap();
        statusMap = AbstractPathOrder.simplifyStatus(statusMap);

        // CPF takes the statusMap as kind of a fake or special afs
        // so that permutation is no problem here
        final Map<FunctionSymbol, Integer> precedenceMap = this.getPrecedenceAsMap();
        if (Globals.useAssertions) {
            assert statusMap != null : "Every path order should be able to tell about its status!";
        }
        final Map<FunctionSymbol, Permutation> statusAsMap = statusMap.getMapCopy();
        if (Globals.useAssertions) {
            assert precedenceMap.keySet().equals(statusAsMap.keySet()) : "Key sets differ for:\n* Status map: "
                + statusAsMap
                + "\n* Prec map: "
                + precedenceMap;
        }

        final Element statusPrecedence = CPFTag.STATUS_PRECEDENCE.create(doc);
        final Element afsTag = CPFTag.ARGUMENT_FILTER.create(doc);
        int afsEntries = 0;
        for (FunctionSymbol preF : fs) {
            final FunctionSymbol f = (afs == null ? preF : afs.filter(preF));
            final Pair<YNM[], Boolean> filtering = (afs == null ? Afs.getNoFiltering(preF.getArity()) : afs.getFiltering(preF));
            if (f == null) { // collapsing
                // only store afs entry, no status-precedence required
                afsTag.appendChild(afs.toCPFEntry(preF, filtering, doc, xmlMetaData, null));
            } else { // non-collapsing
                statusPrecedence.appendChild(CPFTag.STATUS_PRECEDENCE_ENTRY.create(doc,
                        preF.toCPF(doc, xmlMetaData),
                        CPFTag.ARITY.create(doc, preF.getArity()),
                        CPFTag.PRECEDENCE.create(doc, precedenceMap.get(f)),
                        (statusMap.hasMultisetStatus(f) ? CPFTag.MUL : CPFTag.LEX).create(doc)
                        ));

                Permutation perm = statusMap.getPermutation(f);
                if (afs != null || perm != null) {
                    afsTag.appendChild(afs.toCPFEntry(preF, filtering, doc, xmlMetaData, perm));
                    afsEntries++;
                }
            }
        }
        Element pathOrder = CPFTag.PATH_ORDER.create(doc, statusPrecedence);
        if (afsEntries > 0) {
            pathOrder.appendChild(afsTag);
        }
        return CPFTag.ORDERING_CONSTRAINT_PROOF.create(doc,
                CPFTag.RED_PAIR.create(doc, pathOrder));
    }


    @Override
    public final String isCPFSupported() {
        return null;
    }


}
