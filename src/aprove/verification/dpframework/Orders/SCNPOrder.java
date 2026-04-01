package aprove.verification.dpframework.Orders;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * The order induced by SCNP (as in the LPAR-17 paper by
 * Codish, Fuhs, Giesl, Schneider-Kamp).
 *
 * @author fuhs
 * @author nowonder
 */
public class SCNPOrder implements QActiveOrder {

    public enum Comparison {
        MAX,
        MIN,
        MS, // multiset
        DMS; // dual multiset
    }

    final static String orderName = "SCNP Order";

    private final Comparison comparison;
    private final LevelMapping levelMapping;
    private final QActiveOrder argOrder;

    // contains the data concerning the tuple symbols for the QActiveConditions
    private final Afs tupleActiveAfs;

    public SCNPOrder(final QActiveOrder argOrder, final LevelMapping levelMapping,
            final Comparison comparison) {
        this.argOrder = argOrder;
        this.levelMapping = levelMapping;
        this.comparison = comparison;
        this.tupleActiveAfs = SCNPOrder.computeTupleActiveAfs(argOrder, levelMapping);
    }

    /**
     *
     * @param argOrder
     * @param levelMapping
     * @return an Afs that regards an argument of a tuple symbol
     *  if levelMapping does or if argOrder does -- handy for active
     */
    private static Afs computeTupleActiveAfs(final QActiveOrder argOrder,
            final LevelMapping levelMapping) {
        final Afs res = new Afs(levelMapping.getAfsForOriginalFunctionSymbols());
        if (! levelMapping.getRootArg()) { // easy, no extended SCGs
            return res;
        }
        final Set<FunctionSymbol> fs = res.getFunctionSymbols();
        for (final FunctionSymbol f : fs) {
            // ask argOrder if it also regards some arguments of f
            final int n = f.getArity();
            for (int i = 0; i < n; ++i) {
                final QActiveCondition fi = QActiveCondition.TRUE.and(f, i);
                final boolean argOrderRegardsFI = argOrder.checkQActiveCondition(fi);
                if (argOrderRegardsFI) {
                    res.setFiltering(f, i, YNM.YES);
                }
            }
        }
        return res;
    }

    @Override
    public boolean checkQActiveCondition(final QActiveCondition condition) {
        final QActiveCondition specializedQAC = condition.specialize(this.tupleActiveAfs);
        final boolean result = this.argOrder.checkQActiveCondition(specializedQAC);
        return result;
    }

    @Override
    public boolean areEquivalent(final TRSTerm s, final TRSTerm t) throws AbortionException {
        final Constraint<TRSTerm> c1 = Constraint.create(s, t, OrderRelation.GE);
        final Constraint<TRSTerm> c2 = Constraint.create(t, s, OrderRelation.GE);
        return this.solves(c1) && this.solves(c2);
    }

    @Override
    public boolean inRelation(final TRSTerm s, final TRSTerm t) throws AbortionException {
        final Constraint<TRSTerm> c = Constraint.create(s, t, OrderRelation.GR);
        return this.solves(c);
    }

    @Override
    public boolean solves(final Constraint<TRSTerm> c) throws AbortionException {
        final TRSTerm l = c.x;
        final TRSTerm r = c.y;
        if (l.isVariable() || r.isVariable()) {
            if (Globals.useAssertions) {
                if (! l.isVariable()) {
                    assert !this.levelMapping.knows(((TRSFunctionApplication) l).getRootSymbol());
                }
                if (! r.isVariable()) {
                    assert !this.levelMapping.knows(((TRSFunctionApplication) r).getRootSymbol());
                }
            }
            return this.argOrder.solves(c);
        }
        final TRSFunctionApplication lFApp = (TRSFunctionApplication) l;
        final TRSFunctionApplication rFApp = (TRSFunctionApplication) r;
        final FunctionSymbol lRootSym = lFApp.getRootSymbol();
        final FunctionSymbol rRootSym = rFApp.getRootSymbol();
        if (this.levelMapping.knows(lRootSym)) {
            if (Globals.useAssertions) {
                assert this.levelMapping.knows(rRootSym);
            }
            final OrderRelation rel = c.z;
            switch (rel) {
            case EQ:    return this.areEquivalent(l, r);
            case GENGR: return this.solves(Constraint.create(l, r, OrderRelation.GE)) &&
                            ! this.inRelation(l, r);
            case NGE:   return ! this.solves(Constraint.create(l, r, OrderRelation.GE));
            case GE:    return this.compareSCNP(lFApp, rFApp, false);
            case GR:    return this.compareSCNP(lFApp, rFApp, true);
            default:    throw new UnsupportedOperationException("Unknown relation " + rel);
            }
        }
        else {
            if (Globals.useAssertions) {
                assert ! this.levelMapping.knows(rRootSym);
            }
            return this.argOrder.solves(c);
        }
    }

    /**
     *
     * @param l
     * @param r
     * @param strict - true: use ">", false: use ">=".
     * @return
     */
    private boolean compareSCNP(final TRSFunctionApplication l,
            final TRSFunctionApplication r, final boolean strict) throws AbortionException {
        // strict is ok for GE and GR
        if (this.compareByTaggedArguments(l, r, true)) {
            return true;
        }
        final int lTag = this.levelMapping.getRootTag(l.getRootSymbol());
        final int rTag = this.levelMapping.getRootTag(r.getRootSymbol());
        if (strict) {
            if (lTag <= rTag) {
                return false;
            }
        } else {
            if (lTag < rTag) {
                return false;
            }
        }
        return this.compareByTaggedArguments(l, r, false);
    }
    /**
     *
     * @param l
     * @param r
     * @param strict - true: use ">", false: use ">=".
     * @return
     */
    private boolean compareByTaggedArguments(final TRSFunctionApplication l,
            final TRSFunctionApplication r, final boolean strict) throws AbortionException {
        final FunctionSymbol lSym = l.getRootSymbol();
        final FunctionSymbol rSym = r.getRootSymbol();
        final int lArity = lSym.getArity() + (this.levelMapping.getRootArg() ? 1 : 0);
        final int rArity = rSym.getArity() + (this.levelMapping.getRootArg() ? 1 : 0);
        switch (this.comparison) {
        case MAX:
            if (strict && lArity == 0) {
                return false;
            }
            boolean[] lRegArgs = this.levelMapping.getRegarded(lSym);
            boolean[] rRegArgs = this.levelMapping.getRegarded(rSym);
            int[] lTags = this.levelMapping.getArgTags(lSym);
            int[] rTags = this.levelMapping.getArgTags(rSym);
            outer : for (int j = 0; j < rArity; ++j) {
                if (!rRegArgs[j]) {
                    continue outer;
                }
                final TRSTerm t = this.levelMapping.getRootArg() ? (j > 0 ? r.getArgument(j-1) : r) : r.getArgument(j);
                boolean tHasBiggerTermOnLHS = false;
                inner : for (int i = 0; i < lArity; ++i) {
                    if (!lRegArgs[i]) {
                        continue inner;
                    }
                    final TRSTerm s = this.levelMapping.getRootArg() ? (i > 0 ? l.getArgument(i-1) : l) : l.getArgument(i);
                    final boolean isBigger = this.compareTaggedArgs(s, t, lTags[i], rTags[j], strict);
                    if (isBigger) {
                        tHasBiggerTermOnLHS = true;
                        break inner;
                    }
                }
                if (! tHasBiggerTermOnLHS) {
                    return false;
                }
            }
            return true;
        case MIN:
            if (strict && rArity == 0) {
                return false;
            }
            lRegArgs = this.levelMapping.getRegarded(lSym);
            rRegArgs = this.levelMapping.getRegarded(rSym);
            lTags = this.levelMapping.getArgTags(lSym);
            rTags = this.levelMapping.getArgTags(rSym);
            outer : for (int i = 0; i < lArity; ++i) {
                if (!lRegArgs[i]) {
                    continue outer;
                }
                final TRSTerm s = this.levelMapping.getRootArg() ? (i > 0 ? l.getArgument(i-1) : l) : l.getArgument(i);
                boolean sHasSmallerTermOnRHS = false;
                inner : for (int j = 0; j < rArity; ++j) {
                    if (!rRegArgs[j]) {
                        continue inner;
                    }
                    final TRSTerm t = this.levelMapping.getRootArg() ? (j > 0 ? r.getArgument(j-1) : r) : r.getArgument(j);
                    final boolean isSmaller = this.compareTaggedArgs(s, t, lTags[i], rTags[j], strict);
                    if (isSmaller) {
                        sHasSmallerTermOnRHS = true;
                        break inner;
                    }
                }
                if (! sHasSmallerTermOnRHS) {
                    return false;
                }
            }
            return true;
        case MS:
            if (strict && lArity == 0) {
                return false;
            }
            lRegArgs = this.levelMapping.getRegarded(lSym);
            rRegArgs = this.levelMapping.getRegarded(rSym);
            lTags = this.levelMapping.getArgTags(lSym);
            rTags = this.levelMapping.getArgTags(rSym);
            // TODO possible optimization: remove regarded identical arguments from both sides
            List<TRSTerm> lArgs = l.getArguments();
            List<TRSTerm> rArgs = r.getArguments();
            if (this.levelMapping.getRootArg()) {
                lArgs = SCNPOrder.extendList(l, lArgs);
                rArgs = SCNPOrder.extendList(r, rArgs);
            }
            return this.checkMulti(lArgs, rArgs, 0, 0, lTags, rTags, new HashSet<Integer>(), new HashSet<Integer>(), lRegArgs, rRegArgs, !strict);
        case DMS:
            if (strict && rArity == 0) {
                return false;
            }
            lRegArgs = this.levelMapping.getRegarded(lSym);
            rRegArgs = this.levelMapping.getRegarded(rSym);
            lTags = this.levelMapping.getArgTags(lSym);
            rTags = this.levelMapping.getArgTags(rSym);
            // TODO possible optimization: remove regarded identical arguments from both sides
            lArgs = l.getArguments();
            rArgs = r.getArguments();
            if (this.levelMapping.getRootArg()) {
                lArgs = SCNPOrder.extendList(l, lArgs);
                rArgs = SCNPOrder.extendList(r, rArgs);
            }
            return this.checkDualMulti(lArgs, rArgs, 0, 0, lTags, rTags, new HashSet<Integer>(), new HashSet<Integer>(), lRegArgs, rRegArgs, !strict);
        default:
            throw new UnsupportedOperationException("Comparison via " +
                    this.comparison + " is not yet implemented!");
        }
    }

    private static <T> List<T> extendList(final T elem, final List<T> list) {
        final List<T> newList = new ArrayList<T>(list.size()+1);
        newList.add(elem);
        newList.addAll(list);
        return newList;
    }

    private boolean checkMulti(final List<TRSTerm> lArgs, final List<TRSTerm> rArgs, final int lIndex, final int rIndex, final int[] lTags, final int[] rTags, final Set<Integer> usedEquality, final Set<Integer> usedGreater, final boolean[] lRegArgs, final boolean[] rRegArgs, final boolean hasBigger) throws AbortionException {
        if (rIndex >= rArgs.size()) {
            if (hasBigger) {
                return true;
            }
            // let's try to find an argument on the lhs that is regarded and not used for equality
            for (int i = 0; i < lArgs.size(); i++) {
                if (lRegArgs[i] && !usedEquality.contains(i)) {
                    return true;
                }
            }
            // nope, no way it's bigger ... sorry, dude! gotta live with it.
            return false;
        }
        if (lIndex >= lArgs.size()) {
            return false;
        }
        final TRSTerm rArg = rArgs.get(rIndex);
        // do we need cover?
        if (!rRegArgs[rIndex]) {
            return this.checkMulti(lArgs, rArgs, lIndex, rIndex+1, lTags, rTags, usedEquality, usedGreater, lRegArgs, rRegArgs, hasBigger);
        }
        // cannot use this element of the lhs as it is filtered or has been used for equality
        if (!lRegArgs[lIndex] || usedEquality.contains(lIndex)) {
            return this.checkMulti(lArgs, rArgs, lIndex+1, rIndex, lTags, rTags, usedEquality, usedGreater, lRegArgs, rRegArgs, hasBigger);
        }
        final TRSTerm lArg = lArgs.get(lIndex);
        if (this.compareTaggedArgs(lArg, rArg, lTags[lIndex], rTags[rIndex], true)) {
            // we have a bigger element
            final Set<Integer> newUsedGreater = new HashSet<Integer>(usedGreater);
            newUsedGreater.add(lIndex);
            final boolean result = this.checkMulti(lArgs, rArgs, 0, rIndex+1, lTags, rTags, usedEquality, newUsedGreater, lRegArgs, rRegArgs, true);
            if (result) {
                return true;
            }
        }
        // cannot use this element of the lhs if it has been used for greater before
        if (usedGreater.contains(lIndex)) {
            return this.checkMulti(lArgs, rArgs, lIndex+1, rIndex, lTags, rTags, usedEquality, usedGreater, lRegArgs, rRegArgs, hasBigger);
        }
        if (this.compareTaggedArgs(lArg, rArg, lTags[lIndex], rTags[rIndex], false)) {
            // we have an equal element
            final Set<Integer> newUsedEquality = new HashSet<Integer>(usedEquality);
            newUsedEquality.add(lIndex);
            final boolean result = this.checkMulti(lArgs, rArgs, 0, rIndex+1, lTags, rTags, newUsedEquality, usedGreater, lRegArgs, rRegArgs, hasBigger);
            if (result) {
                return true;
            }
        }
        // this element of the lhs did not work out ... try the next
        return this.checkMulti(lArgs, rArgs, lIndex+1, rIndex, lTags, rTags, usedEquality, usedGreater, lRegArgs, rRegArgs, hasBigger);
    }

    private boolean checkDualMulti(final List<TRSTerm> lArgs, final List<TRSTerm> rArgs, final int lIndex, final int rIndex, final int[] lTags, final int[] rTags, final Set<Integer> usedEquality, final Set<Integer> usedLess, final boolean[] lRegArgs, final boolean[] rRegArgs, final boolean hasSmaller) throws AbortionException {
        if (lIndex >= lArgs.size()) {
            if (hasSmaller) {
                return true;
            }
            // let's try to find an argument on the rhs that is regarded and not used for equality
            for (int j = 0; j < rArgs.size(); j++) {
                if (rRegArgs[j] && !usedEquality.contains(j)) {
                    return true;
                }
            }
            // nope, it's really big ... congrats, dude! watch out you don't faint.
            return false;
        }
        if (rIndex >= rArgs.size()) {
            return false;
        }
        final TRSTerm lArg = lArgs.get(lIndex);
        // do we need cover?
        if (!lRegArgs[lIndex]) {
            return this.checkDualMulti(lArgs, rArgs, lIndex+1, rIndex, lTags, rTags, usedEquality, usedLess, lRegArgs, rRegArgs, hasSmaller);
        }
        // cannot use this element of the rhs as it is filtered or has been used for equality
        if (!rRegArgs[rIndex] || usedEquality.contains(rIndex)) {
            return this.checkDualMulti(lArgs, rArgs, lIndex, rIndex+1, lTags, rTags, usedEquality, usedLess, lRegArgs, rRegArgs, hasSmaller);
        }
        final TRSTerm rArg = rArgs.get(rIndex);
        if (this.compareTaggedArgs(lArg, rArg, lTags[lIndex], rTags[rIndex], true)) {
            // we have a smaller element
            final Set<Integer> newUsedLess = new HashSet<Integer>(usedLess);
            newUsedLess.add(rIndex);
            final boolean result = this.checkDualMulti(lArgs, rArgs, lIndex+1, 0, lTags, rTags, usedEquality, newUsedLess, lRegArgs, rRegArgs, true);
            if (result) {
                return true;
            }
        }
        // cannot use this element of the rhs if it has been used for less before
        if (usedLess.contains(rIndex)) {
            return this.checkDualMulti(lArgs, rArgs, lIndex, rIndex+1, lTags, rTags, usedEquality, usedLess, lRegArgs, rRegArgs, hasSmaller);
        }
        if (this.compareTaggedArgs(lArg, rArg, lTags[lIndex], rTags[rIndex], false)) {
            // we have an equal element
            final Set<Integer> newUsedEquality = new HashSet<Integer>(usedEquality);
            newUsedEquality.add(rIndex);
            final boolean result = this.checkDualMulti(lArgs, rArgs, lIndex+1, 0, lTags, rTags, newUsedEquality, usedLess, lRegArgs, rRegArgs, hasSmaller);
            if (result) {
                return true;
            }
        }
        // this element of the rhs did not work out ... try the next
        return this.checkDualMulti(lArgs, rArgs, lIndex, rIndex+1, lTags, rTags, usedEquality, usedLess, lRegArgs, rRegArgs, hasSmaller);
    }

    private boolean compareTaggedArgs(final TRSTerm lArg, final TRSTerm rArg, final int lTag, final int rTag,
            final boolean strict) throws AbortionException {
        final Constraint<TRSTerm> strictConstraint = Constraint.create(lArg, rArg, OrderRelation.GR);
        if (this.argOrder.solves(strictConstraint)) {
            return true;
        }
        if (strict) {
            if (lTag <= rTag) {
                return false;
            }
        }
        else {
            if (lTag < rTag) {
                return false;
            }
        }
        final Constraint<TRSTerm> weakConstraint = Constraint.create(lArg, rArg, OrderRelation.GE);
        return this.argOrder.solves(weakConstraint);
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder sb = new StringBuilder();
        sb.append("SCNP Order with the following components:");
        sb.append(o.linebreak());
        sb.append("Level mapping:");
        sb.append(o.linebreak());
        sb.append(this.levelMapping.export(o));
        sb.append(o.linebreak());
        sb.append("Comparison: ");
        sb.append(this.comparison);
        sb.append(o.linebreak());
        sb.append("Underlying order for the size change arcs and the rules of R:");
        sb.append(o.linebreak());
        sb.append(this.argOrder.export(o));
        return sb.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public Element toDOMSCNP(final Document doc, final XMLMetaData xmlMetaData) {
        final Element scnp = XMLTag.SCNP.createElement(doc);
        final Element status = XMLTag.SCNP_STATUS.createElement(doc);
        XMLAttribute.TYPE.setAttribute(status, this.comparison.name());
        scnp.appendChild(status);
        scnp.appendChild(this.levelMapping.toDOM(doc, xmlMetaData));
        return scnp;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element order = this.argOrder.toCPF(doc, xmlMetaData);
        return order;
    }

    @Override
    public String isCPFSupported() {
        String support = this.argOrder.isCPFSupported();
        return support == null ? null : "SCNP + " + support;
    }


    public void getSCNPGraphsToDOMWithP(final Document doc, final XMLMetaData xmlMetaData,
            final Set<Rule> P, final Element proof)
            throws AbortionException {
        final Map<Rule, List<Pair<Pair<Integer, Integer>, Boolean>>> dpsToGtGe = new LinkedHashMap<Rule, List<Pair<Pair<Integer, Integer>, Boolean>>>();
        for (final Rule rule : P) {
            final List<Pair<Pair<Integer, Integer>, Boolean>> gegt = new LinkedList<Pair<Pair<Integer, Integer>, Boolean>>();
            final TRSFunctionApplication lhs = rule.getLeft();
            final TRSFunctionApplication rhs;
            final TRSTerm rhsTerm = rule.getRight();
            if (rhsTerm instanceof TRSFunctionApplication) {
                rhs = (TRSFunctionApplication) rhsTerm;
            } else {
                rhs = null;
            }
            assert (rhs != null);
            Integer i = 1;
            Integer j = 1;
            final LinkedList<TRSTerm> lefts = new LinkedList<TRSTerm>();
            final LinkedList<TRSTerm> rights = new LinkedList<TRSTerm>();
            final boolean root = this.levelMapping.getRootArg();
            if (root) {
                lefts.add(lhs);
                i--;
                rights.add(rhsTerm);
                j--;
            }
            lefts.addAll(lhs.getArguments());
            rights.addAll(rhs.getArguments());

            for (final TRSTerm leftArgument : lefts) {
                j = 1;
                if (root) {
                    j--;
                }
                for (final TRSTerm rightArgument : rights) {
                    final Constraint<TRSTerm> cGE = Constraint.create(
                            leftArgument, rightArgument, OrderRelation.GE);
                    final Constraint<TRSTerm> cGT = Constraint.create(
                            leftArgument, rightArgument, OrderRelation.GR);
                    if (this.argOrder.solves(cGT)) {
                        final Pair<Integer, Integer> theEdge = new Pair<Integer, Integer>(
                                i, j);
                        final Pair<Pair<Integer, Integer>, Boolean> theEdgePlusStrictInformation = new Pair<Pair<Integer, Integer>, Boolean>(
                                theEdge, true);
                        gegt.add(theEdgePlusStrictInformation);
                    } else {
                        if (this.argOrder.solves(cGE)) {
                            final Pair<Integer, Integer> theEdge = new Pair<Integer, Integer>(
                                    i, j);
                            final Pair<Pair<Integer, Integer>, Boolean> theEdgePlusStrictInformation = new Pair<Pair<Integer, Integer>, Boolean>(
                                    theEdge, false);
                            gegt.add(theEdgePlusStrictInformation);
                        }
                    }
                    j++;
                }
                i++;
            }
            dpsToGtGe.put(rule, gegt);
        }

        for (final Rule rule : P) {
            final Element scg = XMLTag.QDP_SIZE_CHANGE_GRAPH.createElement(doc);
            scg.appendChild(rule.toDOM(doc, xmlMetaData));
            final List<Pair<Pair<Integer, Integer>, Boolean>> listOfEdgesWithStrictInformation = dpsToGtGe
                    .get(rule);
            if (listOfEdgesWithStrictInformation != null) {
                for (final Pair<Pair<Integer, Integer>, Boolean> edge : listOfEdgesWithStrictInformation) {
                    final Element e = XMLTag.EDGE.createElement(doc);
                    final Element from = XMLTag.POSITION.createElement(doc);
                    if (edge.getValue()) {
                        XMLAttribute.STRICT.setAttribute(e, "true");
                    } else {
                        XMLAttribute.STRICT.setAttribute(e, "false");
                    }
                    final Element to = XMLTag.POSITION.createElement(doc);
                    from.setAttribute("value", "" + edge.getKey().x);
                    to.setAttribute("value", "" + edge.getKey().y);
                    e.appendChild(from);
                    e.appendChild(to);
                    scg.appendChild(e);
                }
            }
            proof.appendChild(scg);
        }
    }
}
