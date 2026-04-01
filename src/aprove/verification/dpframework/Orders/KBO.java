package aprove.verification.dpframework.Orders ;

import java.math.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * Implementation of the Knuth-Bendix Order.
 *  @author  R. Thiemann
 *  @version 2006/03/29
 */

public class KBO implements CPFExportableAfsOrder {

    private final Poset<FunctionSymbol> precedence;
    private final Map<FunctionSymbol, BigInteger> weightMap;
    private final FunctionSymbol leastConstantOfMinimalWeight;
    private final FunctionSymbol greatestTermOfMinimalWeight;
    private final boolean uniqueMinimalTerm;
    private final BigInteger weightOfMinimalTerm; // 1 is chosen, if the weight map provides no constant.

    /**
     *  Creates a KBO for a given precedence and weightMap.
     *  One can only compare terms where for every function symbol the weight is defined.
     */
    public KBO(final Poset<FunctionSymbol> precedence, final Map<FunctionSymbol, BigInteger> weight) {
        // we figure out all the details of the state for KBO-solving,
        // i.e. U, G, L, ...
        this.precedence = precedence;
        this.weightMap = weight;
        BigInteger minimalWeight = null;
        final Set<FunctionSymbol> smallestWeights = new HashSet<FunctionSymbol>();
        FunctionSymbol gotUnaryZeroWeight = null;
        for (final Map.Entry<FunctionSymbol, BigInteger> entry : this.weightMap.entrySet()) {
            final FunctionSymbol f = entry.getKey();
            final int n = f.getArity();
            if (n == 0) {
                final BigInteger w = entry.getValue();
                if (minimalWeight == null) {
                    minimalWeight = w;
                    smallestWeights.add(f);
                } else {
                    final int comp = minimalWeight.compareTo(w);
                    if (comp == 0) {
                        smallestWeights.add(f);
                    } else if (comp > 0) {
                        smallestWeights.clear();
                        smallestWeights.add(f);
                        minimalWeight = w;
                    }
                }
            } else if (n == 1) {
                if (this.weightMap.get(entry.getKey()).equals(BigInteger.ZERO)) {
                    if (Globals.useAssertions) {
                        assert(gotUnaryZeroWeight == null);
                    }
                    gotUnaryZeroWeight = f;
                }
            }
        }

        this.weightOfMinimalTerm = minimalWeight == null ? BigInteger.ONE : minimalWeight;

        if (gotUnaryZeroWeight != null) {
            this.uniqueMinimalTerm = false;
            this.greatestTermOfMinimalWeight = null;
            if (Globals.useAssertions) {
                for (final FunctionSymbol f : this.weightMap.keySet()) {
                    assert(gotUnaryZeroWeight.equals(f) || this.precedence.isGreater(gotUnaryZeroWeight, f));
                }
            }
        } else {
            this.uniqueMinimalTerm = smallestWeights.size() == 1;
            final Iterator<FunctionSymbol> i = smallestWeights.iterator();
            FunctionSymbol max = i.next();
            while (i.hasNext()) {
                final FunctionSymbol other = i.next();
                if (max == null || this.precedence.isGreater(other, max)) {
                    max = other;
                }
            }
            this.greatestTermOfMinimalWeight = max;
        }

        final Iterator<FunctionSymbol> i = smallestWeights.iterator();
        FunctionSymbol min = i.next();
        while (i.hasNext()) {
            final FunctionSymbol other = i.next();
            if (min == null || this.precedence.isGreater(min, other)) {
                min = other;
            }
        }
        this.leastConstantOfMinimalWeight = min;
    }

    /**
     * checks whether this KBO solves the given constraint. Is limited to EQ, GE, and GR,
     * where GE is implemented as GR or EQ
     * @param c
     * @return
     */
    @Override
    public boolean solves(final Constraint<TRSTerm> c) {
        final OrderRelation rel = c.z;
        if (rel == OrderRelation.GE) {
            return this.inRelation(c.x, c.y, false);
        }
        if (rel == OrderRelation.GR) {
            return this.inRelation(c.x, c.y, true);
        }
        if (rel == OrderRelation.EQ) {
            return c.x.equals(c.y);
        }
        throw new RuntimeException("Relation "+rel+" not supported by KBO");
    }

    /**
     * checks s =_KBO t, i.e. s = t
     * @param s
     * @param t
     */
    @Override
    public boolean areEquivalent(final TRSTerm s, final TRSTerm t) {
        return s.equals(t);
    }


    /**
     * Checks, whether s>t holds with this Knuth-Bendix order or not.
     * @return TRUE, if s>t holds with this KBO, FALSE otherwise
     */
    @Override
    public boolean inRelation(final TRSTerm s, final TRSTerm t) {

        return this.inRelation(s, t, true);
    }

    /**
     * Checks, whether s >(=) t holds with this Knuth-Bendix order or not.
     * @param strict s > t or s >= t.
     * @return TRUE, if s >(=) t holds with this KBO, FALSE otherwise
     */
    public boolean inRelation(final TRSTerm s, final TRSTerm t, final boolean strict) {
        final ArrayStack<Pair<InfoTerm, InfoTerm>> tupleInequality = new ArrayStack<Pair<InfoTerm, InfoTerm>>(); // the set of constraints
        tupleInequality.push(new Pair<InfoTerm, InfoTerm>(new InfoTerm(s), new InfoTerm(t)));

        final Set<TRSVariable> M = new HashSet<TRSVariable>(); // the set of variables with minimal weighted terms

        while (true) {
            // preprocess
            KBO.removeFirstEquals(tupleInequality);
            if (tupleInequality.isEmpty()) {
                return !strict;
            }
            // end preprocess

            final Pair<InfoTerm, InfoTerm> tt = tupleInequality.pop();
            final InfoTerm ileft = tt.x;
            final InfoTerm iright = tt.y;

            final TRSTerm left = ileft.term;
            final TRSTerm right = iright.term;

            // M3
            if (ileft.weight.compareTo(iright.weight) < 0) {
                return false;
            }


            // M1
            // add all variables with n(x,s) > n(x,t) to M
            final MultiSet<TRSVariable> leftVars = ileft.vars;
            final MultiSet<TRSVariable> rightVars = iright.vars;
            for (final Map.Entry<TRSVariable, Integer> leftVar : leftVars.entrySet()) {
                final TRSVariable v = leftVar.getKey();
                final int countLeft = leftVar.getValue();
                final int countRight = rightVars.frequency(v);
                if (countLeft > countRight) {
                    M.add(v);
                }
            }

            // M2
            // refuse if for some x not in M with n(x,s) < n(x,t)
            for (final Map.Entry<TRSVariable, Integer> rightVar : rightVars.entrySet()) {
                final TRSVariable v = rightVar.getKey();
                final int countRight = rightVar.getValue();
                final int countLeft = leftVars.frequency(v);
                if (countLeft < countRight && !M.contains(v)) {
                    return false;
                }
            }




            // check, whether weight of left side > weight of right side
            if (ileft.weight.compareTo(iright.weight) > 0) {
                return true;
            }

            // now check the special cases M4-M8 (same weights)

            // M4 and M5
            final boolean varLeft = left.isVariable();
            final boolean varRight = right.isVariable();
            if (!varRight &&  !varLeft) {
                final TRSFunctionApplication fLeft = (TRSFunctionApplication) left;
                final TRSFunctionApplication gRight = (TRSFunctionApplication) right;
                final FunctionSymbol f = fLeft.getRootSymbol();
                final FunctionSymbol g = gRight.getRootSymbol();
                if (f.equals(g)) {
                    // M5
                    KBO.insertArguments(tupleInequality, ileft, iright);
                } else {
                    // M4
                    return this.precedence.isGreater(f, g);
                }
            } else if (varLeft && varRight) {
                // M6
                if (!this.uniqueMinimalTerm) {
                    return false;
                }
            } else if (varLeft && !varRight) {
                // M7
                if (this.leastConstantOfMinimalWeight != null) {
                    final FunctionSymbol f = ((TRSFunctionApplication) right).getRootSymbol();
                    if (f.equals(this.leastConstantOfMinimalWeight)) {
                        if (strict) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                } else {
                    return false;
                }
            } else {
                // M8
                final TRSVariable v = (TRSVariable) right;
                if (Globals.useAssertions) {
                    assert(!varLeft && varRight);
                }
                if (ileft.vars.contains(v)) {
                    return true;
                }
                if (this.greatestTermOfMinimalWeight != null) {
                    final FunctionSymbol f = ((TRSFunctionApplication) left).getRootSymbol();
                    if (f.equals(this.greatestTermOfMinimalWeight)) {
                        KBO.replaceVariables(tupleInequality, v, ileft);
                    } else {
                        return false;
                    }
                } else {
                    return false;
                }
            }

            // loop again starting with preprocess

        }

    }

    /**
     * substitues v/t in all terms in the list
     * @param list
     * @param v
     * @param t
     */
    private static final void replaceVariables(final List<Pair<InfoTerm, InfoTerm>> list, final TRSVariable v, final InfoTerm t) {
        final ListIterator<Pair<InfoTerm, InfoTerm>> i = list.listIterator();
        while (i.hasNext()) {
            Pair<InfoTerm, InfoTerm> pair = i.next();
            pair = new Pair<InfoTerm, InfoTerm>(pair.x.replaceVariable(v, t), pair.y.replaceVariable(v, t));
            i.set(pair);
        }
    }

    /**
     * removes all pairs from the beginning of the list, until there
     * is no pair any more, or the first pair is different.
     * @param list
     */
    private static final <X> void removeFirstEquals(final List<Pair<X, X>> list) {
        final Iterator<Pair<X, X>> i = list.iterator();
        while (i.hasNext()) {
            final Pair<X, X> pair = i.next();
            if (pair.x.equals(pair.y)) {
                i.remove();
            } else {
                break;
            }
        }
    }

    /**
     * inserts (t_1,s_1),..,(t_n,s_n) in front of the list, such that (t_1,s_1) will be returned first by the iterator
     * of the list afterwards.
     * @param list
     * @param left has to be f(t_1,..,t_n)
     * @param right has to be f(s_1,..,s_n)
     */
    private static final void insertArguments(final ArrayStack<Pair<InfoTerm, InfoTerm>> list, final InfoTerm left, final InfoTerm right) {
        final List<InfoTerm> l = left.args;
        final List<InfoTerm> r = right.args;
        int i = l.size();
        list.ensureCapacity(list.size()+i);
        while (i > 0) {
            i--;
            list.push(new Pair<InfoTerm, InfoTerm>(l.get(i), r.get(i)));
        }
    }


    @Override
    public String export(final Export_Util o) {
        final StringBuilder res = new StringBuilder();
        res.append("Knuth-Bendix order "+o.cite(Citation.KBO)+" with precedence:");
        res.append(o.export(this.precedence));
        res.append(o.cond_linebreak()+"and weight map:");
        res.append(o.linebreak());
        res.append(o.set(this.weightMap.entrySet(), Export_Util.RULES));
        return res.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }


    private static final MultiSet<FunctionSymbol> EMPTY_SET = new HashMultiSet<FunctionSymbol>(0);

    /**
     * a InfoTerm stores things as weights, number of vars, ...
     * even for its subterms. Used for speedup in calculation.
     *
     * @author thiemann
     *
     */
    private class InfoTerm {


        public final TRSTerm term;
        public final MultiSet<TRSVariable> vars;
        public final MultiSet<FunctionSymbol> fs;
        public final BigInteger weight;
        public final List<InfoTerm> args;

        public InfoTerm(final TRSTerm t) {
            this.term = t;
            if (t.isVariable()) {
                this.vars = new HashMultiSet<TRSVariable>(1);
                this.vars.add((TRSVariable) t, 1);
                this.weight = KBO.this.weightOfMinimalTerm;
                this.fs = KBO.EMPTY_SET;
                this.args = null;
            } else {
                final TRSFunctionApplication ft = (TRSFunctionApplication) t;
                final FunctionSymbol f = ft.getRootSymbol();
                final int n = f.getArity();
                this.vars = new HashMultiSet<TRSVariable>(n);
                this.fs = new HashMultiSet<FunctionSymbol>(n * 2 + 1);
                this.fs.add(f, 1);
                BigInteger weight = KBO.this.weightMap.get(f);
                this.args = new ArrayList<InfoTerm>(n);
                for (final TRSTerm arg : ft.getArguments()) {
                    final InfoTerm infoArg = new InfoTerm(arg);
                    this.args.add(infoArg);
                    weight = weight.add(infoArg.weight);
                    this.vars.addAll(infoArg.vars);
                    this.fs.addAll(infoArg.fs);
                }
                this.weight = weight;
            }
        }

        private InfoTerm(final TRSFunctionApplication t, final MultiSet<TRSVariable> vars, final MultiSet<FunctionSymbol> fs, final BigInteger weight, final List<InfoTerm> args) {
            this.term = t;
            this.vars = vars;
            this.fs = fs;
            this.weight = weight;
            this.args = args;
        }

        public InfoTerm replaceVariable(final TRSVariable v, final InfoTerm t) {
            if (this.vars.contains(v)) {
                if (this.args == null) {
                    // are we a variable
                    return t;
                } else {
                    // or a functionApplication
                    final TRSFunctionApplication fterm = (TRSFunctionApplication) this.term;
                    final FunctionSymbol f = fterm.getRootSymbol();
                    final int n = f.getArity();
                    final List<InfoTerm> newInfos = new ArrayList<InfoTerm>(n);
                    final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(n);
                    BigInteger newWeight = this.weight;
                    final MultiSet<TRSVariable> newVars = new HashMultiSet<TRSVariable>(this.vars);
                    final MultiSet<FunctionSymbol> newFs = new HashMultiSet<FunctionSymbol>(this.fs);
                    for (final InfoTerm argInfo : this.args) {
                        final InfoTerm newArgInfo = argInfo.replaceVariable(v, t);
                        if (argInfo != newArgInfo) {
                            newWeight = newWeight.add(newArgInfo.weight).subtract(argInfo.weight);
                            newVars.removeAll(argInfo.vars);
                            newVars.addAll(newArgInfo.vars);
                            newFs.removeAll(argInfo.fs);
                            newFs.addAll(newArgInfo.fs);
                        }
                        newInfos.add(newArgInfo);
                        newArgs.add(newArgInfo.term);
                    }
                    final TRSFunctionApplication newTerm = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(newArgs));

                    return new InfoTerm(newTerm, newVars, newFs, newWeight, newInfos);

                }
            } else {
                return this;
            }
        }

        @Override
        public boolean equals(final Object other) {
            if (other == null) {
                return false;
            }
            final InfoTerm info = (InfoTerm) other;
            if (!this.weight.equals(info.weight)) {
                return false;
            }
            return this.term.equals(info.term);
        }

        @Override
        public int hashCode() {
            return this.term.hashCode();
        }
    }

    /**
     * exports this KBO into CPF
     * @param doc
     * @param xmlMetaData
     * @param fs the set of function symbols to be exported
     * @param afs an optional AFS that is used before the KBO.
     * @return
     */
    @Override
    public Element toCPF(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final Iterable<FunctionSymbol> fs,
        final Afs afs)
    {
        final Element entries = CPFTag.PRECEDENCE_WEIGHT.create(doc);
        final Map<FunctionSymbol, Integer> precedenceMap = this.precedence.getTopSortMap();
        BigInteger maxWeight = weightMap.values().stream().reduce(BigInteger.ZERO, (x, y) -> x.max(y));
        for (final FunctionSymbol preF : fs) {
            final FunctionSymbol f = (afs == null ? preF : afs.filter(preF));
            if (f == null) {
                continue;
            }
            BigInteger w = this.weightMap.get(f);
            if (w == null) {
                w = maxWeight.add(BigInteger.ONE);
            }
            final Element weight = CPFTag.WEIGHT.create(doc, w);
            Integer precedence = precedenceMap.get(f);
            if (precedence == null) {
                precedence = 0;
            }
            entries.appendChild(CPFTag.PRECEDENCE_WEIGHT_ENTRY.create(
                doc,
                preF.toCPF(doc, xmlMetaData), // take unfiltered symbol, as this is in xmlMetaData
                CPFTag.ARITY.create(doc, preF.getArity()), // take arity of unfiltered symbol (CPF requirement)
                CPFTag.PRECEDENCE.create(doc, precedence),
                weight));
        }
        final Element kbo =
            CPFTag.KNUTH_BENDIX_ORDER.create(
                doc,
                CPFTag.WEIGHT_ZERO.create(doc, this.weightOfMinimalTerm),
                entries);
        if (afs != null) {
            kbo.appendChild(afs.toCPF(doc, xmlMetaData));
        }
        return CPFTag.ORDERING_CONSTRAINT_PROOF.create(doc, CPFTag.RED_PAIR.create(doc, kbo));
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return this.toCPF(doc, xmlMetaData, this.weightMap.keySet(), null);
    }

    @Override
    public String isCPFSupported() {
        return null;
    }

}
