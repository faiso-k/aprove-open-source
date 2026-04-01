package aprove.verification.dpframework.TRSProblem.Utility.SRSNonLoop;

import java.util.*;

import org.w3c.dom.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;


/**
 * represent Overlap Closures, which consists of {@link Stringpattern} lhs,rhs,
 * a {@link Reason}, and bigness
 * @author Tim Enger
 */
public class OverlapClosure implements DerivationStructure, Immutable {

    private static final boolean useOC2str = false;
    private static final boolean useOC3str = false;

    private final StringPattern lhs;
    private final StringPattern rhs;
    private final int bigness;
    private final Reason reason;
    private final int hashCode;
    private final TRSType type;

    public OverlapClosure(final StringPattern lhs, final StringPattern rhs, final int bigness,
            final Reason reason, final TRSType type) {
        this.lhs = lhs;
        this.rhs = rhs;
        this.bigness = bigness;
        this.reason = reason;
        this.hashCode = this.newHashCode();
        this.type = type;
    }

    public StringPattern getLhs() {
        return this.lhs;
    }

    public StringPattern getRhs() {
        return this.rhs;
    }

    @Override
    public Reason getReason() {
        return this.reason;
    }

    @Override
    public TRSType getType() {
        return this.type;
    }

    @Override
    public String toString() {
        return this.lhs.toString() + " --> " + this.rhs.toString();
    }

    /**
     * for DEBUG only
     */
    @Override
    public String toString(final int depth) {
        final StringBuilder indent = new StringBuilder();
        for (int i = 0; i < depth; i++) {
            indent.append("\t");
        }

        final StringBuilder sb = new StringBuilder();

        sb.append(indent);
        // DEBUG
        sb.append("#" + this.getBigness() + " ");

        sb.append(this.lhs);
        sb.append(" --> ");
        sb.append(this.rhs);

        sb.append("   Reason: ");
        sb.append(this.reason);
        sb.append(" ");

        for (final DerivationStructure ds : this.reason.getParents()) {
            sb.append("\n");
            sb.append(indent);
            sb.append(ds.toString(depth + 1));
        }
        return sb.toString();
    }

    @Override
    public boolean equals(final Object oc) {
        if (this.hashCode != oc.hashCode()) {
            return false;
        }

        if (oc instanceof OverlapClosure) {
            return this.lhs.equals(((OverlapClosure) oc).getLhs())
                && this.rhs.equals(((OverlapClosure) oc).getRhs());
        }
        return false;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    public int newHashCode() {
        return this.lhs.hashCode() * 13 + this.rhs.hashCode() * 17;
    }

    @Override
    public Set<DerivationStructure> overlapsWith(final DerivationStructure ds) {
        if (ds instanceof OverlapClosure) {
            return this.overlapsWith((OverlapClosure) ds);
        } else {
            // this case is not handled
            return new LinkedHashSet<DerivationStructure>();
        }
    }

    /**
     * Definition 3.4 page 8/9
     * @param oc OverlapClosure
     * @return Set of generated OverlapClosures
     */
    public Set<DerivationStructure> overlapsWith(final OverlapClosure oc) {
        final Set<DerivationStructure> newOcs =
            new LinkedHashSet<DerivationStructure>();

        // if oc is in P, overlap must not exist
        if (oc.type.equals(TRSType.P)) {
            return newOcs;
        }

        // if type of this is in R (both ocs are in R) so result is in R
        // else result in P
        final TRSType type =
            this.type.equals(TRSType.R) ? TRSType.R : TRSType.P;

        // ******************* OC 2 *********************
        // oc1: w -> t x  and  oc2: x l -> r
        // =>  w l -> t r
        int max = this.getRhs().size();

        for (final Pair<Integer, Integer> pair : oc.getLhs().overlapBeginEnd(this.getRhs())) {
            final List<FunctionSymbol> w =
                new ArrayList<FunctionSymbol>(this.getLhs().getList());
            final List<FunctionSymbol> t =
                new ArrayList<FunctionSymbol>(this.getRhs().getSublist(0, pair.y));

            w.addAll(oc.getLhs().getSublist(pair.x, oc.getLhs().size())); // w l
            t.addAll(oc.getRhs().getList()); // t r

            newOcs.add(new OverlapClosure(new StringPattern(w),
                new StringPattern(t), this.bigness + oc.bigness, new Reason(
                    "OverlapClosure OC 2", pair, ReasonType.OC2, this, oc), type));
        }

        // ******************* OC 3 *********************
        // oc1: w -> t_1 x t_2  and  oc2: x -> r
        // =>  w -> t_1 r t_2

        max = this.getRhs().size();

        for (final Pair<Integer, Integer> pair : this.getRhs().overlapMiddle(oc.getLhs())) {
            // w -> t_1 r t_2
            final List<FunctionSymbol> t1 =
                new ArrayList<FunctionSymbol>(this.getRhs().getSublist(0, pair.x));
            final List<FunctionSymbol> t2 =
                new ArrayList<FunctionSymbol>(this.getRhs().getSublist(pair.y, max));

            t1.addAll(oc.getRhs().getList()); // t_1 r
            t1.addAll(t2);

            newOcs.add(new OverlapClosure(
                new StringPattern(this.getLhs().getList()), // w
                new StringPattern(t1), this.bigness + oc.bigness, new Reason(
"OverlapClosure OC 3", pair, ReasonType.OC3, this, oc),
                type));
        }

        // ******************* OC 2' *********************
        // oc1: w -> x t  and  oc2: l x -> r
        // => l w -> -> r t

        if (OverlapClosure.useOC2str) {
            //every possible x
            max = this.getRhs().size();
            for (int i = 1; i <= max; i++) {
                final List<FunctionSymbol> x = this.getRhs().getSublist(0, i);

                // oc needs to be as long as x
                if (x.size() > oc.getLhs().size()) {
                    break;
                } else if (x.equals(oc.getLhs().getSublist(
                    oc.getLhs().size() - i, oc.getLhs().size()))) {
                    // l w -> r t
                    final List<FunctionSymbol> w =
                        new ArrayList<FunctionSymbol>(this.getLhs().getList());
                    final List<FunctionSymbol> l =
                        new ArrayList<FunctionSymbol>(oc.getLhs().getSublist(0,
                            oc.getLhs().size() - i));
                    final List<FunctionSymbol> t =
                        new ArrayList<FunctionSymbol>(this.getRhs().getSublist(i,
                            max));
                    final List<FunctionSymbol> r =
                        new ArrayList<FunctionSymbol>(oc.getRhs().getList());

                    l.addAll(w);
                    r.addAll(t);
                    newOcs.add(new OverlapClosure(new StringPattern(l),
                        new StringPattern(r), this.bigness + oc.bigness, new Reason(
                            "OverlapClosure OC 2'", i, ReasonType.OC2prime, this, oc), type));
                }
            }
        }

        // ******************* OC 3' *********************
        // oc1: t_1 x t_2 -> r and oc2: w -> x
        // =>  t_1 w t_2 -> r
        if (OverlapClosure.useOC3str) {
            max = oc.getLhs().size();
            for (final Pair<Integer, Integer> pair : oc.getLhs().overlapMiddle(
                this.rhs)) {

                final List<FunctionSymbol> w =
                    new ArrayList<FunctionSymbol>(this.lhs.getList());
                final List<FunctionSymbol> t1 =
                    new ArrayList<FunctionSymbol>(oc.getLhs().getSublist(0,
                        pair.x));
                final List<FunctionSymbol> t2 =
                    new ArrayList<FunctionSymbol>(oc.getLhs().getSublist(
                        pair.y, max));
                final List<FunctionSymbol> r =
                    new ArrayList<FunctionSymbol>(oc.getRhs().getList());

                t1.addAll(w);
                t1.addAll(t2);

                newOcs.add(new OverlapClosure(new StringPattern(t1),
                    new StringPattern(r), this.bigness + oc.bigness, new Reason(
                        "OverlapClosure OC 3'", pair, ReasonType.OC3prime, this, oc), type));
            }
        }

        return newOcs;
    }

    /**
     * see 6.1 page 25 <br>
     * a OverlapClosure (lhs,rhs) is selfOverlapping if
     * <ul>
     * <li>am1: lhs = lc and rhs = cr -> l^x c -> c r^x</li>
     * <li>am2: lhs = cl and rhs = rc -> c l^x -> r^x c</li>
     * </ul>
     * @return generated OverlapClosures
     */
    public Set<DerivationStructure> selfOverlapping() {
        final Set<DerivationStructure> newDs =
            new LinkedHashSet<DerivationStructure>();
        StringPattern l, r, c;

        if (this.type.equals(TRSType.P)) {
            return newDs;
        }

        // lhs = lc and rhs = cr -> l^x c -> c r^x
        for (final Pair<Integer, Integer> pair : this.rhs.overlapBeginEnd(this.lhs)) {
            c = new StringPattern(this.lhs.getSublist(pair.y, this.lhs.size()));
            l = new StringPattern(this.lhs.getSublist(0, pair.y));
            r = new StringPattern(this.rhs.getSublist(pair.x, this.rhs.size()));

            if (c.size() > 0 && r.size() > 0 && l.size() > 0) {
                final WordPattern lhs =
                    new WordPattern(new StringPattern(
                        new ArrayList<FunctionSymbol>()), l, c,
                        new LinearFunction(1, 0));
                final WordPattern rhs =
                    new WordPattern(c, r, new StringPattern(
                        new ArrayList<FunctionSymbol>()), new LinearFunction(1,
                        0));
                newDs.add(new DerivationPattern(lhs, rhs, this.getBigness() + 1,
                    new Reason("Selfoverlapping OC am1", ReasonType.OC_DP_1, this), TRSType.R));
            }
        }

        // lhs = cl and rhs = rc -> c l^x -> r^x c
        for (final Pair<Integer, Integer> pair : this.lhs.overlapBeginEnd(this.rhs)) {
            c = new StringPattern(this.lhs.getSublist(0, pair.x));
            l = new StringPattern(this.lhs.getSublist(pair.x, this.lhs.size()));
            r = new StringPattern(this.rhs.getSublist(0, pair.y));

            if (c.size() > 0 && r.size() > 0 && l.size() > 0) {
                final WordPattern lhs =
                    new WordPattern(c, l, new StringPattern(
                        new ArrayList<FunctionSymbol>()), new LinearFunction(1,
                        0));
                final WordPattern rhs =
                    new WordPattern(new StringPattern(
                        new ArrayList<FunctionSymbol>()), r, c,
                        new LinearFunction(1, 0));
                newDs.add(new DerivationPattern(lhs, rhs, this.getBigness() + 1,
                    new Reason("Selfoverlapping OC am2", ReasonType.OC_DP_2, this), TRSType.R));
            }
        }
        return newDs;
    }

    @Override
    public boolean selfEmbedding() {
        return !this.rhs.overlapMiddle(this.lhs).isEmpty();
    }

    @Override
    public int getBigness() {
        return this.bigness + this.lhs.size() + this.rhs.size();
    }

    /**
     * for selfembedding ocs "m -> l m r", returns l and r.
     */
    private Pair<List<FunctionSymbol>, List<FunctionSymbol>> getLeftRight() {
        final Pair<Integer, Integer> pair = this.rhs.overlapMiddle(this.lhs).get(0);
        final List<FunctionSymbol> left = this.rhs.getSublist(0, pair.x);
        final List<FunctionSymbol> right = this.rhs.getSublist(pair.y, this.rhs.getList().size());
        return new Pair<>(left, right);
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return CPFTag.OVERLAP_CLOSURE.create(doc, this.lhs.toCPF(doc, xmlMetaData), this.rhs.toCPF(doc, xmlMetaData));
    }

    @Override
    public void toCPF(final Document doc, final XMLMetaData xmlMetaData, Element patterns, Set<DerivationStructure> exported) {
        if (exported.add(this)) {
            for (DerivationStructure ds : this.reason.getParents()) {
                ds.toCPF(doc, xmlMetaData, patterns, exported);
            }
            Element oc = this.toCPF(doc, xmlMetaData);
            Element prf = CPFTag.DERIVATION_PATTERN_PROOF.create(doc);
            switch (this.reason.type) {
            case OC1:
            {
                final Element isPair = CPFTag.IS_PAIR.createElement(doc);
                isPair.appendChild(doc.createTextNode("" + (this.type == TRSType.P)));
                prf.appendChild(CPFTag.OC1.create(doc, oc, isPair));
            }
            break;
            case OC2:
                // oc1: w -> t x  and  oc2: x l -> r
                // =>  w l -oc1-> t x l -oc2-> t r
            {
                final List<DerivationStructure> ds = this.reason.getParents();
                final OverlapClosure oc1 = (OverlapClosure) ds.get(0);
                final OverlapClosure oc2 = (OverlapClosure) ds.get(1);
                final Pair<Integer, Integer> lenXlenT = (Pair) this.reason.additionalInfo;
                final List<FunctionSymbol> xl = oc2.getLhs().getList();
                final List<FunctionSymbol> l = xl.subList(lenXlenT.x, xl.size());
                final List<FunctionSymbol> tx = oc1.getRhs().getList();
                final List<FunctionSymbol> t = tx.subList(0, lenXlenT.y);
                final List<FunctionSymbol> x = xl.subList(0, lenXlenT.x);
                prf.appendChild(CPFTag.OC2.create(doc,
                        oc,
                        oc1.toCPF(doc, xmlMetaData),
                        oc2.toCPF(doc, xmlMetaData),
                        StringPattern.stringToCPF(doc, xmlMetaData, t),
                        StringPattern.stringToCPF(doc, xmlMetaData, x),
                        StringPattern.stringToCPF(doc, xmlMetaData, l)
                        ));
            }
            break;
            case OC2prime:
                // ******************* OC 2' *********************
                // oc1: w -> x t  and  oc2: l x -> r
                // => l w -oc1-> l x t -oc2-> r t
            {
                final List<DerivationStructure> ds = this.reason.getParents();
                final OverlapClosure oc1 = (OverlapClosure) ds.get(0);
                final OverlapClosure oc2 = (OverlapClosure) ds.get(1);
                final int lenX = (Integer) this.reason.additionalInfo;
                final List<FunctionSymbol> lx = oc2.getLhs().getList();
                final List<FunctionSymbol> l = lx.subList(0, lx.size() - lenX);
                final List<FunctionSymbol> xt = oc1.getRhs().getList();
                final List<FunctionSymbol> t = xt.subList(lenX, xt.size());
                final List<FunctionSymbol> x = xt.subList(0, lenX);
                prf.appendChild(CPFTag.OC2prime.create(doc,
                        oc,
                        oc1.toCPF(doc, xmlMetaData),
                        oc2.toCPF(doc, xmlMetaData),
                        StringPattern.stringToCPF(doc, xmlMetaData, x),
                        StringPattern.stringToCPF(doc, xmlMetaData, t),
                        StringPattern.stringToCPF(doc, xmlMetaData, l)
                        ));
            }
            break;

            case OC3:
                // ******************* OC 3 *********************
                // oc1: w -> t_1 x t_2  and  oc2: x -> r
                // =>  w -oc1-> t_1 x t_2 -oc2-> t_1 r t_2
            {
                final List<DerivationStructure> ds = this.reason.getParents();
                final OverlapClosure oc1 = (OverlapClosure) ds.get(0);
                final OverlapClosure oc2 = (OverlapClosure) ds.get(1);
                final Pair<Integer, Integer> lenT1lenT1X = (Pair) this.reason.additionalInfo;
                final List<FunctionSymbol> t1xt2 = oc1.getRhs().getList();
                final List<FunctionSymbol> t1 = t1xt2.subList(0, lenT1lenT1X.x);
                final List<FunctionSymbol> t2 = t1xt2.subList(lenT1lenT1X.y, t1xt2.size());
                prf.appendChild(CPFTag.OC3.create(doc,
                        oc,
                        oc1.toCPF(doc, xmlMetaData),
                        oc2.toCPF(doc, xmlMetaData),
                        StringPattern.stringToCPF(doc, xmlMetaData, t1),
                        StringPattern.stringToCPF(doc, xmlMetaData, t2)
                        ));
            }
                break;
            case OC3prime:
                // ******************* OC 3' *********************
                // oc1: t_1 x t_2 -> r and oc2: w -> x
                // =>  t_1 w t_2 -oc2-> t_1 x t_2 -oc1-> r
            {
                final List<DerivationStructure> ds = this.reason.getParents();
                final OverlapClosure oc1 = (OverlapClosure) ds.get(0);
                final OverlapClosure oc2 = (OverlapClosure) ds.get(1);
                final Pair<Integer, Integer> lenT1lenT1X = (Pair) this.reason.additionalInfo;
                final List<FunctionSymbol> t1xt2 = oc1.getLhs().getList();
                final List<FunctionSymbol> t1 = t1xt2.subList(0, lenT1lenT1X.x);
                final List<FunctionSymbol> t2 = t1xt2.subList(lenT1lenT1X.y, t1xt2.size());
                prf.appendChild(CPFTag.OC3prime.create(doc,
                        oc,
                        oc1.toCPF(doc, xmlMetaData),
                        oc2.toCPF(doc, xmlMetaData),
                        StringPattern.stringToCPF(doc, xmlMetaData, t1),
                        StringPattern.stringToCPF(doc, xmlMetaData, t2)
                        ));
            }
                break;
            default:
                prf.appendChild(CPFTag.createError(doc));
            }
            patterns.appendChild(prf);

        }
    }

    @Override
    public Element toNontermCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Pair<List<FunctionSymbol>, List<FunctionSymbol>> lr = this.getLeftRight();
        Element m = this.lhs.toCPF(doc, xmlMetaData);
        Element patterns = CPFTag.DERIVATION_PATTERNS.create(doc);
        Set<DerivationStructure> exported = new HashSet<>();
        this.toCPF(doc, xmlMetaData, patterns, exported);
        final Element seOC = CPFTag.SELF_EMBEDDING_OC.create(doc,
                StringPattern.stringToCPF(doc, xmlMetaData, lr.x),
                m,
                StringPattern.stringToCPF(doc, xmlMetaData, lr.y)
                );
        return CPFTag.NONTERMINATING_SRS.create(doc, patterns, seOC);

    }
}