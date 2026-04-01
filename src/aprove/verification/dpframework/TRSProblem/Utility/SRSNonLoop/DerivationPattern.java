package aprove.verification.dpframework.TRSProblem.Utility.SRSNonLoop;

import java.util.*;

import org.w3c.dom.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * represents DerivationPattern (lhs, rhs)<br>
 * with {@link WordPattern} lhs,rhs, a {@link Reason} and bigness
 */
public class DerivationPattern implements DerivationStructure, Immutable {

    private final WordPattern lhs;
    private final WordPattern rhs;
    private final int bigness;
    private final Reason reason;
    private final int hashCode;
    private final TRSType type;

    public DerivationPattern(WordPattern lhs, WordPattern rhs, int bigness,
            Reason reason, TRSType type) {
        this.lhs = lhs;
        this.rhs = rhs;
        this.bigness = bigness;
        this.reason = reason;
        this.hashCode = this.newHashCode();
        this.type = type;
    }

    /**
     * see 6.3.2
     * @return true if selfEmbedding
     */
    @Override
    public boolean selfEmbedding() {

        if (!this.lhs.getF().isFitableIn(this.rhs.getF())) {
            return false;
        }

        // m_1 = m_2
        if (!this.lhs.getM().equals(this.rhs.getM())) {
            return false;
        }

        StringPattern l_lhs = this.lhs.getL();
        StringPattern l_rhs = this.rhs.getL();

        StringPattern r_lhs = this.lhs.getR();
        StringPattern r_rhs = this.rhs.getR();

        // l_1 < l_2 and r_1 < r_2
        if (l_lhs.size() > l_rhs.size() || r_lhs.size() > r_rhs.size()) {
            return false;
        }

        // o.l = o.l u.l_1
        if (!l_lhs.equalsSub(0, l_rhs, l_rhs.size() - l_lhs.size(),
            l_lhs.size())) {
            return false;
        }

        // o.r = o.r u.r_1
        if (!r_lhs.equalsSub(0, r_rhs, 0, r_lhs.size())) {
            return false;
        }
        return true;
    }

    /**
     * it's enough to rotate rhs page 39
     * @return
     */
    public Set<DerivationStructure> rotate() {
        Set<DerivationStructure> rotations =
            new LinkedHashSet<DerivationStructure>();
        for (WordPattern wp : this.rhs.rotate()) {
            rotations.add(new DerivationPattern(this.lhs, wp, this.bigness + 1,
                new Reason("Operation rotate", ReasonType.Equivalent, this), this.type));
        }
        return rotations;
    }

    /**
     * it's enough to expand rhs page 39
     * @return
     */
    public Set<DerivationStructure> expand() {
        Set<DerivationStructure> expansions =
            new LinkedHashSet<DerivationStructure>();
        for (WordPattern wp : this.rhs.expand()) {
            expansions.add(new DerivationPattern(this.lhs, wp, this.bigness + 1,
                new Reason("Operation expand", ReasonType.Equivalent, this), this.type));
        }
        return expansions;
    }

    /**
     * lift lhs and rhs (i.e., increase constants in function by linear factor on both hand sides)
     * @return generated DerivationPattern
     */
    public Set<DerivationStructure> lift() {
        Set<DerivationStructure> lift =
            new LinkedHashSet<DerivationStructure>();
        lift.add(new DerivationPattern(this.lhs.lift(), this.rhs.lift(), this.bigness + 1,
            new Reason("Operation lift", ReasonType.Lift, this), this.type));
        return lift;
    }

    /**
     * see 7.2.3 (page 38) <br>
     * <br>
     * do the following operations (as often as possible)
     * <ul>
     * <li>scale</li>
     * <li>invers expand<, "exp-"/li>
     * <li>invers rotate, "rot-"</li>
     * </ul>
     */
    public WordPattern minimize(WordPattern wp) {

        WordPattern newWp = this.scale(wp);

        StringPattern newM = newWp.getM();
        StringPattern newL = newWp.getL();
        StringPattern newR = newWp.getR();
        LinearFunction newF = newWp.getF();

        int sizeM;
        int sizeL;
        int sizeR;

        // *invers rotate*
        boolean changed = false;
        do {
            changed = false;

            sizeM = newM.size();
            sizeL = newL.size();
            sizeR = newR.size();

            for (int i = sizeM; i > 0; i--) {
                // compare end of m with end of l with length i
                if (newM.equalsSub(sizeM - i, newL, sizeL - i, i)) {
                    // compare begin of m with begin of r with length m.size()-i
                    if (newM.equalsSub(0, newR, 0, sizeM - i)) {
                        // l end + r begin
                        List<FunctionSymbol> syms =
                            new ArrayList<FunctionSymbol>();
                        syms.addAll(newL.getSublist(sizeL - i, sizeL));
                        syms.addAll(newR.getSublist(0, sizeM - i));
                        newM = new StringPattern(syms);

                        // cut l at end
                        newL = new StringPattern(newL.getSublist(0, sizeL - i));
                        // cut r at begin
                        newR =
                            new StringPattern(newR.getSublist(sizeM - i, sizeR));

                        newF = newF.add(1);
                        changed = true;
                        break;
                    }
                }
            }
        } while (changed);

        // *invers expand*
        while (sizeL >= sizeM && newL.equalsSub(sizeL - sizeM, newM, 0, sizeM)) {
            newL = new StringPattern(newL.getSublist(0, sizeL - sizeM));
            sizeL = newL.size();
            newF = newF.add(1);
        }

        while (sizeR >= sizeM && newR.equalsSub(0, newM, 0, sizeM)) {
            newR = new StringPattern(newR.getSublist(sizeM, sizeR));
            newF = newF.add(1);
            sizeR = newR.size();
        }

        return new WordPattern(newL, newM, newR, newF);
    }

    public DerivationPattern minimize() {
        WordPattern newLhs = this.minimize(this.lhs);
        WordPattern newRhs = this.minimize(this.rhs);
        if (newLhs.equals(this.lhs) && newRhs.equals(this.rhs)) {
            return this;
        } else {
            return new DerivationPattern(newLhs, newRhs, this.bigness, new Reason("Equivalent", ReasonType.Equivalent, this), this.type);
        }
    }

    /**
     * if m is the same word multiple times, you can scale the LinearFactor<br>
     * <br>
     * e.g (0 0 0)^x+3 then after scaling its (0)^3x+9
     */
    public WordPattern scale(WordPattern wp) {

        StringPattern newM = wp.getM();
        LinearFunction newF = wp.getF();
        int sizeM = newM.size();

        // every possible greatness of a pattern
        int max = sizeM / 2 + 1;
        for (int i = 1; i < max; i++) {
            // pattern must fit
            if (sizeM % i == 0) {

                boolean pattern = true;
                for (int j = i; j < sizeM; j += i) {
                    if (!newM.equalsSub(0, newM, j, i)) {
                        // if (!x.equals(m.getSublist(j, j + i))) {
                        pattern = false;
                        break;
                    }
                }

                if (pattern) {
                    newF = newF.multiply(newM.size() / i);
                    newM = new StringPattern(newM.getSublist(0, i));
                    return new WordPattern(wp.getL(), newM, wp.getR(), newF);
                }
            }
        }
        return wp;
    }

    /**
     * two ways of overlapping
     * <ul>
     * <li>overlaps with DerivationPattern</li>
     * <li>overlaps with OverlapClosure</li>
     * </ul>
     * @param ds DerivationStructure
     * @return generated DerivationStructures
     */
    @Override
    public Set<DerivationStructure> overlapsWith(DerivationStructure ds) {
        if (ds instanceof DerivationPattern) {
            return this.overlapsWith((DerivationPattern) ds);
        }
        return this.overlapsWith((OverlapClosure) ds);
    }

    /**
     * see 6.2.2 page 27<br>
     * <br>
     * two DerivationPattern (lhs_1,rhs_1),(lhs_2,rhs_2) overlap if rhs_1 and
     * lhs_2 central overlap<br>
     * <p>
     * central overlap means: (l_1,m_1,r_1,f_1),(l_2,m_2,r_2,f_2)
     * <ul>
     * <li>m_1 = m_2</li>
     * <li>AND f_1 = f_1</li>
     * <li>AND l_1 = l l_2 OR l_2 = l l_1</li>
     * <li>AND r_1 = r_2 r OR r_2 = r_1 r</li>
     * </ul>
     * </p>
     * <p>
     * <ul>
     * <li>DerivationPattern ((l_1', m_1', r_1', f_1') := lhs_1, (l_1, m_1, r_1,
     * f_1) =: rhs_1</li>
     * <li>DerivationPattern ((l_2, m_2, r_2, f_2) =: lhs_2, (l_2', m_2', r_2',
     * f_2') =: rhs_2</li>
     * </ul>
     * </p>
     * <p>
     * with
     * <ul>
     * <li>(1.1) if l_1 = l l_2 -> l_rhs = l l_2' l_lhs = l_1'</li>
     * <li>(1.2) if l_2 = l l_1 -> l_lhs = l l_1' l_rhs = l_2'</li>
     * </ul>
     * <ul>
     * <li>(2.1) if r_1 = r_2 r -> r_rhs = r_2' r r_lhs = r_1'</li>
     * <li>(2.2) if r_2 = r_1 r -> r_lhs = r_1' r r_rhs = r_2'</li>
     * </ul>
     * </p>
     * <p>
     * Result:((l_lhs, m_1', r_lhs, f_1'), (l_rhs, m_2', r_rhs, f_2'))
     * </p>
     * @param dp {@link DerivationPattern}
     * @return new DerivationStructure if overlapping
     */
    public Set<DerivationStructure> overlapsWith(DerivationPattern dp) {

        Set<DerivationStructure> result =
            new LinkedHashSet<DerivationStructure>();

        WordPattern lhs_2 = dp.getLhs();
        WordPattern rhs_1 = this.rhs;

        StringPattern l_lhs = null;
        StringPattern l_rhs = null;
        StringPattern r_lhs;
        StringPattern r_rhs;

        // m_1 = m_2
        if (!rhs_1.getM().equals(lhs_2.getM())) {
            return result;
        }

        // f_1 = f_2
        if (!rhs_1.getF().equals(lhs_2.getF())) {
            return result;
        }

        StringPattern l_1 = rhs_1.getL();
        StringPattern l_2 = lhs_2.getL();
        int sizeL1 = l_1.size();
        int sizeL2 = l_2.size();
        List<FunctionSymbol> l = null;

        // if this in P and dp in R, 1.1 must fit
        final boolean only11 =
            this.type.equals(TRSType.P) && dp.type.equals(TRSType.R);

        // if this in R and dp in P, 1.2 must fit
        final boolean only12 =
            this.type.equals(TRSType.R) && dp.type.equals(TRSType.P);

        // result only in R, if this and dp in R
        final TRSType type =
            this.type.equals(TRSType.R) && dp.type.equals(TRSType.R)
                ? TRSType.R : TRSType.P;

        // this and dp in P, then l_1 and l_2 need to be equal
        if (this.type.equals(TRSType.P) && dp.type.equals(TRSType.P)) {
            if (!l_1.equals(l_2)) {
                return result;
            }
        }

        boolean leftOne = true;;
        // (1.1) l_1 = l l_2, if not l_2 = l l_1
        if (!only12) {
            if (l_lhs == null) {
                if (l_1.equalsSub(sizeL1 - sizeL2, l_2, 0, sizeL2)) {
                    l =
                        new ArrayList<FunctionSymbol>(l_1.getSublist(0, sizeL1
                            - sizeL2));

                    // if l_1 = l l_2 -> l_rhs = l l_2'  l_lhs = l_1'
                    List<FunctionSymbol> syms =
                        new ArrayList<FunctionSymbol>(l);
                    syms.addAll(dp.getRhs().getL().getList());

                    l_rhs = new StringPattern(syms);
                    l_lhs = this.lhs.getL();
                }
            }
        }

        // (1.2) l_2 = l l_1
        if (!only11) {
            if (l_2.equalsSub(sizeL2 - sizeL1, l_1, 0, sizeL1)) {
                l =
                    new ArrayList<FunctionSymbol>(l_2.getSublist(0, sizeL2
                        - sizeL1));

                // if l_2 = l l_1 -> l_lhs = l l_1'  l_rhs = l_2'
                List<FunctionSymbol> syms = new ArrayList<FunctionSymbol>(l);
                syms.addAll(this.lhs.getL().getList());

                l_lhs = new StringPattern(syms);
                l_rhs = dp.getRhs().getL();
                leftOne = false;
            }
        }

        // neither l_1 = l l_2 nor l_2 = l l_1
        if (l_lhs == null) {
            return result;
        }

        StringPattern r_1 = rhs_1.getR();
        StringPattern r_2 = lhs_2.getR();
        int sizeR1 = r_1.size();
        int sizeR2 = r_2.size();

        List<FunctionSymbol> r;
        boolean rightOne = false;
        // r_2 = r_1 r
        if (r_2.equalsSub(0, r_1, 0, sizeR1)) {
            r = new ArrayList<FunctionSymbol>(r_2.getSublist(sizeR1, sizeR2));

            List<FunctionSymbol> syms =
                new ArrayList<FunctionSymbol>(this.lhs.getR().getList());
            syms.addAll(r);

            r_lhs = new StringPattern(syms);
            r_rhs = dp.getRhs().getR();
        } else {
            // r_1 = r_2 r
            rightOne = true;
            if (r_1.equalsSub(0, r_2, 0, sizeR2)) {
                r =
                    new ArrayList<FunctionSymbol>(
                        r_1.getSublist(sizeR2, sizeR1));

                // if r_1 = r_2 r -> r_rhs = r_2' r  r_lhs = r_1'
                List<FunctionSymbol> syms =
                    new ArrayList<FunctionSymbol>(dp.getRhs().getR().getList());
                syms.addAll(r);

                r_rhs = new StringPattern(syms);
                r_lhs = this.lhs.getR();

                // neither r_1 = r_2 r nor r_2 = r_1 r
            } else {
                return result;
            }
        }

        WordPattern newLhs =
            new WordPattern(l_lhs, this.lhs.getM(), r_lhs, this.lhs.getF());
        WordPattern newRhs =
            new WordPattern(l_rhs, dp.getRhs().getM(), r_rhs,
                dp.getRhs().getF());

        Pair<List<FunctionSymbol>,List<FunctionSymbol>> info = new Pair<>(l,r);
        // page 38


        ReasonType rtype = leftOne ?
                (rightOne ? ReasonType.DP_DP_1_1 : ReasonType.DP_DP_1_2) :
                    (rightOne ? ReasonType.DP_DP_2_1 : ReasonType.DP_DP_2_2);
        DerivationPattern newPat = new DerivationPattern(newLhs, newRhs, this.bigness + dp.bigness
              + 1, new Reason("Overlapping Derivationstructures", info, rtype, this, dp), type);

        Set<DerivationStructure> newDs =
            new LinkedHashSet<DerivationStructure>();
        newDs.add(newPat.minimize());

        return newDs;
    }

    /**
     * see 6.2.3 page 28 / 29<br>
     * DerivationPattern o:(l_1 , m_1, r_1, f_1) -> (l_2 ,m_2 , r_2, f_2)<br>
     * OverlapClosure u -> v
     * <p>
     * <ul>
     * <li>case 1: w_1 = l_2 and w_2 = u</li>
     * <ul>
     * <li>1.1: (ol1) w_1 = l x r, w_2 = x <br>
     * -> new DP: o -> (l v r, m_2, r_2, f_2)</li>
     * <li>1.2: (ol4) w_1 = x r, w_2 = l x <br>
     * -> new DP: (l l_1 , m_1, r_1, f_1) -> (v r, m_2, r_2, f_2)</li>
     * </ul>
     * </p>
     * <p>
     * <li>case 2: w_1 = m_2 and w_2 = u</li>
     * <ul>
     * <li>2.1: (ol1) w_1 = l x r, w_2 = x <br>
     * -> new DP: o -> (l_2, l v r, r_2, f_2)</li>
     * </ul>
     * </p>
     * <p>
     * <li>case 3: w_1 = r_2 and w_2 = u</li>
     * <ul>
     * <li>3.1: (ol1) w_1 = l x r, w_2 = x <br>
     * -> new DP: o -> (l_2, m_2 , l v r, f_2)</li>
     * <li>3.2: (ol3) w_1 = l x, w_2 = x r <br>
     * -> new DP: (l_1, m_1, r_1 r, f_1) -> (l_2, m_2, l v, f_2)</li>
     * </ul>
     * </ul>
     * </p>
     * w_1 is a part of rhs of DerivationPattern<br>
     * w_2 is lhs of OverlapClosure<br>
     * @param oc Overlap Closure
     * @return the generated DerivationStructures
     */
    public Set<DerivationStructure> overlapsWith(OverlapClosure oc) {

        Set<DerivationStructure> newDs =
            new LinkedHashSet<DerivationStructure>();

        // w2 not empty
        if (oc.getLhs().size() == 0) {
            return newDs;
        }

        final StringPattern w2 = oc.getLhs();
        StringPattern w1;

        // all cases expect of 1.2
        final boolean allCases;
        // only 1.2
        final boolean case12;
        final TRSType type;

        // oc in P, this in P or R
        if (oc.getType().equals(TRSType.P)) {
            type = TRSType.P;
            allCases = false;
            case12 = true;
        } else {
            // both in R
            if (this.type.equals(TRSType.R) && oc.getType().equals(TRSType.R)) {
                case12 = true;
                allCases = true;
                type = TRSType.R;
            } else {
                // this in P, oc in
                case12 = false;
                allCases = true;
                type = TRSType.P;
            }
        }

        // 1.1: (l): (ol1)  w_1 = l x r and w_2 = x
        // w1 not empty
        if (this.rhs.getL().size() > 0) {
            if (allCases) {
                w1 = this.rhs.getL();
                for (Pair<Integer, Integer> pair : w1.overlapMiddle(w2)) {
                    List<FunctionSymbol> syms = new ArrayList<FunctionSymbol>();

                    syms.addAll(w1.getSublist(0, pair.x)); // l
                    syms.addAll(oc.getRhs().getList()); // v
                    syms.addAll(w1.getSublist(pair.y, w1.size())); // r

                    StringPattern newSP = new StringPattern(syms);

                    WordPattern newLhs = this.lhs;

                    WordPattern newRhs =
                        new WordPattern(newSP, this.rhs.getM(), this.rhs.getR(),
                            this.rhs.getF());

                    DerivationPattern newPat = new DerivationPattern(newLhs, newRhs, this.bigness
                            + oc.getBigness() + 1, new Reason(
                                    "Overlap u with l (ol1)", pair, ReasonType.DP_OC_1_1, this, oc), type);

                    newDs.add(newPat.minimize());
                }
            }

            // 1.2: (l): (ol4) w_1 = x r and  w_2 = l x
            if (case12) {
                w1 = this.rhs.getL();
                for (Pair<Integer, Integer> pair : w1.overlapBeginEnd(w2)) {
                    List<FunctionSymbol> symsl =
                        new ArrayList<FunctionSymbol>();
                    List<FunctionSymbol> symsr =
                        new ArrayList<FunctionSymbol>();

                    symsl.addAll(w2.getSublist(0, pair.y)); // l
                    symsl.addAll(this.lhs.getL().getList()); // l_1

                    symsr.addAll(oc.getRhs().getList()); // v
                    symsr.addAll(w1.getSublist(pair.x, w1.size())); // r

                    StringPattern l = new StringPattern(symsl);
                    StringPattern r = new StringPattern(symsr);

                    // if this and oc both in P, l needs to be empty
                    if (oc.getType().equals(TRSType.P)
                        && this.type.equals(TRSType.P) && !(l.size() == 0)) {
                        continue;
                    }

                    WordPattern newLhs =
                        new WordPattern(l, this.lhs.getM(), this.lhs.getR(), this.lhs.getF());

                    WordPattern newRhs =
                        new WordPattern(r, this.rhs.getM(), this.rhs.getR(), this.rhs.getF());

                    DerivationPattern newPat = new DerivationPattern(newLhs, newRhs, this.bigness
                            + oc.getBigness() + 1, new Reason(
                                    "Overlap u with l (ol4)", pair, ReasonType.DP_OC_1_2, this, oc), type);

                    // new DP: (l l_1 , m_1, r_1, f_1) -> (v r, m_2, r_2, f_2)
                    newDs.add(newPat.minimize());
                }
            }
        }

        if (allCases) {
            // 2.1: (m): (ol1) w_1 = l x r,  w_2 = x
            // w1 not empty
            if (this.rhs.getM().size() > 0) {
                if (allCases) {
                    w1 = this.rhs.getM();
                    for (Pair<Integer, Integer> pair : w1.overlapMiddle(w2)) {
                        List<FunctionSymbol> syms =
                            new ArrayList<FunctionSymbol>();

                        syms.addAll(w1.getSublist(0, pair.x)); // l
                        syms.addAll(oc.getRhs().getList()); // v
                        syms.addAll(w1.getSublist(pair.y, w1.size())); // r

                        StringPattern newSP = new StringPattern(syms);
                        if (newSP.size() > 0) {

                            WordPattern newLhs = this.lhs;

                            WordPattern newRhs =
                                new WordPattern(this.rhs.getL(), newSP, this.rhs.getR(),
                                    this.rhs.getF());

                            DerivationPattern newPat = new DerivationPattern(newLhs, newRhs,
                                    this.bigness + oc.getBigness() + 1, new Reason(
                                            "Overlap u with m (ol1)", pair, ReasonType.DP_OC_2, this, oc), type);

                            newDs.add(newPat.minimize());
                        }
                    }
                }
            }

            // 3.1: (r): (ol1) w_1 = l x r,  w_2 = x
            // w1 not empty
            if (this.rhs.getR().size() > 0) {
                w1 = this.rhs.getR();
                for (Pair<Integer, Integer> pair : w1.overlapMiddle(w2)) {
                    List<FunctionSymbol> syms = new ArrayList<FunctionSymbol>();

                    syms.addAll(w1.getSublist(0, pair.x)); // l
                    syms.addAll(oc.getRhs().getList()); // v
                    syms.addAll(w1.getSublist(pair.y, w1.size())); // r

                    StringPattern newSP = new StringPattern(syms);

                    WordPattern newLhs = this.lhs;

                    WordPattern newRhs =
                        new WordPattern(this.rhs.getL(), this.rhs.getM(), newSP,
                            this.rhs.getF());

                    DerivationPattern newPat = new DerivationPattern(newLhs, newRhs, this.bigness
                            + oc.getBigness() + 1, new Reason(
                                    "Overlap u with r (ol1)", pair, ReasonType.DP_OC_3_1, this, oc), type);

                    newDs.add(newPat.minimize());
                }

                // 3.2: (r): (ol3) w_1 = l x and  w_2 = x r
                for (Pair<Integer, Integer> pair : w2.overlapBeginEnd(w1)) {
                    List<FunctionSymbol> symsl =
                        new ArrayList<FunctionSymbol>();
                    List<FunctionSymbol> symsr =
                        new ArrayList<FunctionSymbol>();

                    symsl.addAll(this.lhs.getR().getList()); // r_1
                    symsl.addAll(w2.getSublist(pair.x, w2.size())); // r

                    symsr.addAll(w1.getSublist(0, pair.y)); // l
                    symsr.addAll(oc.getRhs().getList()); // v

                    StringPattern l = new StringPattern(symsl);
                    StringPattern r = new StringPattern(symsr);

                    WordPattern newLhs =
                        new WordPattern(this.lhs.getL(), this.lhs.getM(), l, this.lhs.getF());

                    WordPattern newRhs =
                        new WordPattern(this.rhs.getL(), this.rhs.getM(), r, this.rhs.getF());


                    DerivationPattern newPat = new DerivationPattern(newLhs, newRhs, this.bigness
                            + oc.getBigness() + 1, new Reason(
                                    "Overlap u with r (ol3)", pair, ReasonType.DP_OC_3_2, this, oc), type);
                    newDs.add(newPat.minimize());
                }
            }
        }
        return newDs;
    }

    @Override
    public TRSType getType() {
        return this.type;
    }

    public WordPattern getLhs() {
        return this.lhs;
    }

    public WordPattern getRhs() {
        return this.rhs;
    }

    @Override
    public Reason getReason() {
        return this.reason;
    }

    @Override
    public int getBigness() {
        return this.bigness + this.lhs.getL().size() + this.lhs.getM().size()
            + this.lhs.getR().size() + this.rhs.getL().size() + this.rhs.getM().size()
            + this.rhs.getR().size();
    }

    @Override
    public String toString() {
        return this.lhs.toString() + " -->" + this.rhs.toString();
    }

    /**
     * for DEBUG only
     */
    @Override
    public String toString(int depth) {
        StringBuilder indent = new StringBuilder();
        for (int i = 0; i < depth; i++) {
            indent.append("\t");
        }

        StringBuilder sb = new StringBuilder();

        sb.append(indent);

        // DEBUG
        sb.append("#" + this.getBigness() + " ");

        sb.append(this.lhs);
        sb.append(" -->");
        sb.append(this.rhs);

        sb.append("   Reason: ");
        sb.append(this.reason);
        sb.append(" ");

        for (DerivationStructure ds : this.reason.getParents()) {
            sb.append("\n");
            sb.append(indent);
            sb.append(ds.toString(depth + 1));
        }
        return sb.toString();
    }

    @Override
    public boolean equals(Object other) {
        if (this.hashCode != other.hashCode()) {
            return false;
        }

        if (other instanceof DerivationPattern) {
            DerivationPattern ds = (DerivationPattern) other;
            return this.lhs.equals(ds.getLhs()) && this.rhs.equals(ds.getRhs());
        }
        return false;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    public int newHashCode() {
        return this.rhs.hashCode() * 719 + this.lhs.hashCode() * 131;
    }

    @Override
    public Element toCPF(Document doc, XMLMetaData xmlMetaData) {
        return CPFTag.DERIVATION_PATTERN.create(doc,
                this.lhs.toCPF(doc, xmlMetaData),
                this.rhs.toCPF(doc, xmlMetaData));
    }

    @Override
    public void toCPF(final Document doc, final XMLMetaData xmlMetaData, Element patterns, Set<DerivationStructure> exported) {
        if (exported.add(this)) {
            for (DerivationStructure ds : this.reason.getParents()) {
                ds.toCPF(doc, xmlMetaData, patterns, exported);
            }
            Element dp = this.toCPF(doc, xmlMetaData);
            Element prf = CPFTag.DERIVATION_PATTERN_PROOF.create(doc);
            switch (this.reason.type) {
            case OC_DP_1:
            {
                prf.appendChild(CPFTag.OC_DP1.create(doc,
                        dp,
                        this.reason.getParents().get(0).toCPF(doc, xmlMetaData)
                        ));
            }
            break;
            case OC_DP_2:
            {
                prf.appendChild(CPFTag.OC_DP2.create(doc,
                        dp,
                        this.reason.getParents().get(0).toCPF(doc, xmlMetaData)
                        ));
            }
            break;
            case Lift:
            {
                prf.appendChild(CPFTag.LIFT.create(doc,
                        dp,
                        this.reason.getParents().get(0).toCPF(doc, xmlMetaData)
                        ));
            }
            break;
            case Equivalent:
            {
                prf.appendChild(CPFTag.EQUIVALENT.create(doc,
                        dp,
                        this.reason.getParents().get(0).toCPF(doc, xmlMetaData)
                        ));
            }
            break;
            case DP_OC_1_1:
            {
                List<DerivationStructure> parents = this.reason.getParents();
                DerivationPattern dp1 = (DerivationPattern) parents.get(0);
                OverlapClosure oc2 = (OverlapClosure) parents.get(1);
                Pair<Integer,Integer> pair = (Pair) this.reason.additionalInfo;
                StringPattern lxr = dp1.rhs.getL();
                List<FunctionSymbol> l = lxr.getSublist(0, pair.x);
                List<FunctionSymbol> r = lxr.getSublist(pair.y, lxr.size());
                prf.appendChild(CPFTag.DP_OC_1_1.create(doc,
                        dp,
                        dp1.toCPF(doc, xmlMetaData),
                        oc2.toCPF(doc, xmlMetaData),
                        StringPattern.stringToCPF(doc, xmlMetaData, l),
                        StringPattern.stringToCPF(doc, xmlMetaData, r)
                        ));

            }
            break;
            case DP_OC_1_2:
            {
                List<DerivationStructure> parents = this.reason.getParents();
                DerivationPattern dp1 = (DerivationPattern) parents.get(0);
                OverlapClosure oc2 = (OverlapClosure) parents.get(1);
                Pair<Integer,Integer> pair = (Pair) this.reason.additionalInfo;
                StringPattern xr = dp1.rhs.getL();
                List<FunctionSymbol> l = oc2.getLhs().getSublist(0, pair.y);
                List<FunctionSymbol> r = xr.getSublist(pair.x, xr.size());
                List<FunctionSymbol> x = xr.getSublist(0, pair.x);

                prf.appendChild(CPFTag.DP_OC_1_2.create(doc,
                        dp,
                        dp1.toCPF(doc, xmlMetaData),
                        oc2.toCPF(doc, xmlMetaData),
                        StringPattern.stringToCPF(doc, xmlMetaData, l),
                        StringPattern.stringToCPF(doc, xmlMetaData, r),
                        StringPattern.stringToCPF(doc, xmlMetaData, x)
                        ));

            }
            break;
            case DP_OC_2:
            {
                List<DerivationStructure> parents = this.reason.getParents();
                DerivationPattern dp1 = (DerivationPattern) parents.get(0);
                OverlapClosure oc2 = (OverlapClosure) parents.get(1);
                Pair<Integer,Integer> pair = (Pair) this.reason.additionalInfo;
                StringPattern lxr = dp1.rhs.getM();
                List<FunctionSymbol> l = lxr.getSublist(0, pair.x);
                List<FunctionSymbol> r = lxr.getSublist(pair.y, lxr.size());
                prf.appendChild(CPFTag.DP_OC_2.create(doc,
                        dp,
                        dp1.toCPF(doc, xmlMetaData),
                        oc2.toCPF(doc, xmlMetaData),
                        StringPattern.stringToCPF(doc, xmlMetaData, l),
                        StringPattern.stringToCPF(doc, xmlMetaData, r)
                        ));

            }
            break;
            case DP_OC_3_1:
            {
                List<DerivationStructure> parents = this.reason.getParents();
                DerivationPattern dp1 = (DerivationPattern) parents.get(0);
                OverlapClosure oc2 = (OverlapClosure) parents.get(1);
                Pair<Integer,Integer> pair = (Pair) this.reason.additionalInfo;
                StringPattern lxr = dp1.rhs.getR();
                List<FunctionSymbol> l = lxr.getSublist(0, pair.x);
                List<FunctionSymbol> r = lxr.getSublist(pair.y, lxr.size());
                prf.appendChild(CPFTag.DP_OC_3_1.create(doc,
                        dp,
                        dp1.toCPF(doc, xmlMetaData),
                        oc2.toCPF(doc, xmlMetaData),
                        StringPattern.stringToCPF(doc, xmlMetaData, l),
                        StringPattern.stringToCPF(doc, xmlMetaData, r)
                        ));

            }
            break;
            case DP_OC_3_2:
            {
                List<DerivationStructure> parents = this.reason.getParents();
                DerivationPattern dp1 = (DerivationPattern) parents.get(0);
                OverlapClosure oc2 = (OverlapClosure) parents.get(1);
                Pair<Integer,Integer> pair = (Pair) this.reason.additionalInfo;
                StringPattern xr = oc2.getLhs();
                StringPattern lx = dp1.getRhs().getR();
                List<FunctionSymbol> l = lx.getSublist(0, pair.y);
                List<FunctionSymbol> r = xr.getSublist(pair.x, xr.size());
                List<FunctionSymbol> x = xr.getSublist(0, pair.x);
                prf.appendChild(CPFTag.DP_OC_3_2.create(doc,
                        dp,
                        dp1.toCPF(doc, xmlMetaData),
                        oc2.toCPF(doc, xmlMetaData),
                        StringPattern.stringToCPF(doc, xmlMetaData, l),
                        StringPattern.stringToCPF(doc, xmlMetaData, r),
                        StringPattern.stringToCPF(doc, xmlMetaData, x)
                        ));

            }
            break;
            case DP_DP_1_1:
            {
                List<DerivationStructure> parents = this.reason.getParents();
                DerivationPattern dp1 = (DerivationPattern) parents.get(0);
                DerivationPattern dp2 = (DerivationPattern) parents.get(1);
                Pair<List<FunctionSymbol>,List<FunctionSymbol>> pair = (Pair) this.reason.additionalInfo;
                prf.appendChild(CPFTag.DP_DP_1_1.create(doc,
                        dp,
                        dp1.toCPF(doc, xmlMetaData),
                        dp2.toCPF(doc, xmlMetaData),
                        StringPattern.stringToCPF(doc, xmlMetaData, pair.x),
                        StringPattern.stringToCPF(doc, xmlMetaData, pair.y)
                        ));

            }
            break;
            case DP_DP_1_2:
            {
                List<DerivationStructure> parents = this.reason.getParents();
                DerivationPattern dp1 = (DerivationPattern) parents.get(0);
                DerivationPattern dp2 = (DerivationPattern) parents.get(1);
                Pair<List<FunctionSymbol>,List<FunctionSymbol>> pair = (Pair) this.reason.additionalInfo;
                prf.appendChild(CPFTag.DP_DP_1_2.create(doc,
                        dp,
                        dp1.toCPF(doc, xmlMetaData),
                        dp2.toCPF(doc, xmlMetaData),
                        StringPattern.stringToCPF(doc, xmlMetaData, pair.x),
                        StringPattern.stringToCPF(doc, xmlMetaData, pair.y)
                        ));

            }
            break;
            case DP_DP_2_1:
            {
                List<DerivationStructure> parents = this.reason.getParents();
                DerivationPattern dp1 = (DerivationPattern) parents.get(0);
                DerivationPattern dp2 = (DerivationPattern) parents.get(1);
                Pair<List<FunctionSymbol>,List<FunctionSymbol>> pair = (Pair) this.reason.additionalInfo;
                prf.appendChild(CPFTag.DP_DP_2_1.create(doc,
                        dp,
                        dp1.toCPF(doc, xmlMetaData),
                        dp2.toCPF(doc, xmlMetaData),
                        StringPattern.stringToCPF(doc, xmlMetaData, pair.x),
                        StringPattern.stringToCPF(doc, xmlMetaData, pair.y)
                        ));

            }
            break;
            case DP_DP_2_2:
            {
                List<DerivationStructure> parents = this.reason.getParents();
                DerivationPattern dp1 = (DerivationPattern) parents.get(0);
                DerivationPattern dp2 = (DerivationPattern) parents.get(1);
                Pair<List<FunctionSymbol>,List<FunctionSymbol>> pair = (Pair) this.reason.additionalInfo;
                prf.appendChild(CPFTag.DP_DP_2_2.create(doc,
                        dp,
                        dp1.toCPF(doc, xmlMetaData),
                        dp2.toCPF(doc, xmlMetaData),
                        StringPattern.stringToCPF(doc, xmlMetaData, pair.x),
                        StringPattern.stringToCPF(doc, xmlMetaData, pair.y)
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
        Element patterns = CPFTag.DERIVATION_PATTERNS.create(doc);
        Set<DerivationStructure> exported = new HashSet<>();
        this.toCPF(doc, xmlMetaData, patterns, exported);
        StringPattern ll = this.rhs.getL();
        StringPattern l = this.lhs.getL();
        List<FunctionSymbol> l1 = ll.getSublist(0, ll.size() - l.size());
        StringPattern rr = this.rhs.getR();
        StringPattern r = this.lhs.getR();
        List<FunctionSymbol> r1 = rr.getSublist(r.size(), rr.size());
        final Element seDP = CPFTag.SELF_EMBEDDING_DP.create(doc,
                this.toCPF(doc, xmlMetaData),
                StringPattern.stringToCPF(doc, xmlMetaData, l1),
                StringPattern.stringToCPF(doc, xmlMetaData, r1)
                );
        return CPFTag.NONTERMINATING_SRS.create(doc, patterns, seDP);

    }


}