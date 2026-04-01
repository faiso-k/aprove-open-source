package aprove.verification.oldframework.Algebra.MinMaxExprs;

import static aprove.verification.oldframework.Algebra.MinMaxExprs.MinMaxExpr.Op.*;
import static aprove.verification.oldframework.Utility.Collection_Util.*;
import static java.util.Collections.*;
import static java.util.stream.Collectors.*;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Class to represent expressions that may contain min, max, absolute values, division, multiplication, subtraction, and addition.
 *
 * Note: this class has a natural ordering that is inconsistent with equals.
 */
public abstract class MinMaxExpr implements Exportable, Comparable<MinMaxExpr> {

    /**
     * operations supported by MinMaxExpr
     */
    static enum Op implements aprove.prooftree.Export.Utility.Exportable {

        Min, Max, Log, Plus, Minus, UnaryMinus, Times, Div, Abs;

        @Override
        public String export(Export_Util eu) {
            switch (this) {
                case Plus:
                    return eu.escape("+");
                case Minus:
                case UnaryMinus:
                    return eu.escape("-");
                case Times:
                    return eu.multSign();
                case Div:
                    return eu.escape("/");
                default:
                    return eu.escape(this.toString().toLowerCase());
            }
        }
    }

    public static MinMaxExpr createMax(Set<MinMaxExpr> args) {
        return new FunApp(Max, args);
    }

    public static MinMaxExpr createAbs(MinMaxExpr arg) {
        return new FunApp(Abs, singleton(arg));
    }

    public static MinMaxExpr createMax(MinMaxExpr arg1, MinMaxExpr arg2) {
        Set<MinMaxExpr> args = new LinkedHashSet<>();
        args.add(arg1);
        args.add(arg2);
        return createMax(args);
    }

    public static MinMaxExpr createMin(Set<MinMaxExpr> args) {
        return new FunApp(Min, args);
    }

    public static MinMaxExpr createLog(MinMaxExpr base, MinMaxExpr arg) {
        Set<MinMaxExpr> args = new LinkedHashSet<>();
        args.add(base);
        args.add(arg);
        return new FunApp(Log, args);
    }

    public static MinMaxExpr createUnaryMinus(MinMaxExpr arg) {
        return new FunApp(UnaryMinus, singleton(arg));
    }

    public static MinMaxExpr createPlus(MinMaxExpr lhs, MinMaxExpr rhs) {
        return new InfixFunApp(Plus, lhs, rhs);
    }

    public static MinMaxExpr createTimes(MinMaxExpr lhs, MinMaxExpr rhs) {
        return new InfixFunApp(Times, lhs, rhs);
    }

    public static MinMaxExpr createDiv(MinMaxExpr lhs, MinMaxExpr rhs) {
        return new InfixFunApp(Div, lhs, rhs);
    }

    public static MinMaxExpr createMinus(MinMaxExpr lhs, MinMaxExpr rhs) {
        return new InfixFunApp(Minus, lhs, rhs);
    }

    public static MinMaxExpr createInt(BigInteger value) {
        return new Number(value);
    }

    public static MinMaxExpr createVar(String name) {
        return new Variable(name);
    }

    public static MinMaxExpr createMin(MinMaxExpr arg1, MinMaxExpr arg2) {
        Set<MinMaxExpr> args = new LinkedHashSet<>();
        args.add(arg1);
        args.add(arg2);
        return createMin(args);
    }

    /**
     * check if this is a standard polynomial (without min, max, div, or absolute values)
     */
    abstract boolean isPoly();

    List<MinMaxExpr> getFactors() {
        return singletonList(this);
    }

    /**
     * replaces each variable x with |x|
     */
    public abstract MinMaxExpr absolutize();

    public abstract MinMaxExpr substitute(Map<String, MinMaxExpr> sigma);

    /**
     * Transforms a MinMaxExpr to a set of polynomials (that are implicitly connected by "min").
     * To this end, "max" is approximated by summing its arguments, |p| is transformed to p, and x/y is approximated by x.
     * @return the resulting set of polynomials P and an integer x whose meaning is that
     *         min(P) is most likely (much) smaller/greater than the original MinMaxExpr
     *         if x is (much) smaller/greater than 0
     */
    public abstract Pair<Set<SimplePolynomial>, Integer> toPolySet();

    @Override
    public String toString() {
        return export(new PLAIN_Util());
    }

    public MinMaxExpr normalize() {
        MinMaxExpr oldoldRes;
        MinMaxExpr res = this;
        FreshNameGenerator fng = new FreshNameGenerator(FreshNameGenerator.VARIABLES);
        for (String s: getVariables()) {
            fng.lockName(s);
        }
        do {
            oldoldRes = res;
            MinMaxExpr oldRes;
            do {
                oldRes = res;
                res = res.combineMinMax();
            } while (!oldRes.equals(res));
            do {
                oldRes = res;
                res = res.pushArithmetic();
            } while (!oldRes.equals(res));
            Pair<MinMaxExpr, Map<String, MinMaxExpr>> p = res.normalizeByReplacingNonPolys(fng);
            res = p.x.substitute(p.y);
        } while (!oldoldRes.equals(res));
        return res.filterMinMaxArguments();
    }

    /**
     * Remove arguments from min / max which are greater / smaller than others.
     * E.g., min(3,5,x) becoems min(3,x).
     */
    abstract MinMaxExpr filterMinMaxArguments();

    /**
     * Combine nested min / max expressions.
     * E.g., max(x, max(y,z)) becomes max(x,y,z).
     */
    abstract MinMaxExpr combineMinMax();

    /**
     * Push addition / multiplication with constants into min / max expressions.
     * E.g., max(x,y) + 3 becomes max(x+3, y+3).
     * The intention is to be able to apply "combineMax" more often.
     * E.g., max(max(x,y) + 3, z) ~> max(max(x+3, y+3), z) ~> max(x+3, y+3, z).
     */
    abstract MinMaxExpr pushArithmetic();

    abstract Set<String> getVariables();

    /**
     * Normalize polynomial sub-expressions.
     * E.g., max(2x + 3x, y) becomes max(5x, y).
     */
    abstract MinMaxExpr normalizePolys();

    /**
     * Recursively replace non-polynomial sub-expressions with variables and normalize the resulting "polynomial skeleton".
     * The returned substitution allows to undo the replacement.
     * E.g., (3 + max(2x + 3x, y)) - 1 becomes (3 + x') - 1 and is then normalized to 2 + x'.
     * The returned substitution is [x'/max(5x, y)].
     */
    abstract Pair<MinMaxExpr, Map<String, MinMaxExpr>> normalizeByReplacingNonPolys(FreshNameGenerator fng);

    boolean needsBrackets() {
        return false;
    }

    /**
     * @see MinMaxExpr#compareTo(MinMaxExpr)
     */
    public static int compare(SimplePolynomial x, SimplePolynomial y) {
        if (x.getVariables().equals(y.getVariables())) {
            return x.compareTo(y);
        } else {
            if (x.getVariables().containsAll(y.getVariables()) && x.getDegree() > y.getDegree()) {
                return 1;
            }
            if (y.getVariables().containsAll(x.getVariables()) && y.getDegree() > x.getDegree()) {
                return -1;
            }
        }
        return 0;
    }

    /**
     * Heuristically compares two MinMaxExprs.
     * So "-1" means that "this" seems to be the nicer upper resource bound in some sense.
     * Most likely, this method does not make sense at all
     * if the expressions represent something different than an upper resource bound.
     */
    @Override
    public int compareTo(MinMaxExpr that) {
        // comparing sets of polynomials is easier than comparing MinMaxExprs directly
        Pair<Set<SimplePolynomial>, Integer> thisP = this.toPolySet();
        int thisOverApproximations = thisP.y;
        Pair<Set<SimplePolynomial>, Integer> thatP = that.toPolySet();
        int thatOverApproximations = thatP.y;
        Set<SimplePolynomial> thisSet = new LinkedHashSet<>(thisP.x);
        Set<SimplePolynomial> thatSet = new LinkedHashSet<>(thatP.x);
        // remove all common elements and just compare the rest
        Set<SimplePolynomial> intersection = intersection(thisSet, thatSet);
        thisSet.removeAll(intersection);
        thatSet.removeAll(intersection);
        if (thisSet.isEmpty() && thatSet.isEmpty()) {
            return thatOverApproximations - thisOverApproximations;
        }
        if (thisSet.stream().allMatch(x -> thatSet.stream().anyMatch(y -> compare(x, y) > 0))) {
            return 1;
        }
        if (thatSet.stream().allMatch(x -> thisSet.stream().anyMatch(y -> compare(x, y) > 0))) {
            return -1;
        }
        return 0;
    }

    private static class Number extends MinMaxExpr {

        private BigInteger value;

        public Number(BigInteger value) {
            this.value = value;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((value == null) ? 0 : value.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            Number other = (Number) obj;
            if (value == null) {
                if (other.value != null)
                    return false;
            } else if (!value.equals(other.value))
                return false;
            return true;
        }

        @Override
        public Pair<Set<SimplePolynomial>, Integer> toPolySet() {
            return new Pair<>(singleton(SimplePolynomial.create(value)), 0);
        }

        @Override
        public String export(Export_Util eu) {
            return value.toString();
        }

        @Override
        public MinMaxExpr substitute(Map<String, MinMaxExpr> sigma) {
            return this;
        }

        @Override
        public MinMaxExpr absolutize() {
            return this;
        }

        @Override
        public MinMaxExpr normalizePolys() {
            return this;
        }

        @Override
        public boolean isPoly() {
            return true;
        }

        @Override
        Pair<MinMaxExpr, Map<String, MinMaxExpr>> normalizeByReplacingNonPolys(FreshNameGenerator fng) {
            return new Pair<>(this, emptyMap());
        }

        @Override
        Set<String> getVariables() {
            return emptySet();
        }

        @Override
        MinMaxExpr combineMinMax() {
            return this;
        }

        @Override
        MinMaxExpr pushArithmetic() {
            return this;
        }

        @Override
        MinMaxExpr filterMinMaxArguments() {
            return this;
        }

    }

    private static class Variable extends MinMaxExpr {

        private String name;

        public Variable(String name) {
            this.name = name;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((name == null) ? 0 : name.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            Variable other = (Variable) obj;
            if (name == null) {
                if (other.name != null)
                    return false;
            } else if (!name.equals(other.name))
                return false;
            return true;
        }

        @Override
        public Pair<Set<SimplePolynomial>, Integer> toPolySet() {
            return new Pair<>(singleton(SimplePolynomial.create(name)), 0);
        }

        @Override
        public String export(Export_Util eu) {
            return eu.escape(name);
        }

        @Override
        public MinMaxExpr substitute(Map<String, MinMaxExpr> sigma) {
            if (sigma.containsKey(name)) {
                return sigma.get(name);
            } else {
                return this;
            }
        }

        @Override
        public MinMaxExpr absolutize() {
            return createAbs(this);
        }

        @Override
        public MinMaxExpr normalizePolys() {
            return this;
        }

        @Override
        public boolean isPoly() {
            return true;
        }

        @Override
        Pair<MinMaxExpr, Map<String, MinMaxExpr>> normalizeByReplacingNonPolys(FreshNameGenerator fng) {
            return new Pair<>(this, emptyMap());
        }

        @Override
        Set<String> getVariables() {
            return singleton(name);
        }

        @Override
        MinMaxExpr combineMinMax() {
            return this;
        }

        @Override
        MinMaxExpr pushArithmetic() {
            return this;
        }

        @Override
        MinMaxExpr filterMinMaxArguments() {
            return this;
        }

    }

    private static class InfixFunApp extends MinMaxExpr {

        Op op;
        MinMaxExpr lhs;
        MinMaxExpr rhs;

        public InfixFunApp(Op op, MinMaxExpr lhs, MinMaxExpr rhs) {
            this.op = op;
            this.lhs = lhs;
            this.rhs = rhs;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((lhs == null) ? 0 : lhs.hashCode());
            result = prime * result + ((op == null) ? 0 : op.hashCode());
            result = prime * result + ((rhs == null) ? 0 : rhs.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            InfixFunApp other = (InfixFunApp) obj;
            if (lhs == null) {
                if (other.lhs != null)
                    return false;
            } else if (!lhs.equals(other.lhs))
                return false;
            if (op != other.op)
                return false;
            if (rhs == null) {
                if (other.rhs != null)
                    return false;
            } else if (!rhs.equals(other.rhs))
                return false;
            return true;
        }

        @Override
        public Pair<Set<SimplePolynomial>, Integer> toPolySet() {
            Pair<Set<SimplePolynomial>, Integer> p1 = lhs.toPolySet();
            Set<SimplePolynomial> lhss = p1.x;
            Pair<Set<SimplePolynomial>, Integer> p2 = rhs.toPolySet();
            Set<SimplePolynomial> rhss = p2.x;
            int overApproximations = p1.y + p2.y;
            Set<SimplePolynomial> res = new LinkedHashSet<>();
            for (SimplePolynomial l : lhss) {
                for (SimplePolynomial r : rhss) {
                    switch (op) {
                        case Plus:
                            res.add(l.plus(r));
                            break;
                        case Minus:
                            res.add(l.minus(r));
                            break;
                        case Times:
                            res.add(l.times(r));
                            break;
                        case Div:
                            res.add(l);
                            overApproximations++;
                            break;
                        default:
                            throw new RuntimeException();
                    }
                }
            }
            return new Pair<>(res, overApproximations);
        }

        @Override
        List<MinMaxExpr> getFactors() {
            if (op == Times) {
                List<MinMaxExpr> res = new ArrayList<>();
                res.addAll(lhs.getFactors());
                res.addAll(rhs.getFactors());
                return res;
            } else {
                return singletonList(this);
            }
        }

        @Override
        public String export(Export_Util eu) {
            switch (op) {
                case Times:
                    List<MinMaxExpr> factors = getFactors();
                    Map<MinMaxExpr, Integer> occurrences = new DefaultValueMap<>(0);
                    for (MinMaxExpr exp: factors) {
                        occurrences.put(exp, occurrences.get(exp) + 1);
                    }
                    StringBuilder res = new StringBuilder();
                    Iterator<Entry<MinMaxExpr, Integer>> it = occurrences.entrySet().iterator();
                    while (it.hasNext()) {
                        Entry<MinMaxExpr, Integer> e = it.next();
                        MinMaxExpr exp = e.getKey();
                        Integer degree = e.getValue();
                        if (exp.needsBrackets()) {
                            res.append("(");
                        }
                        res.append(exp.export(eu));
                        if (exp.needsBrackets()) {
                            res.append(")");
                        }
                        if (degree > 1) {
                            res.append(eu.sup(Integer.toString(degree)));
                        }
                        if (it.hasNext()) {
                            res.append(eu.appSpace());
                            res.append(eu.multSign());
                            res.append(eu.appSpace());
                        }
                    }
                    return res.toString();
                case Div:
                case Minus: {
                    String lhsString;
                    String rhsString;
                    if (lhs instanceof InfixFunApp) {
                        lhsString = "(" + lhs.export(eu) + ")";
                    } else {
                        lhsString = lhs.export(eu);
                    }
                    if (rhs instanceof InfixFunApp) {
                        rhsString = "(" + rhs.export(eu) + ")";
                    } else {
                        rhsString = rhs.export(eu);
                    }
                    return lhsString + eu.appSpace() + op.export(eu) + eu.appSpace() + rhsString;
                }
                case Plus:
                    return lhs.export(eu) + eu.appSpace() + op.export(eu) + eu.appSpace() + rhs.export(eu);
                default:
                    throw new RuntimeException();
            }
        }

        @Override
        public MinMaxExpr substitute(Map<String, MinMaxExpr> sigma) {
            return new InfixFunApp(op, lhs.substitute(sigma), rhs.substitute(sigma));
        }

        @Override
        public MinMaxExpr absolutize() {
            return new InfixFunApp(op, lhs.absolutize(), rhs.absolutize());
        }

        @Override
        public MinMaxExpr normalizePolys() {
            if (isPoly()) {
                Set<SimplePolynomial> polys = this.toPolySet().x;
                assert polys.size() == 1;
                return polys.iterator().next().toMinMaxExpr();
            } else {
                return new InfixFunApp(op, lhs.normalizePolys(), rhs.normalizePolys());
            }
        }

        @Override
        public boolean isPoly() {
            if (op == Div) {
                return false;
            }
            return lhs.isPoly() && rhs.isPoly();
        }

        @Override
        Pair<MinMaxExpr, Map<String, MinMaxExpr>> normalizeByReplacingNonPolys(FreshNameGenerator fng) {
            Pair<MinMaxExpr, Map<String, MinMaxExpr>> p1 = lhs.normalizeByReplacingNonPolys(fng);
            Pair<MinMaxExpr, Map<String, MinMaxExpr>> p2 = rhs.normalizeByReplacingNonPolys(fng);
            assert p1.x.isPoly() && p2.x.isPoly();
            MinMaxExpr newLhs = p1.x;
            MinMaxExpr newRhs = p2.x;
            Map<String, MinMaxExpr> lhsSigma = p1.y;
            Map<String, MinMaxExpr> rhsSigma = p2.y;
            Map<MinMaxExpr, String> lhsSigmaInverted = lhsSigma.entrySet().stream().collect(toMap(e -> e.getValue(), e -> e.getKey()));
            Map<MinMaxExpr, String> rhsSigmaInverted = rhsSigma.entrySet().stream().collect(toMap(e -> e.getValue(), e -> e.getKey()));
            for (Entry<MinMaxExpr, String> e: lhsSigmaInverted.entrySet()) {
                if (rhsSigmaInverted.containsKey(e.getKey())) {
                    newRhs = newRhs.substitute(singletonMap(rhsSigmaInverted.get(e.getKey()), MinMaxExpr.createVar(e.getValue())));
                    rhsSigma.remove(rhsSigmaInverted.get(e.getKey()));
                }
            }
            MinMaxExpr norm = new InfixFunApp(op, newLhs, newRhs).normalizePolys();
            Map<String, MinMaxExpr> sigma = new LinkedHashMap<>();
            sigma.putAll(lhsSigma);
            sigma.putAll(rhsSigma);
            switch (op) {
                case Times:
                case Plus:
                case Minus:
                    return new Pair<>(norm, sigma);
                default:
                    String var = fng.getFreshName("x", false);
                    sigma.put(var, norm.substitute(sigma));
                    return new Pair<>(MinMaxExpr.createVar(var), sigma);
            }
        }

        @Override
        Set<String> getVariables() {
            return union(lhs.getVariables(), rhs.getVariables());
        }

        @Override
        MinMaxExpr combineMinMax() {
            return new InfixFunApp(op, lhs.combineMinMax(), rhs.combineMinMax());
        }

        @Override
        MinMaxExpr pushArithmetic() {
            if (this.op == Plus || this.op == Times) {
                if (lhs instanceof FunApp && rhs instanceof Number) {
                    FunApp lhsf = (FunApp) lhs;
                    Number rhsn = (Number) rhs;
                    switch (lhsf.op) {
                        case Min:
                        case Max:
                            Set<MinMaxExpr> newArgs = lhsf.args.stream().map(x -> new InfixFunApp(op, x, rhs).pushArithmetic()).collect(toSet());
                            switch (this.op) {
                                case Plus: return new FunApp(lhsf.op, newArgs);
                                case Times:
                                    int comp = rhsn.value.compareTo(BigInteger.ZERO);
                                    if (comp > 0) {
                                        return new FunApp(lhsf.op, newArgs);
                                    } else if (comp == 0) {
                                        return lhsf;
                                    } else if (comp < 0) {
                                        switch (lhsf.op) {
                                            case Min: return new FunApp(Max, newArgs);
                                            case Max: return new FunApp(Min, newArgs);
                                        }
                                    }
                            }
                    }
                } else if (rhs instanceof FunApp && lhs instanceof Number) {
                    return new InfixFunApp(op, rhs.pushArithmetic(), lhs.pushArithmetic());
                }
            }
            return new InfixFunApp(op, lhs.pushArithmetic(), rhs.pushArithmetic());
        }

        @Override
        MinMaxExpr filterMinMaxArguments() {
            return new InfixFunApp(op, lhs.filterMinMaxArguments(), rhs.filterMinMaxArguments());
        }

        @Override
        boolean needsBrackets() {
            return true;
        }

    }

    private static class FunApp extends MinMaxExpr {

        Op op;
        Set<MinMaxExpr> args;

        FunApp(Op op, Set<MinMaxExpr> args) {
            this.op = op;
            this.args = args;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((args == null) ? 0 : args.hashCode());
            result = prime * result + ((op == null) ? 0 : op.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            FunApp other = (FunApp) obj;
            if (args == null) {
                if (other.args != null)
                    return false;
            } else if (!args.equals(other.args))
                return false;
            if (op != other.op)
                return false;
            return true;
        }

        @Override
        public Pair<Set<SimplePolynomial>, Integer> toPolySet() {
            List<Pair<Set<SimplePolynomial>, Integer>> pArgs = args.stream().map(x -> x.toPolySet()).collect(toList());
            List<Set<SimplePolynomial>> polyArgs = pArgs.stream().map(p -> p.x).collect(toList());
            int overApproximations = pArgs.stream().collect(summingInt(p -> p.y));
            switch (op) {
                case Max:
                    Set<SimplePolynomial> polys = polyArgs.stream().reduce(singleton(SimplePolynomial.ZERO),
                            (xs, ys) -> xs.stream().flatMap(x -> ys.stream().map(y -> x.plus(y))).collect(toSet()));
                    return new Pair<>(polys, overApproximations + args.size() - 1);
                case Min:
                    return new Pair<>(polyArgs.stream().reduce(emptySet(), (y, z) -> union(y, z)), overApproximations);
                case UnaryMinus:
                    return new Pair<>(polyArgs.stream().findFirst().get().stream().map(x -> x.negate()).collect(toSet()), overApproximations);
                case Abs:
                    return new Pair<>(polyArgs.stream().findFirst().get(), overApproximations - 1);
                case Log:
                    return new Pair<>(polyArgs.get(1), overApproximations + 1);
                default:
                    throw new RuntimeException();
            }
        }

        @Override
        public String export(Export_Util eu) {
            switch (op) {
                case UnaryMinus:
                    return "-" + args.iterator().next().toString();
                case Abs:
                    return "|" + args.iterator().next().toString() + "|";
                case Max:
                    if (args.size() == 2) {
                        Iterator<MinMaxExpr> it = args.iterator();
                        MinMaxExpr fst = it.next();
                        MinMaxExpr snd = it.next();
                        MinMaxExpr zero = MinMaxExpr.createInt(BigInteger.ZERO);
                        if (fst.equals(zero)) {
                            return "nat(" + snd.export(eu) + ")";
                        } else if (snd.equals(zero)) {
                            return "nat(" + fst.export(eu) + ")";
                        }
                    }
                    // fall through is intended
                default:
                    StringBuilder res = new StringBuilder();
                    res.append(op.export(eu) + eu.escape("("));
                    Iterator<MinMaxExpr> it = args.iterator();
                    while (it.hasNext()) {
                        res.append(it.next().export(eu));
                        if (it.hasNext()) {
                            res.append(", ");
                        }
                    }
                    res.append(")");
                    return res.toString();
            }
        }

        @Override
        public MinMaxExpr substitute(Map<String, MinMaxExpr> sigma) {
            return new FunApp(op, args.stream().map(x -> x.substitute(sigma)).collect(toSet()));
        }

        @Override
        public MinMaxExpr absolutize() {
            return new FunApp(op, args.stream().map(x -> x.absolutize()).collect(toSet()));
        }

        @Override
        public boolean isPoly() {
            switch (op) {
                case Min:
                case Max:
                case Abs:
                case Log:
                    return false;
                case UnaryMinus:
                    return args.iterator().next().isPoly();
                default:
                    throw new RuntimeException();
            }
        }

        @Override
        public MinMaxExpr normalizePolys() {
            if (isPoly()) {
                Set<SimplePolynomial> polys = this.toPolySet().x;
                assert polys.size() == 1;
                return polys.iterator().next().toMinMaxExpr();
            } else {
                return new FunApp(op, args.stream().map(x -> x.normalizePolys()).collect(toSet()));
            }
        }

        @Override
        Pair<MinMaxExpr, Map<String, MinMaxExpr>> normalizeByReplacingNonPolys(FreshNameGenerator fng) {
            Set<Pair<MinMaxExpr, Map<String, MinMaxExpr>>> xs = args.stream().map(y -> y.normalizeByReplacingNonPolys(fng)).collect(toSet());
            Map<String, MinMaxExpr> varRenaming = new LinkedHashMap<>();
            Map<String, MinMaxExpr> sigma = xs.stream().map(p -> p.y).reduce(emptyMap(), (x, y) -> {
                Map<String, MinMaxExpr> res = new LinkedHashMap<>();
                res.putAll(x);
                Map<MinMaxExpr, String> xInverted = x.entrySet().stream().collect(toMap(e -> e.getValue(), e -> e.getKey()));
                Map<MinMaxExpr, String> yInverted = y.entrySet().stream().collect(toMap(e -> e.getValue(), e -> e.getKey()));
                for (Entry<MinMaxExpr, String> e: xInverted.entrySet()) {
                    if (yInverted.containsKey(e.getKey())) {
                        varRenaming.put(yInverted.get(e.getKey()), MinMaxExpr.createVar(e.getValue()));
                        y.remove(yInverted.get(e.getKey()));
                    }
                }
                res.putAll(y);
                return res;
            });
            Set<MinMaxExpr> newArgs = xs.stream().map(p -> p.x.substitute(varRenaming)).collect(toSet());
            MinMaxExpr norm = new FunApp(op, newArgs).normalizePolys();
            switch (op) {
                case Min:
                case Max:
                case Abs:
                case Log:
                    String var = fng.getFreshName("x", false);
                    sigma.put(var, norm.substitute(sigma));
                    return new Pair<>(MinMaxExpr.createVar(var), sigma);
                default: return new Pair<>(norm, sigma);
            }
        }

        @Override
        Set<String> getVariables() {
            return args.stream().flatMap(x -> x.getVariables().stream()).collect(toSet());
        }

        @Override
        MinMaxExpr combineMinMax() {
            switch (this.op) {
                case Min:
                case Max:
                    Set<MinMaxExpr> newArgs = new LinkedHashSet<>();
                    for (MinMaxExpr arg: args) {
                        if (arg instanceof FunApp) {
                            FunApp farg = (FunApp) arg;
                            if (farg.op == this.op) {
                                newArgs.addAll(farg.args);
                                continue;
                            }
                        }
                        newArgs.add(arg);
                    }
                    return new FunApp(op, newArgs.stream().map(x -> x.combineMinMax()).collect(toSet()));
                default: return new FunApp(op, args.stream().map(x -> x.combineMinMax()).collect(toSet()));
            }
        }

        @Override
        MinMaxExpr pushArithmetic() {
            return new FunApp(op, args.stream().map(x -> x.pushArithmetic()).collect(toSet()));
        }

        @Override
        MinMaxExpr filterMinMaxArguments() {
            if (op == Abs) {
                return new FunApp(op, args.stream().map(x -> x.filterMinMaxArguments()).collect(toSet()));
            }
            Set<MinMaxExpr> filteredArgs = args.stream().map(x -> x.filterMinMaxArguments()).collect(toSet());
            Set<Number> constants = args.stream().filter(x -> x instanceof Number).map(x -> (Number) x).collect(toSet());
            if (!constants.isEmpty()) {
                switch (op) {
                    case Min:
                        Number min = constants.stream().collect(maxBy((x, y) -> x.value.compareTo(y.value))).get();
                        constants.remove(min);
                        filteredArgs.removeAll(constants);
                        break;
                    case Max:
                        Number max = constants.stream().collect(maxBy((x, y) -> x.value.compareTo(y.value))).get();
                        constants.remove(max);
                        filteredArgs.removeAll(constants);
                        break;
                }
            }
            if (filteredArgs.size() == 1) {
                return filteredArgs.iterator().next();
            } else {
                return new FunApp(op, filteredArgs);
            }
        }

    }

}
