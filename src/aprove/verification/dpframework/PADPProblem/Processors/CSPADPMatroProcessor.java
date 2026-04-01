package aprove.verification.dpframework.PADPProblem.Processors;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.PADPProblem.*;
import aprove.verification.dpframework.PADPProblem.Utility.*;
import aprove.verification.dpframework.PATRSProblem.*;
import aprove.verification.dpframework.PATRSProblem.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

public class CSPADPMatroProcessor extends CSPADPProcessor {

    protected final BigInteger range;
    protected final boolean noIntDependence;
    protected final int dimension;

    @ParamsViaArgumentObject
    public CSPADPMatroProcessor(Arguments arguments) {
        this.range = BigInteger.valueOf(arguments.range);
        this.noIntDependence = arguments.noIntDependence;
        this.dimension = arguments.dimension;
    }

    private boolean containsBaseFun(ImmutableMap<String, ImmutableList<String>> sortMap) {
        for (Map.Entry<String, ImmutableList<String>> entry : sortMap.entrySet()) {
            String name = entry.getKey();
            ImmutableList<String> sorts = entry.getValue();
            if (name.equals("0") || name.equals("1") || name.equals("+") || name.equals("-")) {
                continue;
            } else {
                if (sorts.get(sorts.size() - 1).equals("int")) {
                    return true;
                }
            }
        }
        return false;
    }

    private boolean isPA(Collection<PARule> P, ImmutableMap<String, ImmutableList<String>> sortMap, Map<FunctionSymbol, FunctionSymbol> def_tup) {
        Set<FunctionSymbol> pafuns = new LinkedHashSet<FunctionSymbol>();
        pafuns.add(FunctionSymbol.create("0", 0));
        pafuns.add(FunctionSymbol.create("1", 0));
        pafuns.add(FunctionSymbol.create("-", 1));
        pafuns.add(FunctionSymbol.create("+", 2));
        for (PARule p : P) {
            if (!this.isPA(p, sortMap, def_tup, pafuns)) {
                return false;
            }
        }
        return true;
    }

    private boolean isPA(PARule p, ImmutableMap<String, ImmutableList<String>> sortMap, Map<FunctionSymbol, FunctionSymbol> def_tup, Set<FunctionSymbol> pafuns) {
        TRSFunctionApplication ft = (TRSFunctionApplication) p.getRight();
        FunctionSymbol f = ft.getRootSymbol();
        List<String> fsorts = sortMap.get(this.getDef(f, def_tup).getName());
        int arr = f.getArity();
        for (int i = 0; i < arr; i++) {
            if (!fsorts.get(i).equals("int")) {
                return false;
            }
        }

        Set<FunctionSymbol> funs = new LinkedHashSet<FunctionSymbol>();
        for (TRSTerm arg : ft.getArguments()) {
            funs.addAll(arg.getFunctionSymbols());
        }
        return pafuns.containsAll(funs);
    }

    protected boolean cannotBeUsed(CSPADPProblem cspadp) {
        return !this.isPA(cspadp.getP(), cspadp.getSortMap(), cspadp.getDefTup()) && this.containsBaseFun(cspadp.getSortMap());
    }

    protected boolean isStronglyConservativePA(Collection<PARule> p, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        for (PARule r : p) {
            if (!this.isStronglyConservative(r.getLeft(), r.getRight(), mu)) {
                return false;
            }
        }
        return true;
    }

    protected boolean isStronglyConservative(Collection<Rule> p, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        for (Rule r : p) {
            if (!this.isStronglyConservative(r.getLeft(), r.getRight(), mu)) {
                return false;
            }
        }
        return true;
    }

    protected boolean isStronglyConservative(TRSTerm s, TRSTerm t, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        if (!CSTermHelper.getActiveVariables(s, mu).containsAll(CSTermHelper.getActiveVariables(t, mu))) {
            return false;
        }
        if (!this.intersect(CSTermHelper.getActiveVariables(s, mu), CSTermHelper.getInactiveVariables(s, mu)).isEmpty()) {
            return false;
        }
        if (!this.intersect(CSTermHelper.getActiveVariables(t, mu), CSTermHelper.getInactiveVariables(t, mu)).isEmpty()) {
            return false;
        }
        return true;
    }

    private<T> Set<T> intersect(Set<T> x, Set<T> y) {
        Set<T> res = new LinkedHashSet<T>(x);
        res.retainAll(y);
        return res;
    }

    protected CSPATRSProblem getUseable(CSPADPProblem cspadp, Collection<PARule> p) {
        ImmutableMap<String, ImmutableSet<Integer>> mu = cspadp.getMu();
        CSPATRSProblem useable = null;
        if (this.isStronglyConservativePA(p, mu)) {
            useable = new CSPAUseableStronglyConservative(cspadp).getUseable(p);
            if (!this.isStronglyConservativePA(useable.getR(), mu) || !this.isStronglyConservative(useable.getS(), mu)) {
                useable = new CSPAUseable(cspadp).getUseable(p);
            }
        } else {
            useable = new CSPAUseable(cspadp).getUseable(p);
        }
        return useable;
    }

    @Override
    protected Result processCSPADP(CSPADPProblem cspadp, Abortion aborter) throws AbortionException {
        if (this.cannotBeUsed(cspadp)) {
            return ResultFactory.unsuccessful();
        }

        List<PARule> p = new Vector<PARule>(cspadp.getP());
        CSPATRSProblem useable = this.getUseable(cspadp, p);
        Set<PARule> r = useable.getR();
        Set<Rule> s = useable.getS();
        Set<Equation> e = useable.getE();

        CSPADPProblem dummy = CSPADPProblem.create(cspadp.getP(), useable, cspadp.getDefTup());
        ImmutableMap<String, ImmutableList<String>> sortMap = dummy.getSortMap();
        ImmutableSet<FunctionSymbol> tupleSymbols = dummy.getTupleSymbols();
        Set<FunctionSymbol> signature = dummy.getSignature();
        Map<FunctionSymbol, FunctionSymbol> defTup = dummy.getDefTup();

        MatrixInterpretation interp = new MatrixInterpretation(p, signature, sortMap, tupleSymbols, defTup, this.range, this.noIntDependence, this.dimension);

        MatrixDioCreator dio = new MatrixDioCreator(this.noIntDependence, this.dimension);
        List<Pair<Set<Diophantine>, Set<Diophantine>>> dps = new Vector<Pair<Set<Diophantine>, Set<Diophantine>>>();
        List<Pair<Set<Diophantine>, Set<Diophantine>>> bounds = new Vector<Pair<Set<Diophantine>, Set<Diophantine>>>();
        Set<Diophantine> rs = new LinkedHashSet<Diophantine>();
        Set<Diophantine> ss = new LinkedHashSet<Diophantine>();
        Set<Diophantine> es = new LinkedHashSet<Diophantine>();

        for (PARule dp : p) {
            Map<TRSVariable, String> varSorts = this.getVarSorts(dp.getLeft(), sortMap, defTup);
            Pair<Set<Diophantine>, Set<Diophantine>> res = dio.getDio(interp.getInterpretation(dp), ConstraintType.GE, true, varSorts, false);
            Set<Diophantine> p1 = res.x;
            Set<Diophantine> boundy1 = res.y;
            boundy1.addAll(dio.getDio(interp.getBoundInterpretation(dp), ConstraintType.GE, false, varSorts, false).x);
            res = dio.getDio(interp.getInterpretation(dp), ConstraintType.GE, true, varSorts, true);
            Set<Diophantine> p2 = res.x;
            Set<Diophantine> boundy2 = res.y;
            boundy2.addAll(dio.getDio(interp.getBoundInterpretation(dp), ConstraintType.GE, false, varSorts, true).x);
            dps.add(new Pair<Set<Diophantine>, Set<Diophantine>>(p1, p2));
            bounds.add(new Pair<Set<Diophantine>, Set<Diophantine>>(boundy1, boundy2));
        }

        for (PARule rule : r) {
            Map<TRSVariable, String> varSorts = this.getVarSorts(rule.getLeft(), sortMap, defTup);
            rs.addAll(dio.getDio(interp.getInterpretation(rule), ConstraintType.GE, false, varSorts, false).x);
        }

        for (Rule rule : s) {
            if (this.isIntRule(rule, sortMap)) {
                ss.addAll(dio.getDio(interp.getInterpretation(rule), ConstraintType.EQ, false).x);
            } else {
                ss.addAll(dio.getDio(interp.getInterpretation(rule), ConstraintType.GE, false).x);
            }
        }

        for (Equation eqn : e) {
            es.addAll(dio.getDio(interp.getInterpretation(eqn), ConstraintType.EQ, false).x);
        }

        dps = this.filterTrivial(dps);
        bounds = this.filterTrivial(bounds);
        rs = this.filterTrivial(rs);
        ss = this.filterTrivial(ss);
        es = this.filterTrivial(es);

        FullSharingFactory<Diophantine> fsf = new FullSharingFactory<Diophantine>();
        List<Formula<Diophantine>> topConj = new Vector<Formula<Diophantine>>();
        topConj.addAll(this.makeDPs(dps, fsf));
        topConj.addAll(this.makeAtoms(rs, fsf));
        topConj.addAll(this.makeAtoms(ss, fsf));
        topConj.addAll(this.makeAtoms(es, fsf));
        topConj.add(this.makeAutostrict(bounds, fsf));
        Formula<Diophantine> fml = fsf.buildAnd(topConj);

        Map<String, BigInteger> rangeMap = new LinkedHashMap<String, BigInteger>();
        BigInteger two = BigInteger.valueOf(2l);
        for (String coeff : interp.getZCoefficients()) {
            rangeMap.put(coeff, this.range.multiply(two));
        }
        MINISATEngine.Arguments args = new MINISATEngine.Arguments();
        args.version = 2;
        MINISATEngine engine = new MINISATEngine(args);
        SatSearch satsearch = SatSearch.create(engine, PlainSPCToCircuitConverter.create(new FullSharingFlatteningFactory<None>(), rangeMap, this.range, new PoloSatConfigInfo()));

        Map<String, BigInteger> solution = satsearch.search(fml, aborter);
        if (solution == null) {
            return ResultFactory.unsuccessful();
        } else {
            for (String coeff : interp.getCoefficients()) {
                if (solution.get(coeff) == null) {
                    solution.put(coeff, BigInteger.ZERO);
                }
            }
            interp = interp.specialize(solution);
            Set<PARule> newp = this.getNewP(p, bounds, solution);
            Set<PARule> deletedP = new LinkedHashSet<PARule>(p);
            deletedP.removeAll(newp);
            if (newp.size() == p.size()) {
                throw new RuntimeException("Internal error in PADPMatroProcessor.processPADP");
            }
            Proof proof = new CSPADPMatroProof(deletedP, interp, useable);
            CSPADPProblem res = CSPADPProblem.create(ImmutableCreator.create(newp), cspadp.getCSPATRS(), cspadp.getDefTup());
            return ResultFactory.proved(res, YNMImplication.EQUIVALENT, proof);
        }
    }

    private Set<PARule> getNewP(List<PARule> p, List<Pair<Set<Diophantine>, Set<Diophantine>>> bounds, Map<String, BigInteger> solution) {
        Set<PARule> res = new LinkedHashSet<PARule>();
        int n = p.size();
        for (int i = 0; i < n; i++) {
            if (!this.isSatisfied(bounds.get(i), solution)) {
                res.add(p.get(i));
            }
        }
        return res;
    }

    protected boolean isIntRule(Rule r, ImmutableMap<String, ImmutableList<String>> sortMap) {
        FunctionSymbol f = r.getLeft().getRootSymbol();
        return sortMap.get(f.getName()).get(f.getArity()).equals("int");
    }

    protected boolean isSatisfied(Pair<Set<Diophantine>, Set<Diophantine>> boundy, Map<String, BigInteger> solution) {
        if (this.isSatisfied(boundy.x, solution)) {
            return true;
        } else {
            return this.isSatisfied(boundy.y, solution);
        }
    }

    protected boolean isSatisfied(Set<Diophantine> dios, Map<String, BigInteger> solution) {
        Set<Diophantine> newDios = new LinkedHashSet<Diophantine>();
        for (Diophantine dio : dios) {
            newDios.add(Diophantine.create(dio.getLeft().specialize(solution), dio.getRight().specialize(solution), dio.getRelation()));
        }
        return this.filterTrivial(newDios).isEmpty();
    }

    protected List<Formula<Diophantine>> makeAtoms(Set<Diophantine> dios, FullSharingFactory<Diophantine> fsf) {
        List<Formula<Diophantine>> res = new Vector<Formula<Diophantine>>();
        for (Diophantine dio : dios) {
            res.add(fsf.buildTheoryAtom(dio));
        }
        return res;
    }

    protected Formula<Diophantine> makeAutostrict(List<Pair<Set<Diophantine>, Set<Diophantine>>> inp, FullSharingFactory<Diophantine> fsf) {
        List<Formula<Diophantine>> res = new Vector<Formula<Diophantine>>();
        for (Pair<Set<Diophantine>, Set<Diophantine>> diopair : inp) {
            Set<Diophantine> s1 = diopair.x;
            Set<Diophantine> s2 = diopair.y;
            if (s1.equals(s2)) {
                res.add(fsf.buildAnd(this.makeAtoms(s1, fsf)));
            } else {
                res.add(fsf.buildAnd(this.makeAtoms(s1, fsf)));
                res.add(fsf.buildAnd(this.makeAtoms(s2, fsf)));
            }
        }
        return fsf.buildOr(res);
    }

    protected List<Formula<Diophantine>> makeDPs(List<Pair<Set<Diophantine>, Set<Diophantine>>> inp, FullSharingFactory<Diophantine> fsf) {
        List<Formula<Diophantine>> res = new Vector<Formula<Diophantine>>();
        for (Pair<Set<Diophantine>, Set<Diophantine>> diopair : inp) {
            Set<Diophantine> s1 = diopair.x;
            Set<Diophantine> s2 = diopair.y;
            if (s1.equals(s2)) {
                res.add(fsf.buildAnd(this.makeAtoms(s1, fsf)));
            } else {
                List<Formula<Diophantine>> tmp = new Vector<Formula<Diophantine>>();
                tmp.add(fsf.buildAnd(this.makeAtoms(s1, fsf)));
                tmp.add(fsf.buildAnd(this.makeAtoms(s2, fsf)));
                res.add(fsf.buildOr(tmp));
            }
        }
        return res;
    }

    protected Set<Diophantine> filterTrivial(Set<Diophantine> inp) {
        Set<Diophantine> res = new LinkedHashSet<Diophantine>();
        for (Diophantine dio : inp) {
            if (!this.isTrivial(dio)) {
                res.add(dio);
            }
        }
        return res;
    }

    protected List<Pair<Set<Diophantine>, Set<Diophantine>>> filterTrivial(List<Pair<Set<Diophantine>, Set<Diophantine>>> inp) {
        List<Pair<Set<Diophantine>, Set<Diophantine>>> res = new Vector<Pair<Set<Diophantine>, Set<Diophantine>>>();
        for (Pair<Set<Diophantine>, Set<Diophantine>> dios : inp) {
            res.add(new Pair<Set<Diophantine>, Set<Diophantine>>(this.filterTrivial(dios.x), this.filterTrivial(dios.y)));
        }
        return res;
    }

    protected boolean isTrivial(Diophantine dio) {
        SimplePolynomial left = dio.getLeft();
        SimplePolynomial right = dio.getRight();
        ConstraintType ct = dio.getRelation();
        if (left.isConstant() && right.isConstant()) {
            int cmp = left.getNumericalAddend().compareTo(right.getNumericalAddend());
            return (ct.equals(ConstraintType.EQ) && cmp == 0) ||
                   (ct.equals(ConstraintType.GE) && cmp >= 0) ||
                   (ct.equals(ConstraintType.GT) && cmp == 1);
        } else {
            return false;
        }
    }

    protected Map<TRSVariable, String> getVarSorts(TRSTerm t, ImmutableMap<String, ImmutableList<String>> sortMap, Map<FunctionSymbol, FunctionSymbol> defTup) {
        if (t.isVariable()) {
            throw new RuntimeException("Internal error in PADPMatroProcessor.getVarSorts");
        } else {
            Map<TRSVariable, String> varSorts = new LinkedHashMap<TRSVariable, String>();
            this.getVarSortsAux(t, sortMap, defTup, varSorts);
            return varSorts;
        }
    }

    protected void getVarSortsAux(TRSTerm t, ImmutableMap<String, ImmutableList<String>> sortMap, Map<FunctionSymbol, FunctionSymbol> defTup, Map<TRSVariable, String> varSorts) {
        if (t instanceof TRSVariable) {
            return;
        }
        TRSFunctionApplication ft = (TRSFunctionApplication) t;
        FunctionSymbol f = ft.getRootSymbol();
        ImmutableList<String> sorts = sortMap.get(f.getName());
        if (sorts == null) {
            sorts = sortMap.get(this.getDef(f, defTup).getName());
        }
        for (int i = 0; i < sorts.size() - 1; i++) {
            TRSTerm tt = ft.getArgument(i);
            if (tt instanceof TRSVariable) {
                varSorts.put((TRSVariable) tt, sorts.get(i));
            } else {
                this.getVarSortsAux(tt, sortMap, defTup, varSorts);
            }
        }
    }

    protected FunctionSymbol getDef(FunctionSymbol f, Map<FunctionSymbol, FunctionSymbol> defTup) {
        for (FunctionSymbol g : defTup.keySet()) {
            if (f.equals(defTup.get(g))) {
                return g;
            }
        }
        return null;
    }

    /*************************************************************************/
    private static class CSPADPMatroProof extends Proof.DefaultProof {

        private Set<PARule> deletedP;
        private MatrixInterpretation interp;
        private CSPATRSProblem useable;

        public CSPADPMatroProof(Set<PARule> deletedP, MatrixInterpretation interp, CSPATRSProblem useable) {
            this.deletedP = deletedP;
            this.interp = interp;
            this.useable = useable;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            result.append("Using a PA-matrix interpretation, ");
            result.append("the following dependency pairs are removed:");
            result.append(o.linebreak());
            result.append(o.set(this.deletedP, Export_Util.RULES));
            result.append(o.linebreak());
            result.append("Needed ");
            result.append(this.useable.export(o));
            result.append("Used ");
            result.append(this.interp.export(o));
            return result.toString();
        }

    }

    public static class Arguments {
        public int range = 1;
        public boolean noIntDependence = true;
        public int dimension = 2;
    }

}

