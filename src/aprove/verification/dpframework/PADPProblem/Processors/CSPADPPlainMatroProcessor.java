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

public class CSPADPPlainMatroProcessor extends CSPADPProcessor {

    protected final int dimension;
    protected final BigInteger range;

    @ParamsViaArgumentObject
    public CSPADPPlainMatroProcessor(Arguments arguments) {
        this.dimension = arguments.dimension;
        this.range = BigInteger.valueOf(arguments.range);
    }

    private boolean isStronglyConservativePA(Collection<PARule> p, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        for (PARule r : p) {
            if (!this.isStronglyConservative(r.getLeft(), r.getRight(), mu)) {
                return false;
            }
        }
        return true;
    }

    private boolean isStronglyConservative(Collection<Rule> p, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        for (Rule r : p) {
            if (!this.isStronglyConservative(r.getLeft(), r.getRight(), mu)) {
                return false;
            }
        }
        return true;
    }

    private boolean isStronglyConservative(TRSTerm s, TRSTerm t, ImmutableMap<String, ImmutableSet<Integer>> mu) {
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

    private CSPATRSProblem getUseable(CSPADPProblem cspadp, Collection<PARule> p) {
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
        List<PARule> p = new Vector<PARule>(cspadp.getP());
        CSPATRSProblem useable = this.getUseable(cspadp, p);
        List<PARule> r = new Vector<PARule>(useable.getR());
        Set<Rule> s = useable.getS();
        Set<Equation> e = useable.getE();

        CSPADPProblem dummy = CSPADPProblem.create(cspadp.getP(), useable, cspadp.getDefTup());
        Set<FunctionSymbol> signature = dummy.getSignature();

        PlainMatrixInterpretation interp = new PlainMatrixInterpretation(this.dimension, signature);

        PlainMatrixDioCreator dio = new PlainMatrixDioCreator();
        Set<Diophantine> dps = new LinkedHashSet<Diophantine>();
        List<Diophantine> auto = new Vector<Diophantine>();
        Set<Diophantine> rs = new LinkedHashSet<Diophantine>();
        Set<Diophantine> ss = new LinkedHashSet<Diophantine>();
        Set<Diophantine> es = new LinkedHashSet<Diophantine>();

        for (PARule dp : p) {
            Pair<Set<Diophantine>, Diophantine> res = dio.getDio(interp.getInterpretation(dp), ConstraintType.GE, true);
            dps.addAll(res.x);
            auto.add(res.y);
        }

        for (PARule rule : r) {
            rs.addAll(dio.getDio(interp.getInterpretation(rule), ConstraintType.GE, false).x);
        }

        for (Rule rule : s) {
            ss.addAll(dio.getDio(interp.getInterpretation(rule), ConstraintType.GE, false).x);
        }

        for (Equation eqn : e) {
            es.addAll(dio.getDio(interp.getInterpretation(eqn), ConstraintType.EQ, false).x);
        }

        dps = this.filterTrivial(dps);
        rs = this.filterTrivial(rs);
        ss = this.filterTrivial(ss);
        es = this.filterTrivial(es);

        FullSharingFactory<Diophantine> fsf = new FullSharingFactory<Diophantine>();
        List<Formula<Diophantine>> topConj = new Vector<Formula<Diophantine>>();
        topConj.addAll(this.makeAtoms(dps, fsf));
        topConj.addAll(this.makeAtoms(rs, fsf));
        topConj.addAll(this.makeAtoms(ss, fsf));
        topConj.addAll(this.makeAtoms(es, fsf));
        topConj.add(this.makeAutostrict(auto, fsf));
        Formula<Diophantine> fml = fsf.buildAnd(topConj);

        Map<String, BigInteger> rangeMap = new LinkedHashMap<String, BigInteger>();
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
            Set<PARule> newp = this.getNewP(p, auto, solution);
            Set<PARule> deletedP = new LinkedHashSet<PARule>(p);
            deletedP.removeAll(newp);
            if (newp.size() == p.size()) {
                throw new RuntimeException("Internal error in CSPADPPlainMatroProcessor.processCSPADP");
            }
            Proof proof = new CSPADPPlainMatroProof(deletedP, interp, useable);
            CSPADPProblem res = CSPADPProblem.create(ImmutableCreator.create(newp), cspadp.getCSPATRS(), cspadp.getDefTup());
            return ResultFactory.proved(res, YNMImplication.EQUIVALENT, proof);
        }
    }

    private Set<PARule> getNewP(List<PARule> p, List<Diophantine> auto, Map<String, BigInteger> solution) {
        Set<PARule> res = new LinkedHashSet<PARule>();
        int n = p.size();
        for (int i = 0; i < n; i++) {
            if (!this.isSatisfied(auto.get(i), solution)) {
                res.add(p.get(i));
            }
        }
        return res;
    }

    protected boolean isSatisfied(Diophantine dio, Map<String, BigInteger> solution) {
        return this.isTrivial(Diophantine.create(dio.getLeft().specialize(solution), dio.getRight().specialize(solution), dio.getRelation()));
    }

    protected List<Formula<Diophantine>> makeAtoms(Set<Diophantine> dios, FullSharingFactory<Diophantine> fsf) {
        List<Formula<Diophantine>> res = new Vector<Formula<Diophantine>>();
        for (Diophantine dio : dios) {
            res.add(fsf.buildTheoryAtom(dio));
        }
        return res;
    }

    protected Formula<Diophantine> makeAutostrict(List<Diophantine> dios, FullSharingFactory<Diophantine> fsf) {
        List<Formula<Diophantine>> res = new Vector<Formula<Diophantine>>();
        for (Diophantine dio : dios) {
            res.add(fsf.buildTheoryAtom(dio));
        }
        return fsf.buildOr(res);
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

    /*********************************************************************/
    private static class CSPADPPlainMatroProof extends Proof.DefaultProof {

        private Set<PARule> deletedP;
        private PlainMatrixInterpretation interp;
        private CSPATRSProblem useable;

        public CSPADPPlainMatroProof(Set<PARule> deletedP, PlainMatrixInterpretation interp, CSPATRSProblem useable) {
            this.deletedP = deletedP;
            this.interp = interp;
            this.useable = useable;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            result.append("Using a matrix interpretation, ");
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
        public int dimension = 2;
        public int range = 1;
    }

}
