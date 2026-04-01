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

public class PADPPlainMatroProcessor extends PADPProcessor {

    protected final int dimension;
    protected final BigInteger range;

    @ParamsViaArgumentObject
    public PADPPlainMatroProcessor(Arguments arguments) {
        this.dimension = arguments.dimension;
        this.range = BigInteger.valueOf(arguments.range);
    }

    @Override
    protected Result processPADP(PADPProblem padp, Abortion aborter) throws AbortionException {
        List<PARule> p = new Vector<PARule>(padp.getP());
        PATRSProblem useable = new PAUseable(padp).getUseable(p);
        List<PARule> r = new Vector<PARule>(useable.getR());
        Set<Rule> s = useable.getS();
        Set<Equation> e = useable.getE();

        PADPProblem dummy = PADPProblem.create(padp.getP(), useable, padp.getDefTup());
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
                throw new RuntimeException("Internal error in PADPPlainMatroProcessor.processPADP");
            }
            Proof proof = new PADPPlainMatroProof(deletedP, interp, useable);
            PADPProblem res = PADPProblem.create(ImmutableCreator.create(newp), padp.getPATRS(), padp.getDefTup());
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

    /*******************************************************************/
    private static class PADPPlainMatroProof extends Proof.DefaultProof {

        private Set<PARule> deletedP;
        private PlainMatrixInterpretation interp;
        private PATRSProblem useable;

        public PADPPlainMatroProof(Set<PARule> deletedP, PlainMatrixInterpretation interp, PATRSProblem useable) {
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
