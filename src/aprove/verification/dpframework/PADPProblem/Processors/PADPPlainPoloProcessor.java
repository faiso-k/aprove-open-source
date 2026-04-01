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

public class PADPPlainPoloProcessor extends PADPProcessor {

    protected final BigInteger range;
    protected final boolean monotonic;

    @ParamsViaArgumentObject
    public PADPPlainPoloProcessor(Arguments arguments) {
        this.range = BigInteger.valueOf(arguments.range);
        this.monotonic = arguments.monotonic;
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

        PlainLinearInterpretation interp = new PlainLinearInterpretation(signature);

        PlainDioCreator dio = new PlainDioCreator();
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
            Pair<Set<Diophantine>, Diophantine> res = dio.getDio(interp.getInterpretation(rule), ConstraintType.GE, true);
            rs.addAll(res.x);
            if (this.monotonic) {
                auto.add(res.y);
            }
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
        if (this.monotonic) {
            topConj.addAll(this.makeMono(interp.getMonoCoefficients(), fsf));
        }
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
            Set<PARule> newr = null;
            Set<PARule> deletedR = null;
            if (this.monotonic) {
                newr = this.getNewR(r, auto, solution, p.size());
                deletedR = new LinkedHashSet<PARule>(r);
                deletedR.removeAll(newr);
                if ((newp.size() == p.size()) && (newr.size() == r.size())) {
                    throw new RuntimeException("Internal error 1 in PADPPlainPoloProcessor.processPADP");
                }
                PATRSProblem newpatrs = PATRSProblem.create(ImmutableCreator.create(newr), padp.getS(), padp.getE(), padp.getSortMap());
                Proof proof = new PADPPlainPoloProof(deletedP, deletedR, interp, useable);
                PADPProblem res = PADPProblem.create(ImmutableCreator.create(newp), newpatrs, padp.getDefTup());
                return ResultFactory.proved(res, YNMImplication.EQUIVALENT, proof);
            } else {
                if (newp.size() == p.size()) {
                    throw new RuntimeException("Internal error 2 in PADPPlainPoloProcessor.processPADP");
                }
                Proof proof = new PADPPlainPoloProof(deletedP, null, interp, useable);
                PADPProblem res = PADPProblem.create(ImmutableCreator.create(newp), padp.getPATRS(), padp.getDefTup());
                return ResultFactory.proved(res, YNMImplication.EQUIVALENT, proof);
            }
        }
    }

    private Set<Formula<Diophantine>> makeMono(Set<String> coeff, FullSharingFactory<Diophantine> fsf) {
        Set<Formula<Diophantine>> res = new LinkedHashSet<Formula<Diophantine>>();
        for (String c : coeff) {
            res.add(fsf.buildTheoryAtom(Diophantine.create(SimplePolynomial.create(c), ConstraintType.GT)));
        }
        return res;
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

    private Set<PARule> getNewR(List<PARule> r, List<Diophantine> auto, Map<String, BigInteger> solution, int offset) {
        Set<PARule> res = new LinkedHashSet<PARule>();
        int n = r.size();
        for (int i = 0; i < n; i++) {
            if (!this.isSatisfied(auto.get(i + offset), solution)) {
                res.add(r.get(i));
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

    /*************************************************************************/
    private static class PADPPlainPoloProof extends Proof.DefaultProof {

        private Set<PARule> deletedP;
        private Set<PARule> deletedR;
        private PlainLinearInterpretation interp;
        private PATRSProblem useable;

        public PADPPlainPoloProof(Set<PARule> deletedP, Set<PARule> deletedR, PlainLinearInterpretation interp, PATRSProblem useable) {
            this.deletedP = deletedP;
            this.deletedR = deletedR;
            this.interp = interp;
            this.useable = useable;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            if (this.deletedR != null) {
                result.append("Using a monotonic polynomial interpretation, ");
                result.append("the following dependency pairs and/or rules are removed:");
            } else {
                result.append("Using a polynomial interpretation, ");
                result.append("the following dependency pairs are removed:");
            }
            result.append(o.linebreak());
            Set<PARule> all = new LinkedHashSet<PARule>();
            all.addAll(this.deletedP);
            if (this.deletedR != null) {
                all.addAll(this.deletedR);
            }
            result.append(o.set(all, Export_Util.RULES));
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
        public boolean monotonic = false;
    }

}
