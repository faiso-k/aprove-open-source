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

public class PADPMonotonicPoloProcessor extends PADPPoloProcessor {

    @ParamsViaArgumentObject
    public PADPMonotonicPoloProcessor(PADPPoloProcessor.Arguments arguments) {
        super(arguments);
    }

    @Override
    protected Result processPADP(PADPProblem padp, Abortion aborter) throws AbortionException {
        if (this.cannotBeUsed(padp)) {
            return ResultFactory.unsuccessful();
        }

        List<PARule> p = new Vector<PARule>(padp.getP());
        PATRSProblem useable = new PAUseable(padp).getUseable(p);
        List<PARule> r = new Vector<PARule>(useable.getR());
        Set<Rule> s = useable.getS();
        Set<Equation> e = useable.getE();

        PADPProblem dummy = PADPProblem.create(padp.getP(), useable, padp.getDefTup());
        ImmutableMap<String, ImmutableList<String>> sortMap = dummy.getSortMap();
        ImmutableSet<FunctionSymbol> tupleSymbols = dummy.getTupleSymbols();
        Set<FunctionSymbol> signature = dummy.getSignature();
        Map<FunctionSymbol, FunctionSymbol> defTup = dummy.getDefTup();

        LinearInterpretation interp = new LinearInterpretation(p, signature, sortMap, tupleSymbols, defTup, this.range, this.noIntDependence);

        DioCreator dio = new DioCreator(this.noIntDependence);
        List<Pair<Set<Diophantine>, Set<Diophantine>>> prs = new Vector<Pair<Set<Diophantine>, Set<Diophantine>>>();
        List<Pair<Set<Diophantine>, Set<Diophantine>>> bounds = new Vector<Pair<Set<Diophantine>, Set<Diophantine>>>();
        Set<Diophantine> ss = new LinkedHashSet<Diophantine>();
        Set<Diophantine> es = new LinkedHashSet<Diophantine>();

        List<PARule> pr = new Vector<PARule>();
        pr.addAll(p);
        pr.addAll(r);
        for (PARule ru : pr) {
            Map<TRSVariable, String> varSorts = this.getVarSorts(ru.getLeft(), sortMap, defTup);
            Pair<Set<Diophantine>, Set<Diophantine>> res = dio.getDio(interp.getInterpretation(ru), ConstraintType.GE, true, varSorts, false);
            Set<Diophantine> p1 = res.x;
            Set<Diophantine> boundy1 = res.y;
            boundy1.addAll(dio.getDio(interp.getBoundInterpretation(ru), ConstraintType.GE, false, varSorts, false).x);
            res = dio.getDio(interp.getInterpretation(ru), ConstraintType.GE, true, varSorts, true);
            Set<Diophantine> p2 = res.x;
            Set<Diophantine> boundy2 = res.y;
            boundy2.addAll(dio.getDio(interp.getBoundInterpretation(ru), ConstraintType.GE, false, varSorts, true).x);
            prs.add(new Pair<Set<Diophantine>, Set<Diophantine>>(p1, p2));
            bounds.add(new Pair<Set<Diophantine>, Set<Diophantine>>(boundy1, boundy2));
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

        prs = this.filterTrivial(prs);
        bounds = this.filterTrivial(bounds);
        ss = this.filterTrivial(ss);
        es = this.filterTrivial(es);

        FullSharingFactory<Diophantine> fsf = new FullSharingFactory<Diophantine>();
        List<Formula<Diophantine>> topConj = new Vector<Formula<Diophantine>>();
        topConj.addAll(this.makeDPs(prs, fsf));
        topConj.addAll(this.makeAtoms(ss, fsf));
        topConj.addAll(this.makeAtoms(es, fsf));
        topConj.add(this.makeAutostrict(bounds, fsf));
        topConj.addAll(this.makeMono(interp.getMonoCoefficients(), fsf));
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
            Set<PARule> newp = this.getNewRules(p, bounds, solution, 0);
            Set<PARule> deletedP = new LinkedHashSet<PARule>(p);
            deletedP.removeAll(newp);
            Set<PARule> newr = this.getNewRules(r, bounds, solution, p.size());
            Set<PARule> deletedR = new LinkedHashSet<PARule>(r);
            deletedR.removeAll(newr);
            if ((newp.size() == p.size()) && (newr.size() == r.size())) {
                throw new RuntimeException("Internal error in PADPMonotonicPoloProcessor.processPADP");
            }
            PATRSProblem newpatrs = PATRSProblem.create(ImmutableCreator.create(newr), padp.getS(), padp.getE(), padp.getSortMap());
            Proof proof = new PADPMonotonicPoloProof(deletedP, deletedR, interp, useable);
            PADPProblem res = PADPProblem.create(ImmutableCreator.create(newp), newpatrs, padp.getDefTup());
            return ResultFactory.proved(res, YNMImplication.EQUIVALENT, proof);
        }
    }

    private Set<Formula<Diophantine>> makeMono(Set<String> coeff, FullSharingFactory<Diophantine> fsf) {
        Set<Formula<Diophantine>> res = new LinkedHashSet<Formula<Diophantine>>();
        for (String c : coeff) {
            res.add(fsf.buildTheoryAtom(Diophantine.create(SimplePolynomial.create(c), ConstraintType.GT)));
        }
        return res;
    }

    private Set<PARule> getNewRules(List<PARule> p, List<Pair<Set<Diophantine>, Set<Diophantine>>> bounds, Map<String, BigInteger> solution, int offset) {
        Set<PARule> res = new LinkedHashSet<PARule>();
        int n = p.size();
        for (int i = 0; i < n; i++) {
            if (!this.isSatisfied(bounds.get(i + offset), solution)) {
                res.add(p.get(i));
            }
        }
        return res;
    }

    /*************************************************************************/
    private static class PADPMonotonicPoloProof extends Proof.DefaultProof {

        private Set<PARule> deletedP;
        private Set<PARule> deletedR;
        private LinearInterpretation interp;
        private PATRSProblem useable;

        public PADPMonotonicPoloProof(Set<PARule> deletedP, Set<PARule> deletedR, LinearInterpretation interp, PATRSProblem useable) {
            this.deletedP = deletedP;
            this.deletedR = deletedR;
            this.interp = interp;
            this.useable = useable;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            result.append("Using a monotonic PA-polynomial interpretation, ");
            result.append("the following dependency pairs and/or rules are removed:");
            result.append(o.linebreak());
            Set<PARule> all = new LinkedHashSet<PARule>();
            all.addAll(this.deletedP);
            all.addAll(this.deletedR);
            result.append(o.set(all, Export_Util.RULES));
            result.append(o.linebreak());
            result.append("Needed ");
            result.append(this.useable.export(o));
            result.append("Used ");
            result.append(this.interp.export(o));
            return result.toString();
        }

    }

}
