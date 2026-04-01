package aprove.verification.dpframework.PADPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.PADPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

@NoParams
public class PADPSubtermProcessor extends PADPProcessor {

    @Override
    protected Result processPADP(PADPProblem padp, Abortion aborter) throws AbortionException {
        Set<PARule> p = new LinkedHashSet<PARule>(padp.getP());
        Set<FunctionSymbol> tups = padp.getTupleSymbols();
        SubtermModE subby = SubtermModE.create(padp.getE());

        Set<Map<FunctionSymbol, Integer>> projs = new LinkedHashSet<Map<FunctionSymbol, Integer>>();
        projs.add(new HashMap<FunctionSymbol, Integer>());

        for (PARule dp : p) {
            if (projs.isEmpty()) {
                return ResultFactory.unsuccessful();
            }
            projs = this.joinAll(projs, this.findProj(dp, this.meetAll(projs, tups), subby), tups);
        }

        Map<FunctionSymbol, Integer> theProj = null;
        Set<PARule> deletedP = null;
        for (Map<FunctionSymbol, Integer> proj : projs) {
            theProj = proj;
            deletedP = this.getDeletedP(p, theProj, subby);
            if (!deletedP.isEmpty()) {
                break;
            }
        }

        if (deletedP == null || deletedP.isEmpty()) {
            return ResultFactory.unsuccessful();
        }

        p.removeAll(deletedP);
        Proof proof = new PADPSubtermProof(deletedP, this.getAfs(theProj, tups));
        PADPProblem newPADP = PADPProblem.create(ImmutableCreator.create(p), padp.getPATRS(), padp.getDefTup());
        return ResultFactory.proved(newPADP, YNMImplication.EQUIVALENT, proof);
    }

    private Set<PARule> getDeletedP(Set<PARule> p, Map<FunctionSymbol, Integer> proj, SubtermModE subby) {
        Set<PARule> res = new LinkedHashSet<PARule>();
        for (PARule dp : p) {
            TRSFunctionApplication l = dp.getLeft();
            TRSFunctionApplication r = (TRSFunctionApplication) dp.getRight();
            Integer il = proj.get(l.getRootSymbol());
            Integer ir = proj.get(r.getRootSymbol());
            if (subby.solves(Constraint.create(l.getArgument(il.intValue()), r.getArgument(ir.intValue()), OrderRelation.GR))) {
                res.add(dp);
            }
        }
        return res;
    }

    private Afs getAfs(Map<FunctionSymbol, Integer> p, Set<FunctionSymbol> tups) {
        Afs res = new Afs();
        for (FunctionSymbol f : tups) {
            res.setCollapsing(f, p.get(f).intValue());
        }
        return res;
    }

    private Set<Map<FunctionSymbol, Integer>> findProj(PARule dp, Map<FunctionSymbol, Integer> p, SubtermModE subby) {
        TRSFunctionApplication l = dp.getLeft();
        TRSFunctionApplication r = (TRSFunctionApplication) dp.getRight();
        FunctionSymbol fl = l.getRootSymbol();
        FunctionSymbol fr = r.getRootSymbol();

        if (fl.equals(fr)) {
            Integer i = p.get(fl);
            Set<Integer> pospos = new LinkedHashSet<Integer>();
            if (i != null) {
                pospos.add(i);
            } else {
                pospos.addAll(this.getPosPos(fl.getArity()));
            }
            return this.findProjOne(l, r, pospos, subby);
        } else {
            Integer il = p.get(fl);
            Integer ir = p.get(fr);
            Set<Integer> posposl = new LinkedHashSet<Integer>();
            Set<Integer> posposr = new LinkedHashSet<Integer>();
            if (il != null) {
                posposl.add(il);
            } else {
                posposl.addAll(this.getPosPos(fl.getArity()));
            }
            if (ir != null) {
                posposr.add(ir);
            } else {
                posposr.addAll(this.getPosPos(fr.getArity()));
            }
            return this.findProjTwo(l, r, posposl, posposr, subby);
        }
    }

    private Set<Map<FunctionSymbol, Integer>> findProjOne(TRSFunctionApplication l, TRSFunctionApplication r, Set<Integer> pospos, SubtermModE subby) {
        Set<Map<FunctionSymbol, Integer>> res = new LinkedHashSet<Map<FunctionSymbol, Integer>>();
        for (Integer j : pospos) {
            int i = j.intValue();
            if (subby.solves(Constraint.create(l.getArgument(i), r.getArgument(i), OrderRelation.GE))) {
                Map<FunctionSymbol, Integer> p = new HashMap<FunctionSymbol, Integer>();
                p.put(l.getRootSymbol(), Integer.valueOf(i));
                res.add(p);
            }
        }
        return res;
    }

    private Set<Map<FunctionSymbol, Integer>> findProjTwo(TRSFunctionApplication l, TRSFunctionApplication r, Set<Integer> posposl, Set<Integer> posposr, SubtermModE subby) {
        Set<Map<FunctionSymbol, Integer>> res = new LinkedHashSet<Map<FunctionSymbol, Integer>>();
        for (Integer jl : posposl) {
            int il = jl.intValue();
            for (Integer jr : posposr) {
                int ir = jr.intValue();
                if (subby.solves(Constraint.create(l.getArgument(il), r.getArgument(ir), OrderRelation.GE))) {
                    Map<FunctionSymbol, Integer> p = new HashMap<FunctionSymbol, Integer>();
                    p.put(l.getRootSymbol(), Integer.valueOf(il));
                    p.put(r.getRootSymbol(), Integer.valueOf(ir));
                    res.add(p);
                }
            }
        }
        return res;
    }

    private Set<Integer> getPosPos(int i) {
        Set<Integer> res = new LinkedHashSet<Integer>();
        for (int j = 0; j < i; j++) {
            res.add(Integer.valueOf(j));
        }
        return res;
    }

    private Map<FunctionSymbol, Integer> meetAll(Set<Map<FunctionSymbol, Integer>> projs, Set<FunctionSymbol> tups) {
        if (projs.isEmpty()) {
            return new HashMap<FunctionSymbol, Integer>();
        }
        Map<FunctionSymbol, Integer> res = null;
        for (Map<FunctionSymbol, Integer> proj : projs) {
            if (res == null) {
                res = proj;
            } else {
                res = this.meet(res, proj, tups);
            }
        }
        return res;
    }

    private Map<FunctionSymbol, Integer> meet(Map<FunctionSymbol, Integer> p1, Map<FunctionSymbol, Integer> p2, Set<FunctionSymbol> tups) {
        Map<FunctionSymbol, Integer> res = new HashMap<FunctionSymbol, Integer>();
        for (FunctionSymbol f : tups) {
            Integer i1 = p1.get(f);
            Integer i2 = p2.get(f);
            if (i1 != null && i2 != null && i1.equals(i2)) {
                res.put(f, i1);
            }
        }
        return res;
    }

    private Set<Map<FunctionSymbol, Integer>> joinAll(Set<Map<FunctionSymbol, Integer>> s1, Set<Map<FunctionSymbol, Integer>> s2, Set<FunctionSymbol> tups) {
        Set<Map<FunctionSymbol, Integer>> res = new LinkedHashSet<Map<FunctionSymbol, Integer>>();
        for (Map<FunctionSymbol, Integer> proj1 : s1) {
            for (Map<FunctionSymbol, Integer> proj2 : s2) {
                Map<FunctionSymbol, Integer> proj12 = this.join(proj1, proj2, tups);
                if (proj12 != null) {
                    res.add(proj12);
                }
            }
        }
        return res;
    }

    private Map<FunctionSymbol, Integer> join(Map<FunctionSymbol, Integer> p1, Map<FunctionSymbol, Integer> p2, Set<FunctionSymbol> tups) {
        Map<FunctionSymbol, Integer> res = new HashMap<FunctionSymbol, Integer>();
        for (FunctionSymbol f : tups) {
            Integer i1 = p1.get(f);
            Integer i2 = p2.get(f);
            if (i1 != null && i2 != null) {
                if (!i1.equals(i2)) {
                    //disagree
                    return null;
                } else {
                    //agree
                    res.put(f, i1);
                }
            } else if (i1 == null) {
                if (i2 != null) {
                    res.put(f, i2);
                }
            } else {
                //i2 == null
                if (i1 != null) {
                    res.put(f, i1);
                }
            }
        }
        return res;
    }

    private static class PADPSubtermProof extends Proof.DefaultProof {

        private Set<PARule> deletedPairs;
        private Afs proj;

        private PADPSubtermProof(Set<PARule> deletedPairs, Afs proj) {
            this.deletedPairs = deletedPairs;
            this.proj = proj;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            result.append("The following dependency pairs are removed by the subterm processor:");
            result.append(o.linebreak());
            result.append(o.set(this.deletedPairs, Export_Util.RULES));
            result.append(o.linebreak());
            result.append("Simple projection used:");
            result.append(o.linebreak());
            String[] tmp = this.proj.export(o).split("\n");
            Set<String> tmps = new LinkedHashSet<String>();
            for (int i = 0; i < tmp.length; i++) {
                if (!tmp[i].equals("")) {
                    tmps.add(tmp[i]);
                }
            }
            result.append(o.set(tmps, Export_Util.RULES));
            return result.toString();
        }

    }

}
