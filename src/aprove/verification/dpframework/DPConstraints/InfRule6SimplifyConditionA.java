package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.SolutionIterator.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/*
 * Rule6 SimplyfyCondition
 * replace    phi & (\/y1...yn.phi' ==> psi') ==> psi
 * with       phi & psi'*sigma ==> psi
 *
 * but only if       phi'*sigma <== phi
 *
 * for every A in phi' there exist a B in phi with A*sigma <== B
 * to As does not share the same B
 */
public class InfRule6SimplifyConditionA extends InfRule {
    public boolean multiSet = true;

    @Override
    public InfRuleID getID() {
        return InfRuleID.VI;
    }

    @Override
    public String getLongName() {
        return "Rule VIA: Simpliyfy Condition (multiset)";
    }

    @Override
    public String getName() {
        return "Rule VIA:";
    }

    @Override
    public Pair<Constraint, InfProofStepInfo> applyToImplication(Implication implication, final Abortion aborter)
        throws AbortionException
    {
        Implication imp = null;
        Implication ih = null;
        Solution sol = null;
        boolean change = false;
        final Set<Constraint> ncs = new LinkedHashSet<>();
        TRSSubstitution sigma = null;
        for (final Constraint c : implication.getConditions()) {
            if (!change && c.isImplication()) {
                imp = (Implication) c;
                final Set<Constraint> rcs = new LinkedHashSet<>(implication.getConditions());
                rcs.remove(imp);
                sol =
                    this.searchSubsetSubstitution(
                        implication,
                        imp,
                        imp.getQuantor(),
                        ConstraintSet.flatCreate(rcs),
                        imp.getConditions());
                if (sol != null) {
                    sigma = sol.getSubstitution();
                    ih = imp;
                    change = true;
                    final Constraint psi = imp.getConclusion();
                    Constraint psi_sigma = (Constraint) psi.applySubstitution(sigma, this.irc.isIdpMode());
                    final Map<TRSVariable, TRSTerm> map = new LinkedHashMap<>();
                    if (psi_sigma.collectMatchMap(implication.getConclusion(), map)) {
                        map.keySet().removeAll(sol.getUsedVariables());
                        map.keySet().retainAll(imp.getQuantor());
                        boolean allGround = true;
                        for (final TRSTerm t : map.values()) {
                            if (!this.irc.isGround(t)) {
                                allGround = false;
                            }
                        }
                        if (allGround) {
                            sigma = sigma.extend(TRSSubstitution.create(ImmutableCreator.create(map)));
                            psi_sigma = (Constraint) psi.applySubstitution(sigma, this.irc.isIdpMode());
                        }
                    }
                    ncs.add(psi_sigma);
                    this.irc.setMark(new CombinedExportable(imp, sigma));
                } else {
                    ncs.add(c);
                }
            } else {
                ncs.add(c);
            }
        }
        if (!change) {
            return null;
        } else {
            //System.out.println("Blocked: "+inductionId);
            final Set<Constraint> cs = new LinkedHashSet<Constraint>();
            /*Map<Object,Object> map = new HashMap<Object,Object>();*/
            final List<Object> idList = new LinkedList<Object>();
            new IdCollector(idList).applyTo(imp);
            /*for (Object id : idList){
                map.put(id,irc.getInductionBlockId());
            }
            for (Constraint c : ncs){
                cs.add((Constraint)c.replaceIdById(map));
            }*/
            cs.addAll(ncs);
            final Set<Object> topIdSet = sol.getTopIdSet();
            if (topIdSet != null) {
                cs.removeAll(topIdSet); // Remove all conditions used by the inductionhypothesis
            }
            implication =
                Implication.create(
                    implication.getQuantor(),
                    ConstraintSet.flatCreate(cs),
                    implication.getConclusion(),
                    implication.getData());
            final Constraint res = implication;
            final InfProofStepInfo info = new InfRule6SimplifyProof(ih, sigma, implication);
            return new Pair<>(res, info);
        }
    }

    public Solution searchSubsetSubstitution(
        final Implication imp,
        final Implication impi,
        final Set<TRSVariable> domain,
        final ConstraintSet phi,
        final ConstraintSet phiQuote)
    {
        final Solution sol = new Solution(domain);
        if (phi.size() > 7 && phiQuote.size() > 7) {
            return null;
        }
        final SolutionIterator soli =
            SolutionIterator.create(
                Direction.right,
                phi,
                phiQuote,
                new SolutionConstraints(this.irc.getConstructorNoHeadSymbols(), this.multiSet),
                null);
        do {
            if (soli.extendWithCurrent(sol)) {
                return sol;
            }
            sol.reset();
        } while (!soli.next());
        return null;

    }

    public static class CombinedExportable extends Pair<Exportable, Exportable> implements Exportable {
        public CombinedExportable(final Exportable key, final Exportable value) {
            super(key, value);
        }

        @Override
        public String export(final Export_Util o) {
            return this.getKey().export(o) + " with " + o.sigma() + " = " + this.getValue().export(o);
        }
    }

}
