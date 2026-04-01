package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/*
 * Rule5 Induction
 */
public class InfRule5Induction extends InfRuleSelectCondition {
    int i = 0;

    @Override
    public InfRuleID getID() {
        return InfRuleID.V;
    }

    @Override
    public String getLongName() {
        return "Rule V: Induction";
    }

    @Override
    public String getName() {
        return "Rule V";
    }

    public int getAppliedInductions() {
        return this.i;
    }

    @Override
    public Pair<Constraint, InfProofStepInfo> processSelection(
        final Implication implication,
        final ReducesTo reducesTo,
        final Set<Constraint> phiBase,
        final List<TRSVariable> vars,
        final Set<ReducesTo> preSel)
    {
        //System.out.println("Induction on: "+reducesTo+" | "+reducesTo.getCount());
        this.irc.setMark(reducesTo);
        Count count = reducesTo.getCount();
        if (count.induction >= this.irc.getInductionCount()) {
            return null;
        }
        final FunctionSymbol f = reducesTo.getLeftRootSymbol();
        final TRSTerm q = reducesTo.getRight();
        count = count.incInduction();
        final Object inductionId = "ID" + (this.i++);
        final Set<Constraint> ncs = new LinkedHashSet<Constraint>();

        final ConstraintSet phi = ConstraintSet.flatCreate(phiBase);
        final Constraint psi = implication.getConclusion();
        final InfRule5InductionProof indInfo = new InfRule5InductionProof(reducesTo, phi);
        for (GeneralizedRule rule : (Set<? extends GeneralizedRule>) this.irc.getRulesFor(f)) {
            rule = this.freshVariablesForRule(rule);
            final TRSTerm r = rule.getRight();
            final TRSSubstitution sigma = InfRule5Induction.createByZip(vars, rule.getLeft().getArguments().iterator());
            final TRSTerm q_sigma = q.applySubstitution(sigma);
            final ReducesTo r_to_q_sigma = ReducesTo.create(r, q_sigma, reducesTo.getParentFunc(), count, inductionId);
            final Constraint psi_sigma = (Constraint) psi.applySubstitution(sigma, this.irc.isIdpMode());
            if (r.isVariable() && !this.irc.isNormal(q)) {
                continue;
            }
            if (!r.isVariable() && !q_sigma.isVariable()) {
                final TRSFunctionApplication fr = (TRSFunctionApplication) r;
                final FunctionSymbol frf = fr.getRootSymbol();
                if (!this.irc.isDefinedSymbol(frf)) {
                    final TRSFunctionApplication fq = (TRSFunctionApplication) q_sigma;
                    if (!frf.equals(fq.getRootSymbol())) {
                        // apply rule I
                        final Implication imp =
                            Implication.create(
                                implication.quantor,
                                ConstraintSet.flatCreate(r_to_q_sigma),
                                psi_sigma,
                                implication.getData());
                        indInfo.addIH(rule, imp, null, r_to_q_sigma);
                        continue;
                    }
                }
            }
            final Constraint phi_sigma = (Constraint) phi.applySubstitution(sigma, this.irc.isIdpMode());
            final Pair<Constraint, List<Pair<TRSTerm, List<TRSVariable>>>> phiQuotesEntries =
                InfRule5Induction.createPhiQuotes(this.irc, inductionId, vars, f, r, q, phi, psi, count, implication);
            final Constraint phiQuotes = phiQuotesEntries.x;
            // (r -> q*sigma && phi*sigma && phi' => psi*sigma
            final Implication imp =
                Implication.create(
                    implication.quantor,
                    ConstraintSet.flatCreate(r_to_q_sigma, phi_sigma, phiQuotes),
                    psi_sigma,
                    implication.getData());
            indInfo.addIH(rule, imp, phiQuotesEntries.y, null);
            ncs.add(imp);
        }
        final Constraint res = ConstraintSet.flatCreate(ncs);
        return new Pair<Constraint, InfProofStepInfo>(res, indInfo);
    }

    @SuppressWarnings("unchecked")
    private static Pair<Constraint, List<Pair<TRSTerm, List<TRSVariable>>>> createPhiQuotes(
        InfRuleContext irc,
        Object inductionId,
        List<TRSVariable> vars,
        FunctionSymbol f,
        TRSTerm r,
        TRSTerm q,
        Constraint phi,
        Constraint psi,
        Count count,
        Implication origImplication
    ) {
        final Set<TRSVariable> rVars = r.getVariables();
        final List<Pair<TRSTerm, List<TRSVariable>>> subtermEntries = new ArrayList<>();
        final Set<Constraint> phiQuotesBase = new LinkedHashSet<Constraint>();
        for (final TRSTerm sr : r.getSubTerms()) {
            if (!sr.isVariable()) {
                final TRSFunctionApplication f_r1_rn = (TRSFunctionApplication) sr;
                if (f_r1_rn.getRootSymbol().equals(f)) { // subterm f(r1,...,rn) found
                    final Set<FunctionSymbol> fs = f_r1_rn.getFunctionSymbols();
                    final Iterator<FunctionSymbol> fsi = fs.iterator();
                    while (fsi.hasNext()) {
                        if (!irc.isDefinedSymbol(fsi.next())) {
                            fsi.remove();
                        }
                    }
                    if (fs.size() == 1) { // with no definied symbols
                        final TRSSubstitution my =
                            InfRule5Induction.createByZip(vars, f_r1_rn.getArguments().iterator());
                        final TRSTerm q_my = q.applySubstitution(my);
                        final ReducesTo f_r1_rn_to_q_my = ReducesTo.create(f_r1_rn, q_my, null, count, inductionId);
                        final Constraint phi_my = (Constraint) phi.applySubstitution(my, irc.isIdpMode());
                        final Constraint psi_my = (Constraint) psi.applySubstitution(my, irc.isIdpMode());
                        final Set<TRSVariable> ys = f_r1_rn_to_q_my.getVariables();
                        ys.addAll((Set<TRSVariable>)phi_my.getVariables());
                        ys.addAll((Set<TRSVariable>)psi_my.getVariables());
                        ys.removeAll(rVars);
                        final TRSSubstitution subs = irc.getFreshRenamingFor(ys);
                        final RenamingVisitor renamingVisitor = new RenamingVisitor(subs);
                        // (f(r1,..,rn) -> qµ && phi*µ => psi*µ

                        final ConstraintSet cs =
                            renamingVisitor.applyTo(ConstraintSet.flatCreate(f_r1_rn_to_q_my, phi_my));
                        final Constraint c = renamingVisitor.applyTo(psi_my);
                        final List<TRSVariable> yss = new ArrayList<>(ys.size());
                        for (final TRSVariable y : ys) {
                            yss.add(y);
                        }
                        subtermEntries.add(new Pair<>(sr, yss));
                        phiQuotesBase.add(Implication.create(
                            inductionId,
                            ImmutableCreator.create(subs.getVariablesInCodomain()),
                            cs,
                            c,
                            origImplication.getData()));
                    }
                }
            }
        }
        return new Pair<Constraint, List<Pair<TRSTerm, List<TRSVariable>>>>(
            ConstraintSet.flatCreate(phiQuotesBase),
            subtermEntries);
    }

    private GeneralizedRule freshVariablesForRule(final GeneralizedRule rule) {
        final Substitution subs = new FreshRenaming(this.irc);
        return GeneralizedRule.create(rule.getLeft().applySubstitution(subs), rule.getRight().applySubstitution(subs));
    }

    private static TRSSubstitution createByZip(final List<TRSVariable> vars, final Iterator<? extends TRSTerm> ita) {
        final Map<TRSVariable, TRSTerm> map = new LinkedHashMap<TRSVariable, TRSTerm>();
        for (final TRSVariable var : vars) {
            map.put(var, ita.next());
        }
        return TRSSubstitution.create(ImmutableCreator.create(map));
    }
}
