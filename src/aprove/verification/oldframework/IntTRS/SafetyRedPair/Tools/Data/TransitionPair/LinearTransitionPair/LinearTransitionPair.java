package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.LinearTransitionPair;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.LinearRelation.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.TermTransitionPair.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class LinearTransitionPair extends Pair<LinearConstraintsSystem, PolyRelation> implements Exportable {

    public static LinearTransitionPair EMPTY =
        new LinearTransitionPair(LinearConstraintsSystem.LIN_TRUE, PolyRelation.create());

    private static FreshNameGenerator ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);

    public static LinearTransitionPair compose(final List<LinearTransitionPair> pairs) {
        final PolyRelation r = PolyRelation.create();
        final LinearConstraintsSystem c = LinearConstraintsSystem.LIN_TRUE;
        LinearTransitionPair p = new LinearTransitionPair(c, r);
        for (final LinearTransitionPair pair : pairs) {
            p = p.compose(pair);
        }
        return p;
    }

    public LinearTransitionPair(final LinearConstraintsSystem key) {
        super(key, null);
        final List<Pair<String, SimplePolynomial>> map = new ArrayList<>();
        for (final String var : key.getVariables()) {
            map.add(new Pair<>(var, SimplePolynomial.create(var)));
        }
        this.y = PolyRelation.createRelation(map);
    }

    public LinearTransitionPair(final LinearConstraintsSystem key, final PolyRelation value) {
        super(key, value);
        this.renameNondet();
    }

    public LinearTransitionPair(LinearConstraintsSystem key, PolyRelation value, boolean keepNdt) {
        super(key, value);
        if (!keepNdt) {
            this.renameNondet();
        }
    }

    public LinearTransitionPair addSuffix(final String suffix) {
        if (suffix.isEmpty()) {
            return this;
        }
        final Map<String, String> renameMap = new HashMap<>();
        for (final String var : this.getValue().getVariablesNames()) {
            renameMap.put(var, var + suffix);
        }
        for (final String var : this.x.getVariables()) {
            renameMap.put(var, var + suffix);
        }
        final PolyRelation r = this.y.rename(renameMap);
        final LinearConstraintsSystem c = LinearConstraintsSystem.create(this.x.rename(renameMap));
        return new LinearTransitionPair(c, r);
    }

    public LinearTransitionPair compose(final LinearTransitionPair pair) {
        final LinearTransitionPair p = new LinearTransitionPair(pair.x, pair.y); // make sure the ndt vars are diff
        final LinearConstraintsSystem c = this.x.merge(this.y.apply(p.x));
        final PolyRelation r = PolyRelation.compose(this.y, p.y);
        return new LinearTransitionPair(c, r);
    }

    public IGeneralizedRule createRule(FunctionSymbol lfSym, FunctionSymbol rfSym, TRSSubstitution sigma) {
        final FreshNameGenerator ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        ng.lockNames(this.x.getVariables());
        ng.lockNames(this.y.getVariablesNames());
        ng.lockNames(this.y.getReferedVariableNames());
        ArrayList<TRSTerm> argl = new ArrayList<>(lfSym.getArity());
        ArrayList<TRSTerm> argr = new ArrayList<>(rfSym.getArity());
        for (final Pair<String, TRSTerm> pair : this.y.toTermRelation(sigma).getTransitions()) {
            argl.add(TRSTerm.createVariable(pair.x));
            argr.add(pair.y == null ? TRSTerm.createVariable(ng.getFreshName("u", false)) : pair.y);
        }
        argl = new ArrayList<>(argl.subList(0, lfSym.getArity()));
        argr = new ArrayList<>(argr.subList(0, rfSym.getArity()));
        final TRSFunctionApplication l = TRSTerm.createFunctionApplication(lfSym, argl).applySubstitution(sigma);
        final TRSTerm r = TRSTerm.createFunctionApplication(rfSym, argr).applySubstitution(sigma);
        return IGeneralizedRule.create(l, r, this.x.toTerm().applySubstitution(sigma));
    }

    @Override
    public String export(Export_Util eu) {
        return "(" + eu.export(this.x) + ", " + eu.export(this.y) + ")";
    }

    public void extandUndefined(final Map<String, Pair<TRSFunctionApplication, List<String>>> varsToFApp) {
        final List<Pair<String, PolyNextValue>> pairs = new ArrayList<>();
        pairs.addAll(this.y.getTransVector());
        final Set<String> changedVars = new HashSet<>();
        final Stack<String> addChanged = new Stack<>();
        this.y.trim().getVariablesNames();
        while (!addChanged.isEmpty()) {
            changedVars.addAll(addChanged);
            for (final String var : addChanged) {
                if (varsToFApp.containsKey(var)) {
                    changedVars.addAll(varsToFApp.get(var).y);
                }
            }
            addChanged.removeAll(changedVars);
        }
        for (final Entry<String, Pair<TRSFunctionApplication, List<String>>> entry : varsToFApp.entrySet()) {
            if (changedVars.contains(entry.getKey())) {
                pairs.add(new Pair<>(entry.getKey(), new PolyNextValue(null)));
            } else {
                pairs.add(new Pair<>(entry.getKey(), new PolyNextValue(SimplePolynomial.create(entry.getKey()))));
            }
        }
        this.y = PolyRelation.create(pairs);
    }

    @Override
    public String toString() {
        return new Pair<>(this.x, this.y.getTrimTrans()).toString();
    }

    public TermTransitionPair toTermTransitionPair(final TRSSubstitution sigma) {
        return new TermTransitionPair(this.x.toTerm().applySubstitution(sigma), this.y.toTermRelation(sigma));
    }

    private void renameNondet() {
        final Set<String> ndtVars = new HashSet<>();
        ndtVars.addAll(this.x.getVariables());
        ndtVars.addAll(this.y.getReferedVariableNames());
        ndtVars.removeAll(this.y.getVariablesNames());
        final Map<String, String> ndtNames = new HashMap<>();
        for (final String v : ndtVars) {
            ndtNames.put(v, LinearTransitionPair.ng.getFreshName("ndt", false));
        }
        this.x = LinearConstraintsSystem.create(this.x.rename(ndtNames));
        this.y = this.y.rename(ndtNames);
    }

}
