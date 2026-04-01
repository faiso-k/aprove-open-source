package aprove.verification.dpframework.TRSProblem.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * this class represents what is called an "Ausschlusssubstitution" in my Diploma Thesis;
 * in substance there is simply a Substitution of a special kind captured
 *
 * @author Sebastian Weise
 */

public class ExclusionSubstitution implements Immutable {

    private final TRSSubstitution theSubstitution;
    /*
     * an upper bound for the maximal Index of allquantified Variables;
     * >= Term.STANDARD_NUMBER - 1 if there are no allquantified Variables
     */
    private final int maxIndex;
    private final OTRSTermGraphUtils util;

    // to avoid multiple computations
    private ImmutableSet<TRSVariable> freeVariables;
    private ImmutableSet<TRSVariable> boundVariables;

    public ExclusionSubstitution(final TRSSubstitution substitution,
            final int maxIndex, final OTRSTermGraphUtils util) {
        this.theSubstitution = substitution;
        this.maxIndex = maxIndex;
        this.util = util;
    }

    public TRSSubstitution getSubstitution() {
        return this.theSubstitution;
    }

    @Override
    public boolean equals(final Object obj) {
        if (obj == this) {
            return true;
        }
        if (!(obj instanceof ExclusionSubstitution)) {
            return false;
        }
        final ExclusionSubstitution objSubstExcl = (ExclusionSubstitution) obj;
        final TRSSubstitution objSubst = objSubstExcl.getSubstitution();
        if (!(this.theSubstitution.getDomain().equals(objSubst.getDomain()))) {
            return false;
        }
        final FunctionSymbol f =
            FunctionSymbol.create("f", this.theSubstitution.getDomain().size());
        final ArrayList<TRSTerm> argsThis = new ArrayList<TRSTerm>(f.getArity());
        final ArrayList<TRSTerm> argsObj = new ArrayList<TRSTerm>(f.getArity());
        for (TRSVariable actVar : this.theSubstitution.getDomain()) {
            argsThis.add(this.theSubstitution.substitute(actVar));
            argsObj.add(objSubst.substitute(actVar));
        }
        final TRSFunctionApplication termThis = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(argsThis));
        final TRSFunctionApplication termObj = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(argsObj));
        final TRSSubstitution matcher = termThis.getMatcher(termObj);
        if (matcher == null) {
            return false;
        }
        return this.util.isVariableRenaming(matcher, this.getBoundVariables(),
            objSubstExcl.getBoundVariables());
    }

    @Override
    public int hashCode() {
        return 0;
    }

    @Override
    public String toString() {
        return this.theSubstitution.toString();
    }

    /**************************************************************************/
    /**************************************************************************/

    public ImmutableSet<TRSVariable> getFreeVariables() {
        if (this.freeVariables == null) {
            this.buildFreeAndBoundVariables();
        }
        return this.freeVariables;
    }

    public ImmutableSet<TRSVariable> getBoundVariables() {
        if (this.boundVariables == null) {
            this.buildFreeAndBoundVariables();
        }
        return this.boundVariables;
    }

    private void buildFreeAndBoundVariables() {
        final Set<TRSVariable> freeVariablesTemp =
            new LinkedHashSet<TRSVariable>();
        final Set<TRSVariable> boundVariablesTemp =
            new LinkedHashSet<TRSVariable>();
        for (final TRSVariable actVar : this.theSubstitution.getVariables()) {
            // in fact, actVar has to be EITHER a Metavariable OR an allquantified Variable
            if (this.util.isMetaVariable(actVar)) {
                freeVariablesTemp.add(actVar);
            }
            if (this.util.isAllqVariable(actVar)) {
                boundVariablesTemp.add(actVar);
            }
        }
        this.freeVariables = ImmutableCreator.create(freeVariablesTemp);
        this.boundVariables = ImmutableCreator.create(boundVariablesTemp);
    }

    /**************************************************************************/

    public ExclusionSubstitution minimize(final TRSTerm t) {
        final Set<TRSVariable> variablesT = t.getVariables();
        TRSSubstitution newSubst =
            this.theSubstitution.restrictTo(variablesT);
        final Set<TRSVariable> unusedMetaVars =
            new LinkedHashSet<TRSVariable>(
                this.util.getMetaVariables(newSubst.getVariablesInCodomain()));
        unusedMetaVars.removeAll(variablesT);
        final Map<TRSVariable, TRSVariable> map =
            new LinkedHashMap<TRSVariable, TRSVariable>();
        int index = this.maxIndex;
        for (final TRSVariable actUnusedMetaVar : unusedMetaVars) {
            index++;
            map.put(actUnusedMetaVar, this.util.getAllqVariable(index));
        }
        final TRSSubstitution substRename =
            TRSSubstitution.create(ImmutableCreator.create(map));
        newSubst = newSubst.compose(substRename).restrictTo(variablesT);
        final Map<TRSVariable, MyInteger> varToCount =
            new LinkedHashMap<TRSVariable, MyInteger>();
        for (final TRSTerm actValue : newSubst.toMap().values()) {
            for (final TRSVariable actAllqVar : this.util.getAllqVariables(actValue.getVariables())) {
                MyInteger actCount = varToCount.get(actAllqVar);
                if (actCount == null) {
                    actCount = new MyInteger(0);
                    varToCount.put(actAllqVar, actCount);
                }
                actCount.increase();
            }
        }
        final Map<TRSVariable, TRSTerm> resultMap =
            new LinkedHashMap<TRSVariable, TRSTerm>();
        for (final Map.Entry<TRSVariable, ? extends TRSTerm> actEntry : newSubst.toMap().entrySet()) {
            final TRSTerm actValue = actEntry.getValue();
            if (!(this.util.isAllqVariable(actValue) && varToCount.get(actValue).getIntValue() == 1)) {
                resultMap.put(actEntry.getKey(), actValue);
            }
        }
        return new ExclusionSubstitution(
            TRSSubstitution.create(ImmutableCreator.create(resultMap)), index,
            this.util);
    }

    /**
     * @param t a Pattern-Term
     * @param substIns an Instantiation-Substitution
     * @return the correspondingly modified ExclusionSubstitution or null if none exists
     */
    public ExclusionSubstitution modify(final TRSTerm t,
        final TRSSubstitution substIns) {
        final TRSTerm tSubstIns = t.applySubstitution(substIns);
        final TRSTerm tSubstExcl = t.applySubstitution(this.theSubstitution);
        TRSSubstitution matcherOrUnifier = tSubstIns.getMatcher(tSubstExcl);
        if (matcherOrUnifier == null) {
            matcherOrUnifier = new Unification(tSubstIns, tSubstExcl).getMgu();
        }
        if (matcherOrUnifier == null) {
            return null;
        }
        return new ExclusionSubstitution(
            this.util.restrictToVmeta(matcherOrUnifier), this.maxIndex,
            this.util).minimize(tSubstIns);
    }

    /**
     * @param varRenaming must be a Variable-Renaming on Metavariables!
     */
    public ExclusionSubstitution transform(final TRSSubstitution varRenaming) {
        return new ExclusionSubstitution(this.util.applyToDomainAndCodomain(
            this.theSubstitution, varRenaming), this.maxIndex,
            this.util);
    }
}