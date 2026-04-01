package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.idp.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;

/**
 * this abstract InfRule expands a left-hand side of an ReducesTo which must be a
 * function application fal to new ReducesTos were each non-variable parameter of
 * fal reduces to a fresh variable and these parameters in fal are replaced by
 * these fresh variables formal:
 *
 *    f(p1,..,pn) = t  is expanded to
 *
 *    a1 = x1 & .. & an = xn & f(b1,..,bn) = t
 *
 *    {a1 ... an} := {p1,...,pn} \ Variables
 *
 *    bi = pi if pi is a variable,
 *    bi = xj otherwise where xj is the fresh variable for bi
 *
 * If createSubs returns true and t is a variable the substitution [t/f(b1,..,bn)]
 * is applied to the new implication
 *
 * The abstract method actionForReducesTo decieds to which ReducesTo the expansion should be applied
 * (this should guaranty that the selected reducesTo should have a function apllication on the left-hand side)
 *
 * The abstract method expandCount should calculates the new Count for the ReducesTo in the expansion
 *
 * @author swiste
 */
public abstract class InfRuleExpandLeft extends InfRuleReducesToReplace {

    @Override
    public TRSSubstitution expandReducesTo(
        final ReducesTo reducesTo,
        final Set<Constraint> ncs,
        final Map<Integer, TRSVariable> newVars,
        final Implication implication,
        final Abortion aborter) throws AbortionException
    {
        final Count count = this.expandCount(reducesTo);
        final TRSFunctionApplication fal = (TRSFunctionApplication) reducesTo.getLeft();
        final List<? extends TRSTerm> args = fal.getArguments();
        final List<TRSTerm> newArgs = new LinkedList<TRSTerm>();
        final Iterator<? extends TRSTerm> ita = args.iterator();
        PredefinedFunction<? extends Domain> idpParentFunc = null;
        if (this.irc.isIdpMode()) {
            final IDPPredefinedMap predefinedMap =
                ((IdpInductionCalculus) this.irc).getIdp().getRuleAnalysis().getPreDefinedMap();
            if (predefinedMap.isPredefined(fal.getRootSymbol())) {
                idpParentFunc = predefinedMap.getPredefinedFunction(fal.getRootSymbol());
            }
        }
        int i = 0;
        while (ita.hasNext()) {
            final TRSTerm arg = ita.next();
            if (arg.isVariable() && !newArgs.contains(arg)) {
                newArgs.add(arg);
            } else {
                if (this.irc.isIdpMode()) {
                    final IDPPredefinedMap predefinedMap =
                        ((IdpInductionCalculus) this.irc).getIdp().getRuleAnalysis().getPreDefinedMap();
                    if (predefinedMap.isPredefined(fal.getRootSymbol())) {
                        if (arg.isVariable() || predefinedMap.isPredefined(((TRSFunctionApplication) arg).getRootSymbol()))
                        {
                            newArgs.add(arg);
                            continue;
                        }
                    }
                }
                final TRSVariable v = this.irc.getFreshVariable();
                newArgs.add(v);
                newVars.put(i, v);
                ncs.add(ReducesTo.create(arg, v, idpParentFunc, count, reducesTo.getId()));
            }
            i++;
        }
        final TRSTerm fx1_xn = TRSTerm.createFunctionApplication(fal.getRootSymbol(), newArgs.toArray(new TRSTerm[] {}));
        if (this.createSubs()) {
            final TRSVariable x = (TRSVariable) reducesTo.getRight();
            return TRSSubstitution.create(x, fx1_xn);
        } else {
            if (!newArgs.equals(args)) {
                ncs.add(ReducesTo.create(
                    fx1_xn,
                    reducesTo.getRight(),
                    reducesTo.getParentFunc(),
                    reducesTo.getCount(),
                    reducesTo.getId()));
            } else {
                ncs.add(reducesTo);
            }
            return null;
        }
    }

    public abstract boolean createSubs();

    public abstract Count expandCount(ReducesTo reducesTo);

}
