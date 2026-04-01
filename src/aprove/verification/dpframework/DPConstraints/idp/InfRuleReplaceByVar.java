/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class InfRuleReplaceByVar extends InfRuleConstraintRepl<InfRuleReplaceByVar.FreshNameContainer> {

    public InfRuleReplaceByVar(Mode mode) {
        super(mode);
    }

    @Override
    protected Constraint processConstraint(
        Implication origImplication,
        Constraint constraint,
        boolean isConclusion,
        FreshNameContainer data,
        Abortion aborter) throws AbortionException
    {

        if (constraint.isReducesTo()) {
            ReducesTo reducesTo = (ReducesTo) constraint;
            IDPNonInfInterpretation interpretation = (IDPNonInfInterpretation) this.getIrc().getPolyInterpretation();
            if (!interpretation.isNat() && !reducesTo.getLeft().isVariable()) {
                TRSFunctionApplication reduceLeft = ((TRSFunctionApplication) reducesTo.getLeft());
                FunctionSymbol reduceLeftRoot = reduceLeft.getRootSymbol();
                IDPPredefinedMap predefinedMap =
                    ((IdpInductionCalculus) this.irc).getIdp().getRuleAnalysis().getPreDefinedMap();
                PredefinedFunction func = predefinedMap.getPredefinedFunction(reduceLeftRoot);
                if (func == null && reducesTo.getParentFunc() != null && reducesTo.getParentFunc().isFunction()) {
                    func = (PredefinedFunction) reducesTo.getParentFunc();
                }
                if (func != null && (func.isRelation() || func.isArithmetic())) {
                    IdpInductionCalculus ic = (IdpInductionCalculus) this.irc;
                    Set<Pair<Position, TRSTerm>> topmostUserDefined = new LinkedHashSet<Pair<Position, TRSTerm>>();
                    Collection<Pair<Position, TRSTerm>> subTerms = reduceLeft.getPositionsWithSubTerms();
                    for (Pair<Position, TRSTerm> subTerm : subTerms) {
                        if (subTerm.y.isVariable()) {
                            continue;
                        } else {
                            TRSFunctionApplication fa = (TRSFunctionApplication) subTerm.y;
                            if (predefinedMap.isPredefined(fa.getRootSymbol())
                                && !predefinedMap.isUndefinedInt(fa.getRootSymbol()))
                            {
                                continue;
                            }
                        }
                        Iterator<Pair<Position, TRSTerm>> topmostIter = topmostUserDefined.iterator();
                        boolean isTopmost = true;
                        while (topmostIter.hasNext()) {
                            Pair<Position, TRSTerm> top = topmostIter.next();
                            if (top.x.isPrefixOf(subTerm.x)) {
                                isTopmost = false;
                                break;
                            } else if (subTerm.x.isPrefixOf(top.x)) {
                                topmostIter.remove();
                            }
                        }
                        if (isTopmost) {
                            topmostUserDefined.add(subTerm);
                        }
                    }
                    Iterator<Pair<Position, TRSTerm>> tud = topmostUserDefined.iterator();
                    while (tud.hasNext()) {
                        Pair<Position, TRSTerm> ud = tud.next();
                        if (!predefinedMap.isUndefinedInt(((TRSFunctionApplication) ud.y).getRootSymbol())
                            && ic.evaluatesToConstantInt(ud.y, aborter))
                        {
                            ud.y =
                                TRSTerm.createFunctionApplication(PredefinedSemanticsFactory
                                    .getUndefinedInt(((IntFunction) func).getDomains().get(0))
                                    .getSym(), ud.y);
                        } else {
                            tud.remove();
                        }
                    }
                    if (topmostUserDefined.isEmpty()) {
                        return constraint;
                    }
                    TRSTerm resLeft = reduceLeft;
                    for (Pair<Position, TRSTerm> replace : topmostUserDefined) {
                        resLeft = reduceLeft.replaceAt(replace.x, replace.y);
                    }
                    return ReducesTo.create(
                        resLeft,
                        reducesTo.getRight(),
                        reducesTo.getParentFunc(),
                        reducesTo.getCount(),
                        reducesTo.getId());
                }
            }
        }
        return constraint;
    }

    @Override
    public InfRuleID getID() {
        return InfRuleID.IDP_REPLACE_BYVAR;
    }

    @Override
    public String getLongName() {
        return "IDP_REPLACE_BYVAR: replaces arguments of an RelOp by a fresh variable whenever they consist of a user-defined symbol and usable rules are locally confluent.";
    }

    @Override
    public String getName() {
        return "IDP_REPLACE_BYVAR";
    }

    @Override
    protected FreshNameContainer prepare(Implication implication, Abortion aborter) {
        return new FreshNameContainer();
    }

    protected static class FreshNameContainer {
        public FreshNameGenerator freshNames;
    }

}
