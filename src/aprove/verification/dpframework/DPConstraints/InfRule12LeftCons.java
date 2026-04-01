package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * This InfRule expands ReducesTo in an implication if it has same constructors as root symbol,
 * if on left-hand side is a constructor as root symbol and the right-hand side root symbol is different
 * the ReducesTo is deleted.
 *
 * @author swiste
 */
public class InfRule12LeftCons extends InfRuleReducesToReplace {

    @Override
    public InfRuleID getID() {
        return InfRuleID.I_II;
    }

    @Override
    public String getName() {
        return "Rule I & II";
    }

    @Override
    public String getLongName() {
        return "Rule I & II: Constructor and Different Functionsymbol & Same Constructors on Both Sides";
    }

    @Override
    public TRSSubstitution expandReducesTo(
        final ReducesTo reducesTo,
        final Set<Constraint> ncs,
        final Map<Integer, TRSVariable> newVars,
        final Implication implication,
        final Abortion aborter) throws AbortionException
    {
        final TRSFunctionApplication fal = (TRSFunctionApplication) reducesTo.getLeft();
        final TRSFunctionApplication far = (TRSFunctionApplication) reducesTo.getRight();
        final Iterator<? extends TRSTerm> li = fal.getArguments().iterator();
        final Iterator<? extends TRSTerm> ri = far.getArguments().iterator();
        while (li.hasNext()) {
            ncs.add(ReducesTo.create(li.next(), ri.next(), null, reducesTo.getCount(), reducesTo.getId()));
        }
        return null;
    }

    @Override
    public Mode actionForReducesTo(final ReducesTo reducesTo, final Implication implication, final Abortion aborter) {
        if (reducesTo.notBlocked(this)) {
            final FunctionSymbol fl = reducesTo.getLeftRootSymbol();
            if ((fl != null) && !this.irc.isDefinedSymbol(fl)) {
                final FunctionSymbol fr = reducesTo.getRightRootSymbol();
                if (fr != null) {
                    this.irc.setMark(reducesTo);
                    if (fl.equals(fr)) {
                        return Mode.Expand;
                    } else {
                        return Mode.Erase;
                    }
                }
            }
            reducesTo.block(this);
        }
        return Mode.NoChange;
    }

}
