package aprove.verification.dpframework.TRSProblem.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

public abstract class Context implements Immutable, XMLObligationExportable, CPFAdditional {

    public static final Context BOX = Box.Instance;

    /**
     * creates a Context from a given Term and a given Position of that Term
     * where the "Box" has to be placed
     */
    public static Context create(final TRSTerm term, final Position position) {
        if (position.isEmptyPosition()) {
            return Context.BOX;
        } else {
            final TRSFunctionApplication funcApp = (TRSFunctionApplication) term;
            final List<TRSTerm> args = funcApp.getArguments();
            final int positionOfDirectSubcontext = position.firstIndex();
            final ArrayList<TRSTerm> beforeTemp = new ArrayList<TRSTerm>();
            for (int i = 0; i <= positionOfDirectSubcontext - 1; i++) {
                beforeTemp.add(args.get(i));
            }
            final ImmutableArrayList<TRSTerm> before =
                ImmutableCreator.create(beforeTemp);
            final Context directSubcontext =
                Context.create(args.get(positionOfDirectSubcontext),
                    position.tail(1));
            final ArrayList<TRSTerm> afterTemp = new ArrayList<TRSTerm>();
            for (int i = positionOfDirectSubcontext + 1; i < args.size(); i++) {
                afterTemp.add(args.get(i));
            }
            final ImmutableArrayList<TRSTerm> after = ImmutableCreator.create(afterTemp);
            return new NonEmptyContext(funcApp.getRootSymbol(), before,
                directSubcontext, after);
        }
    }

    public abstract boolean isEmptyContext();

    @Override
    public String toString() {
        return this.getAsTerm().toString();
    }

    /**
     * @return the Term that you get if you replace the "Box" in this Context by
     * a given Term t
     */
    public abstract TRSTerm replace(TRSTerm t);

    public abstract Position getPosition();

    public abstract Context getSubcontext(int depth);

    public Context getSubcontext(final Position pos) {
        final Position holePos = this.getPosition();
        if (!pos.isPrefixOf(holePos)) {
            throw new IllegalArgumentException();
        }
        return this.getSubcontext(pos.getDepth());
    }

    public abstract Context applySubstitution(TRSSubstitution subst);

    /**
     * This is broken, since the name of the box symbol in a context is not
     * fresh. Do not use. Instead write a version using a
     * {@link FreshNameGenerator}.
     * @return the Term that you get if you replace the "Box" of this Context by
     * a new FunctionApplication whose FunctionSymbol has the Name "[]" and the
     * Arity 0; consider that this FunctionApplication might theoretically
     * already occur in the Rest of the returned Term!
     */
    @Deprecated
    public TRSTerm getAsTerm() {
        return
            this.replace(
                TRSTerm.createFunctionApplication(
                    FunctionSymbol.create("[]", 0),
                    ImmutableCreator.create(new ArrayList<TRSTerm>())
                )
            );
    }

}
