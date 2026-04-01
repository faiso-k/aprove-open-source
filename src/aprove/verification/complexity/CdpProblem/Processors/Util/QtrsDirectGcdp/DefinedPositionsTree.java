/**
 *
 */
package aprove.verification.complexity.CdpProblem.Processors.Util.QtrsDirectGcdp;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

public class DefinedPositionsTree {
    public final Position p;
    public final TRSFunctionApplication t;
    public final ImmutableArrayList<DefinedPositionsTree> sub;
    public OrderPoly<BigIntImmutable> pairPosVar;

    public static DefinedPositionsTree create(TRSTerm t, Set<FunctionSymbol> defined) {
        return DefinedPositionsTree.computeDefinedPositionsTree(t, defined);
    }

    private DefinedPositionsTree(TRSFunctionApplication t, Position p,
            ImmutableArrayList<DefinedPositionsTree> sub) {
        this.p = p;
        this.t = t;
        this.sub = sub;
    }

    private static DefinedPositionsTree computeDefinedPositionsTree(TRSTerm t, Set<FunctionSymbol> defined) {
        ArrayList<DefinedPositionsTree> subtrees = new ArrayList<DefinedPositionsTree>();
        DefinedPositionsTree.addDefinedPositionTrees(subtrees, t, Position.create(), defined);
        ImmutableArrayList<DefinedPositionsTree> imSubtrees =
            ImmutableCreator.create(subtrees);
//        if (t instanceof FunctionApplication
//                && defined.contains(((FunctionApplication)t).getRootSymbol())) {
//            return new DefinedPositionsTree((FunctionApplication)t, Position.create(), imSubtrees);
//        } else {
            return new DefinedPositionsTree(null, null, imSubtrees);
//        }
    }

    private static void addDefinedPositionTrees(
            ArrayList<DefinedPositionsTree> subtrees, TRSTerm t, Position p,
            Set<FunctionSymbol> defined) {
        if (t instanceof TRSVariable) {
            return;
        }
        TRSFunctionApplication fa = (TRSFunctionApplication)t;
        ArrayList<DefinedPositionsTree> ourSubtrees =
            new ArrayList<DefinedPositionsTree>();

        int argc = fa.getArguments().size();
        for (int i=0; i < argc; i++) {
            TRSTerm subt = fa.getArgument(i);
            DefinedPositionsTree.addDefinedPositionTrees(ourSubtrees, subt, p.append(i), defined);
        }
        if (defined.contains(fa.getRootSymbol())) {
            ImmutableArrayList<DefinedPositionsTree> imOurSubtrees =
                ImmutableCreator.create(ourSubtrees);
            subtrees.add(new DefinedPositionsTree(fa, p, imOurSubtrees));
        } else {
            subtrees.addAll(ourSubtrees);
        }
    }


}