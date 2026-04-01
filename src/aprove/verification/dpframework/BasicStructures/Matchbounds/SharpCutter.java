package aprove.verification.dpframework.BasicStructures.Matchbounds;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Cuts a Term at a specified depth and inserts a # function symbol at
 * that point
 *
 * @author <a href="mailto:chang@ariadne.informatik.rwth-aachen.de">Christian Hang</a>
 * @version 1.0
 */
public class SharpCutter {

    private static final TRSVariable x = TRSTerm.createVariable("x");

    private final FunctionSymbol sharpSymbol;
    private final TRSFunctionApplication sharpX;

    public SharpCutter(FunctionSymbol sharpSymbol) {
        if (Globals.useAssertions) {
            assert (sharpSymbol.getArity() == 1);
        }
        this.sharpSymbol = sharpSymbol;
        this.sharpX = TRSTerm.createFunctionApplication(sharpSymbol, new TRSTerm[]{SharpCutter.x});
    }


    /**
     * cuts the term term at the depth cutDepth
     * @param term
     * @param cutDepth
     * @return
     */
    public TRSFunctionApplication cut(TRSTerm term, int cutDepth) {
        // we do not cut variables!!

        TRSFunctionApplication fTerm = (TRSFunctionApplication) term;
        FunctionSymbol f = fTerm.getRootSymbol();
        int n = f.getArity();
        if (n == 0) {
            if (Globals.useAssertions) {
                assert(cutDepth == 0);
            }
            return this.sharpX;
        }
        if (Globals.useAssertions) {
            assert(n == 1);
        }
        TRSTerm arg = fTerm.getArgument(0);
        if (cutDepth == 0) {
            Set<TRSVariable> vars = arg.getVariables();
            if (vars.isEmpty()) {
                return this.sharpX;
            } else {
                return TRSTerm.createFunctionApplication(
                            this.sharpSymbol,
                            new TRSTerm[]{vars.iterator().next()}
                          );
            }
        } else {
            TRSTerm cutArg = this.cut(arg, cutDepth-1);
            return TRSTerm.createFunctionApplication(f, new TRSTerm[]{cutArg});
        }
    }

}
