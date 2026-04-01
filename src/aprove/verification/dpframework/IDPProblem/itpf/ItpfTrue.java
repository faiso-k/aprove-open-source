/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.itpf;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class ItpfTrue extends ItpfAtom {

    public static final ItpfTrue TRUE = new ItpfTrue();

    private ItpfTrue() {
        super();
    }


    @Override
    public boolean isTrue () {
        return true;
    }

    @Override
    protected Itpf applySubstitutionNoCheck(TRSSubstitution sigma) {
        return this;
    }

    @Override
    protected void collectFreeVariables(Set<TRSVariable> variables) {
    }

    @Override
    protected Itpf doNormalization(boolean neg) {
        if (neg) {
            return ItpfFalse.FALSE;
        }
        return this;
    }

    @Override
    protected List<List<Itpf>> doDnf(boolean neg, LinkedList<Pair<TRSVariable, Boolean>> quantors, FreshNameGenerator boundRenaming) {
        if (neg) {
            return new ArrayList<List<Itpf>>();
        } else {
            ArrayList<Itpf> inner = new ArrayList<Itpf>(0);
            List<List<Itpf>> outer = new ArrayList<List<Itpf>>(1);
            outer.add(inner);
            return outer;
        }
    }

    @Override
    public Itpf visit(IItpfVisitor visitor) {
        return visitor.fcaseTrue(this) ? visitor.caseTrue(this) : this;
    }

    @Override
    public String export(Export_Util o) {
        return this.export(o, null, VerbosityLevel.MIDDLE);
    }

    @Override
    public String export(Export_Util o, IDPPredefinedMap predefinedMap, VerbosityLevel verbosityLevel) {
        return "true";
    }


    @Override
    protected void collectFunctionSymbols(Set<FunctionSymbol> variables) {
        // TODO Auto-generated method stub

    }




}
