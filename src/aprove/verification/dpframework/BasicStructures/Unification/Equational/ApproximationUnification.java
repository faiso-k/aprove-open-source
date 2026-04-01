package aprove.verification.dpframework.BasicStructures.Unification.Equational;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * A approximating unification algorithm.
 * Subterms with a root symbol of an equation are replaced by fresh variables
 * and the resulting terms are checked for syntactic unifiability.
 * Only works correctly if the equations do not change top symbols!
 * Also, E need to be collapse-free and regular!
 *
 * @author Stephan Falke
 * @version $Id$
 */

public class ApproximationUnification extends GeneralUnification {

    private Set<FunctionSymbol> aliens;

    public ApproximationUnification(Set<FunctionSymbol> aliens) {
        super();
        this.aliens = aliens;
    }

    /**
     * We cannot actualy compute unifers...
     */
    @Override
    public Collection<TRSSubstitution> unify(TRSTerm s, TRSTerm t, Set<TRSVariable> W) {
        return null;
    }

    /**
     * Approximates whether s and t are unifiable.
     */
    @Override
    public boolean areTheoryUnifiable(TRSTerm s, TRSTerm t) {
        if (!this.checkSyntacticPart(s, t)) {
            return false;
        }
        Set<TRSVariable> used = s.getVariables();
        used.addAll(t.getVariables());
        FreshVarGenerator fvg = new FreshVarGenerator(used);
        TRSTerm su = this.transform(s, fvg);
        TRSTerm tu = this.transform(t, fvg);
        return su.unifies(tu);
    }

    private TRSTerm transform(TRSTerm r, FreshVarGenerator gen) {
        if(r.isVariable()) {
            return r;
        } else {
            TRSFunctionApplication fr = (TRSFunctionApplication) r;
            FunctionSymbol symb = (FunctionSymbol) fr.getRootSymbol();
            if (this.aliens.contains(symb)) {
                return gen.getFreshVariable(TRSTerm.createVariable("yo"), false);
            } else {
                ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                for (int i=0; i < symb.getArity(); i++) {
                    TRSTerm sub = fr.getArgument(i);
                    args.add(this.transform(sub, gen));
                }
                return TRSTerm.createFunctionApplication(symb, ImmutableCreator.create(args));
            }
        }
    }

    private boolean checkSyntacticPart(TRSTerm s, TRSTerm t) {
        if(s.isVariable() || t.isVariable()) {
            return true;
        }
        TRSFunctionApplication sf = (TRSFunctionApplication) s;
        TRSFunctionApplication tf = (TRSFunctionApplication) t;
        FunctionSymbol sSymb = sf.getRootSymbol();
        FunctionSymbol tSymb = tf.getRootSymbol();
        boolean sAlien = this.aliens.contains(sSymb);
        boolean tAlien = this.aliens.contains(tSymb);
        if(sAlien != tAlien) {
            // alien and non-alien don't mix
            return false;
        }
        boolean res = sSymb.equals(tSymb);
        if(res && !sAlien && !tAlien) {
            // check arguments
            int arr = sSymb.getArity();
            for (int i = 0; res && i < arr; i++) {
                res = this.checkSyntacticPart(sf.getArgument(i), tf.getArgument(i));
            }
        }
        return res;
    }

}
