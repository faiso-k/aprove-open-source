package aprove.verification.oldframework.Unification;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/**
 *  A horribly crude approximating unification algorithm.
 *  <br>
 *  Given an algorithm for general unification and a set of alien
 *  function symbols, any alien terms are replaced by fresh variables
 *  and the resulting terms are given to the general unification algorithm.
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class CrudeApproxUnification extends GeneralUnification {

    private GeneralUnification unif;
    private Set<SyntacticFunctionSymbol> aliens;
    private Set<SyntacticFunctionSymbol> frees;
    private Map theoryIndices;

    public CrudeApproxUnification(GeneralUnification unif, Set<SyntacticFunctionSymbol> frees, Set<SyntacticFunctionSymbol> aliens, Map theoryIndices) {
    super();
    this.unif = unif;
    this.frees = frees;
    this.aliens = aliens;
    this.theoryIndices = theoryIndices;
    }

    public GeneralUnification getUnif() {
    return this.unif;
    }

    public Set<SyntacticFunctionSymbol> getAliens() {
    return this.aliens;
    }

    /** Return <code>null</code> if either <code>s</code> or <code>t</code>
     * contains an alien, otherwise the <code>unify</code>-method of the
     * given general unification algorithm is called.
     */
    @Override
    public Collection<AlgebraSubstitution> unify(AlgebraTerm s, AlgebraTerm t, Set<AlgebraVariable> W) {
    Set<SyntacticFunctionSymbol> funs = s.getFunctionSymbols();
    funs.addAll(t.getFunctionSymbols());
    funs.retainAll(this.aliens);
    if(!funs.isEmpty()) {
        /* we can't handle this */
        return null;
    }
    return this.unif.unify(s, t, W);
    }

    /** Crudly approximates whether <code>s</code> and <code>t</code> are unifiable.
     */
    @Override
    public boolean areTheoryUnifiable(AlgebraTerm s, AlgebraTerm t) {
    Set<AlgebraVariable> used = s.getVars();
    used.addAll(t.getVars());
    FreshVarGenerator fvg = new FreshVarGenerator(used);
    AlgebraTerm su = this.transform(s, fvg);
    AlgebraTerm tu = this.transform(t, fvg);
    boolean res = this.unif.areTheoryUnifiable(su, tu);
    if(res) {
        res = this.checkSyntacticPart(s, t);
    }
    return res;
    }

    private AlgebraTerm transform(AlgebraTerm r, FreshVarGenerator gen) {
       if(r.isVariable()) {
       return r;
       }
       else {
       SyntacticFunctionSymbol symb = (SyntacticFunctionSymbol)r.getSymbol();
       if(this.aliens.contains(symb)) {
           return gen.getFreshVariable("yo", symb.getSort(), false);
       }
       else {
           Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
               for(int i=0; i < symb.getArity(); i++) {
                   AlgebraTerm sub = r.getArgument(i);
                   args.addElement(this.transform(sub, gen));
           }
               return AlgebraFunctionApplication.create(symb, args);
       }
       }
    }

    private boolean checkSyntacticPart(AlgebraTerm s, AlgebraTerm t) {
    if(s.isVariable() || t.isVariable()) {
        return true;
    }
    SyntacticFunctionSymbol sSymb = (SyntacticFunctionSymbol)s.getSymbol();
    SyntacticFunctionSymbol tSymb = (SyntacticFunctionSymbol)t.getSymbol();
    boolean sAlien = this.aliens.contains(sSymb);
    boolean tAlien = this.aliens.contains(tSymb);
    boolean sFree = this.frees.contains(sSymb);
    boolean tFree = this.frees.contains(tSymb);
    if(sAlien != tAlien) {
        // Alien and Non-Alien don't mix
        return false;
    }
    if(sAlien && tAlien) {
        // two aliens ==> give it up, man!
        return this.theoryIndices.get(sSymb).equals(this.theoryIndices.get(tSymb));
    }
    // two non-free or syntactic symbols
    boolean res = sSymb.equals(tSymb);
    if(res && sFree && tFree) {
        /* check arguments */
        Iterator i = s.getArguments().iterator();
        Iterator j = t.getArguments().iterator();
        while(res && i.hasNext()) {
            res = this.checkSyntacticPart((AlgebraTerm)i.next(), (AlgebraTerm)j.next());
        }
    }
    return res;
    }

}
