package aprove.verification.oldframework.Haskell;

import aprove.input.Generated.haskell.node.*;
import aprove.verification.oldframework.Haskell.Modules.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 * The HaskellSymFactory is a collection of methods used by the HaskellASTBuilder
 * which create various HaskellSyms of the Haskell Framework.
 *
 * Also the prelude is informed about all occuring names in a Haskell program.
 *
 * every object needed by a create methode has to offer non null token
 * cause the create methods expect an non null token.
 */
public class HaskellSymFactory {

    Prelude prelude;

    private HaskellSym op(HaskellSym sym){
        sym.setOperator(true);
        return sym;
    }

    public HaskellSymFactory(Modules modules){
        this.prelude = modules.getPrelude();
    }

    public HaskellSym createSym(Token tok){
        return (HaskellSym) (this.newHaskellNamedSym(tok.getText())).setToken(tok);
    }

    public HaskellSym createNameSym(Token tok,String name){
        return (HaskellSym) (this.newHaskellNamedSym(name)).setToken(tok);
    }

    public HaskellSym newHaskellNamedSym(String name){
        this.prelude.addUsedName(name);
        return new HaskellNamedSym(name);
    }

    public HaskellSym newHaskellNamedSym(String qual,String name){
        this.prelude.addUsedName(name);
        return new HaskellNamedSym(qual,name);
    }

    public HaskellSym newHaskellNamedSym(String qual,String name,HaskellEntity e){
        this.prelude.addUsedName(name);
        return new HaskellNamedSym(qual,name,e);
    }

    public HaskellSym enumFrom(Token tok){
        return (HaskellSym) (this.newHaskellNamedSym("Prelude","enumFrom")).setToken(tok);
    }

    public HaskellSym enumFromTo(Token tok){
        return (HaskellSym) (this.newHaskellNamedSym("Prelude","enumFromTo")).setToken(tok);
    }

    public HaskellSym enumFromThen(Token tok){
        return (HaskellSym) (this.newHaskellNamedSym("Prelude","enumFromThen")).setToken(tok);
    }

    public HaskellSym enumFromThenTo(Token tok){
        return (HaskellSym) (this.newHaskellNamedSym("Prelude","enumFromThenTo")).setToken(tok);
    }

    public HaskellSym tuple(Token tok,int i){
        this.prelude.createTuple(i);
        HaskellSym res = (HaskellSym) (this.prelude.createSymbol("Prelude","@"+i)).setToken(tok);
        res.setTuple(i);
        return res;
    }

    public HaskellSym typeTuple(Token tok,int i){
        this.prelude.createTuple(i);
        HaskellSym res = (HaskellSym) (this.prelude.createSymbol("Prelude","@"+i)).setToken(tok);
        res.setTuple(i);
        return res;
    }

    public HaskellSym negate(Token tok){
        return (HaskellSym) (this.newHaskellNamedSym("Prelude","negate")).setToken(tok);
    }

    public HaskellSym minus(Token tok){
        return (HaskellSym) (this.newHaskellNamedSym("Prelude","-")).setToken(tok);
    }

    public HaskellSym flip(Token tok){
        return (HaskellSym) (this.newHaskellNamedSym("Prelude","flip")).setToken(tok);
    }

    public HaskellSym monadThen(Token tok){
        return this.op((HaskellSym) (this.newHaskellNamedSym("Prelude",">>")).setToken(tok));
    }

    public HaskellSym monadBind(Token tok){
        return this.op((HaskellSym) (this.newHaskellNamedSym("Prelude",">>=")).setToken(tok));
    }

    public HaskellSym listCons(Token tok){
        return this.op((HaskellSym) this.newHaskellNamedSym("Prelude",":",this.prelude.getListCons()).setToken(tok));
    }

    public HaskellSym emptyListCons(Token tok){
        return (HaskellSym) (this.prelude.createSymbol("Prelude","[]")).setToken(tok);
    }

    public HaskellSym arrowCons(Token tok){
        return this.op((HaskellSym) this.newHaskellNamedSym("Prelude","->",this.prelude.getTypeArrow()).setToken(tok));
    }

    public HaskellSym concat(Token tok){
        return (HaskellSym) (this.newHaskellNamedSym("Prelude","concat")).setToken(tok);
    }

    public HaskellSym map(Token tok){
        return (HaskellSym) this.newHaskellNamedSym("Prelude","map").setToken(tok);
    }

    public HaskellSym concatMap(Token tok){
        return (HaskellSym) this.newHaskellNamedSym("Prelude","concatMap").setToken(tok);
    }

    public HaskellSym trueCons(Token tok){
        return (HaskellSym) this.newHaskellNamedSym("Prelude","True").setToken(tok);
    }

}
