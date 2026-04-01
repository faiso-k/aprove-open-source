package aprove.verification.oldframework.Haskell.Declarations;


/**
 * This class represents a rule of selector declaration in Haskell
 * @author Matthias Raffelsieper
 * @version $Id$
 */
public class SelectorDecl extends FuncDecl implements HaskellDecl {

    public SelectorDecl(FuncDecl fd) {
        super(fd.func, fd.rexp, fd.exp, fd.entityFrame, fd.patternMember);
        this.setToken(fd.getToken());
    }

}
