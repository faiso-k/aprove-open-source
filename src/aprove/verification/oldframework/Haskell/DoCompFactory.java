package aprove.verification.oldframework.Haskell;

import java.util.*;

import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Qualifiers.*;

public interface DoCompFactory {
    public HaskellExp buildMonadBind(HaskellPat pat,HaskellExp exp,HaskellExp next);
    public HaskellExp buildMonadThen(HaskellExp exp,HaskellExp next);
    public HaskellExp buildMonadLet(List<HaskellDecl> decls,HaskellExp res,LetQual lq);
    public HaskellExp buildListCompGen(HaskellPat pat,HaskellExp exp,HaskellExp next);
    public HaskellExp buildListCompGuard(HaskellExp exp,HaskellExp next);
    public HaskellExp buildListCompLet(List<HaskellDecl> decls,HaskellExp res,LetQual lq);
}
