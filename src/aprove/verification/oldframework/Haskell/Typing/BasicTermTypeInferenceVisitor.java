package aprove.verification.oldframework.Haskell.Typing;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 */
public class BasicTermTypeInferenceVisitor extends TypeInferenceVisitor {

    public BasicTermTypeInferenceVisitor(Prelude prelude,Assumptions assum,ClassConstraintGraph ccg){
        super(prelude,assum,ccg);
    }

    @Override
    public HaskellObject leave(HaskellObject ho){
        this.typeAnnos.add(ho);
        this.push(TypeSchema.create(ho.getTypeTerm()));
        this.push(this.massMgu(2,ho));
        ho.setTypeTerm(this.peek().getMatrix());
        return ho;
    }


}
