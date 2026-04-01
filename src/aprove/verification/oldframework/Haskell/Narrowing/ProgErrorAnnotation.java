package aprove.verification.oldframework.Haskell.Narrowing;


public class ProgErrorAnnotation extends Annotation{
    @Override
    public Mode getMode(){
        return Mode.PROGERROR;
    }
}

