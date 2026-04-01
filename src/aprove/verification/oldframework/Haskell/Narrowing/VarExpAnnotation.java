package aprove.verification.oldframework.Haskell.Narrowing;


public class VarExpAnnotation extends Annotation{

    @Override
    public Mode getMode(){
        return Mode.VAREXP;
    }

    @Override
    public String toString(){
        return "VE";
    }
}

