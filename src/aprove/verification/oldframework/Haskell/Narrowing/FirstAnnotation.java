package aprove.verification.oldframework.Haskell.Narrowing;


public class FirstAnnotation extends Annotation{
    @Override
    public Mode getMode(){
        return Mode.FIRST;
    }

    @Override
    public String toString(){
        return "HEAD";
    }
}

