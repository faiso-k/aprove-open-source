package aprove.verification.oldframework.Input.Annotations;

public class SESAnnotation extends Annotation{

    private boolean innermost;

    public SESAnnotation(boolean innermost){
        super();
        this.innermost = innermost;
    }

    public boolean getInnermost(){
        return this.innermost;
    }

}


