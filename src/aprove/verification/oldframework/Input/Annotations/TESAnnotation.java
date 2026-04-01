package aprove.verification.oldframework.Input.Annotations;

public class TESAnnotation extends Annotation{

    private boolean innermost;

    public TESAnnotation(boolean innermost){
        this.innermost = innermost;
    }

    public boolean getInnermost(){
        return this.innermost;
    }

}


