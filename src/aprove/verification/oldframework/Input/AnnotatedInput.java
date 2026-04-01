package aprove.verification.oldframework.Input;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Input.Annotations.*;

public class AnnotatedInput implements HTML_Able {
    protected TypedInput typedInput;
    protected Annotation annotation;

    public AnnotatedInput(final TypedInput typedInput, final Annotation annotation){
        this.typedInput = typedInput;
        this.annotation = annotation;
    }

    public TypedInput getTypedInput(){
        return this.typedInput;
    }

    public void setTypedInput(final TypedInput typedInput){
        this.typedInput = typedInput;
    }

    public Annotation getAnnotation(){
        return this.annotation;
    }

    @Override
    public String toHTML() {
        final Object obj = this.typedInput.getInput();
        String res = null;
        if (obj instanceof HTML_Able) {
            res = ((HTML_Able) obj).toHTML();
        } else if (obj instanceof Exportable) {
            res = ((Exportable) obj).export(new HTML_Util());
        } else {
            final String cname = obj.getClass().getName();
            res = "<strong>" + cname + " is not HTML_Able!</strong>";
        }
        res = res + this.annotation.toHTML();
        return res;
    }

    public void setAnnotation(final Annotation annotation) {
        this.annotation = annotation;
    }

}
