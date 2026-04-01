package aprove.verification.oldframework.Input.Annotators;

import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Annotations.*;

public class TrivialAnnotator implements Annotator{

    @Override
    public Annotation annotate(TypedInput typedInput){
        return new TrivialAnnotation();
    }

    /* Just a convenience method */
    public static Annotation staticAnnotate() {
        return new TrivialAnnotation();
    }

}
