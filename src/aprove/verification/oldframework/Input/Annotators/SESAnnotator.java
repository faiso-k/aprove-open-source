package aprove.verification.oldframework.Input.Annotators;

import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Annotations.*;

public class SESAnnotator implements Annotator{

    @Override
    public Annotation annotate(TypedInput typedInput){
        if(typedInput.getLanguage() != Language.SES) {
            throw new RuntimeException("no SES");
        }
        return new SESAnnotation(false);
    }

}
