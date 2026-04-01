package aprove.verification.oldframework.Input.Annotators;

import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Annotations.*;

public class TESAnnotator implements Annotator{

    @Override
    public Annotation annotate(TypedInput typedInput){
        if(typedInput.getLanguage() != Language.TES) {
            throw new RuntimeException("no TES");
        }
        return new TESAnnotation(false);
    }

}
