package aprove.verification.oldframework.Input.Annotators;

import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Annotations.*;

public interface Annotator {

    public Annotation annotate(TypedInput typedInput) throws SourceException;

}
