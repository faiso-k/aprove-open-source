package aprove.verification.oldframework.Input.Annotators;

import aprove.verification.oldframework.Input.*;

public interface PublicAnnotator {

    public AnnotatedInput annotate(TypedInput typedInput) throws SourceException;

}
