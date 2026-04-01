package aprove.verification.oldframework.Input.Annotators;

import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Annotations.*;

public class PrologAnnotator implements Annotator {

    @Override
    public Annotation annotate(final TypedInput typedInput) {
        if (typedInput.getLanguage() != Language.PROLOG) {
            throw new RuntimeException("no Prolog");
        }
        final String protoAnno = typedInput.getOriginInput().getProtoAnnotation();
        if (protoAnno == null) {
            return new NewPrologAnnotation();
        }
        //        List<String> queries = Arrays.asList(protoAnno.split(";"));
        return new NewPrologAnnotation(protoAnno);
    }

}
