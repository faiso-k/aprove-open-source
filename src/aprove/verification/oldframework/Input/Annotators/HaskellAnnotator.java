package aprove.verification.oldframework.Input.Annotators;

import java.util.*;

import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Annotations.*;
import aprove.verification.oldframework.Utility.*;

public class HaskellAnnotator implements Annotator {

    public static final char STARTTERM_SEPARATOR = '\0';

    @Override
    public Annotation annotate(final TypedInput typedInput) {
        if (typedInput.getLanguage() != Language.HASKELL) {
            throw new RuntimeException("no Haskell");
        }
        final String protoAnno = typedInput.getOriginInput().getProtoAnnotation();
        if (protoAnno == null) {

            // output an error when in CLI mode and no startterms were defined
            if (aprove.Main.UI_MODE == aprove.Main.UI.CLI) {

                final HaskellProgram hp = (HaskellProgram) typedInput.getInput();
                if (hp.getModules().getStartTerms().size() == 0) {
                    // no startterms in the modules
                    aprove.verification.oldframework.Haskell.HaskellError.output(
                        (aprove.input.Generated.haskell.node.Token) null, "No startterms were provided.");
                }
            }

            return new HaskellAnnotation();
        }
        // TODO maybe find some better way of handling start terms
        final List<String> terms = HaskellAnnotator.splitStartTerms(typedInput);

        // output an error when in CLI mode and no startterms were defined
        if ((aprove.Main.UI_MODE == aprove.Main.UI.CLI) && (terms.isEmpty())) {
            aprove.verification.oldframework.Haskell.HaskellError.output((aprove.input.Generated.haskell.node.Token) null,
                "No startterms were provided.");
        }

        return new HaskellAnnotation(terms);
    }

    /**
     * splits the startterms in the protoAnnotation, if they exist
     * @param typedInput an Input, that possibly has a protoAnnotation
     * @return a list of startterms
     */
    public static List<String> splitStartTerms(final TypedInput typedInput) {
        final String protoAnno = typedInput.getOriginInput().getProtoAnnotation();
        List<String> terms = new ArrayList<String>(0);
        if (protoAnno != null) {
            terms = StringSplitter.splitNotQuoted(protoAnno, HaskellAnnotator.STARTTERM_SEPARATOR); //Arrays.asList(protoAnno.split(";"));
        }
        return terms;
    }

}
