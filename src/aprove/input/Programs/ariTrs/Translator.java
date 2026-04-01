package aprove.input.Programs.ariTrs;

import java.io.*;

import org.antlr.runtime.*;

import aprove.input.Generated.ariTrs.*;
import aprove.input.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Translator.*;

/**
 * Translator for various versions of TRSs.
 * @author unknown
 * @version $Id$
 */
public class Translator extends TranslatorSkeleton {

    /**
     * The language this translator parses (depends on the particular input).
     */
    private Language language;

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Input.Translator#getLanguage()
     */
    @Override
    public Language getLanguage() {
        return this.language;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Input.Translator#translate(java.io.Reader)
     */
    @Override
    public void translate(Reader reader) {
        try {
        	ariTrsLexer lex = new ariTrsLexer(new ANTLRReaderStream(reader));
            CommonTokenStream tokens = new CommonTokenStream(lex);
            ariTrsParser parser = new ariTrsParser(tokens);
            RawAriTrs rawptrs = parser.trs();
            ObligationCreator obc = new ObligationCreator(rawptrs);
            this.setState(obc.buildObligation());
            this.language = obc.getLanguage();
        } catch (RecognitionException re) {
            ParseError pe = new ParseError();
            pe.setLine(re.line);
            pe.setColumn(re.charPositionInLine);
            pe.setMessage(re.getMessage());
            this.getErrors().add(pe);
        } catch (IOException e) {
            ParseError pe = new ParseError();
            pe.setMessage(e.getMessage());
            this.getErrors().add(pe);
        } catch (ObligationCreatorException e) {
            this.getErrors().addAll(e.getParseErrors());
        }
    }

    private void processProtoAnnotation(RawPtrs rawptrs) {
        String protoAnnotation = this.getProtoAnnotation();
        if (protoAnnotation != null) {
            TrsAnnotation annotation = TrsAnnotation.parse(protoAnnotation);
            switch (annotation.evaluationStrategy) {
                case INNERMOST: rawptrs.setRewriteStrategy(RewriteStrategy.INNERMOST);
                break;
                case OUTERMOST: rawptrs.setRewriteStrategy(RewriteStrategy.OUTERMOST);
                break;
                case FULL: rawptrs.setRewriteStrategy(RewriteStrategy.OUTERMOST);
                break;
                default: throw new RuntimeException("Unknown evaluation strategy " + annotation.evaluationStrategy + " for TRSs!");
            }
        }
    }

    private static class TrsAnnotation {

        static enum EvaluationStrategy {
            FULL, INNERMOST, OUTERMOST
        }

        private HandlingMode mode;
        private EvaluationStrategy evaluationStrategy;

        private TrsAnnotation(HandlingMode mode, EvaluationStrategy evaluationStrategy) {
            this.mode = mode == null ? HandlingMode.Termination : mode;
            this.evaluationStrategy = evaluationStrategy == null ? EvaluationStrategy.INNERMOST : evaluationStrategy;
        }

        public static TrsAnnotation parse(String protoAnnotation) {
            String[] parts = protoAnnotation.split(",");
            HandlingMode mode = null;
            EvaluationStrategy strategy = null;
            for (String part: parts) {
                String[] entry = part.trim().split(" ");
                if (entry.length != 2) {
                    TrsAnnotation.fail();
                }
                String key = entry[0].trim().toUpperCase();
                String value = entry[1].trim().toUpperCase();
                switch (key) {
                    case "GOAL":
                        if (mode != null) {
                            TrsAnnotation.fail();
                        }
                        switch (value) {
                            case "COMPLEXITY": mode = HandlingMode.RuntimeComplexity;
                            break;
                            case "TERMINATION": mode = HandlingMode.Termination;
                            break;
                            default: TrsAnnotation.fail();
                        }
                        break;
                    case "STRATEGY":
                        if (strategy != null) {
                            TrsAnnotation.fail();
                        }
                        try {
                            strategy = EvaluationStrategy.valueOf(value);
                        } catch (IllegalArgumentException e) {
                            TrsAnnotation.fail();
                        }
                        break;
                    default: TrsAnnotation.fail();
                }
            }
            return new TrsAnnotation(mode, strategy);
        }

        private static void fail() {
            throw new RuntimeException("Parsing the TRS-query failed.");
        }
    }
}
