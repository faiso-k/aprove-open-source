package aprove.verification.oldframework.Input.Annotators;

import java.io.*;
import java.util.*;
import java.util.jar.*;

import aprove.runtime.Options.JBCAnalysisOptions.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Annotations.*;

/**
 * @author Carsten Otto
 */
public class JBCAnnotator implements Annotator {
    /**
     * tag used in jar manifest file
     */
    private static final String STARTMETHOD = "Start-Method";
    private static final String MAINCLASS = "Main-Class";
    private static final String ANALYSISGOAL = "Analysis-Goal";

    /**
     * {@inheritDoc}
     */
    @Override
    public Annotation annotate(final TypedInput typedInput) {
        if (typedInput.getLanguage() != Language.JBC) {
            throw new RuntimeException("no Java Byte Code");
        }
        // Check for given queries
        final String protoAnnotation = typedInput.getOriginInput().getProtoAnnotation();

        HandlingMode goal = HandlingMode.Termination;
        String startMethodFromAnnotation = null;
        String annotationsForStartState = null;
        if (protoAnnotation != null) {
            String[] parts = protoAnnotation.split("\\|");
            Optional<HandlingMode> hm = HandlingMode.valueOfIgnoreCase(parts[0]);
            switch (parts.length) {
                case 1:
                    if (hm.isPresent()) {
                        goal = hm.get();
                    } else {
                        startMethodFromAnnotation = protoAnnotation;
                    }
                    break;
                case 2:
                    if (hm.isPresent()) {
                        goal = hm.get();
                        startMethodFromAnnotation = parts[1];
                    } else {
                        startMethodFromAnnotation = parts[0];
                        annotationsForStartState = parts[1];
                    }
                    break;
                case 3:
                    goal = hm.get();
                    startMethodFromAnnotation = parts[1];
                    annotationsForStartState = parts[2];
                    break;
                default:
                    throw new IllegalArgumentException();
            }
        }

        String jarStartFunction = null;
        String mainClass = null;
        final Input input = typedInput.getOriginInput();
        if (input.getExtension() != null && "jar".equals(input.getExtension().toLowerCase())) {
            try (InputStream inputStream = input.getInputStream()) {
                if (inputStream != null) {
                    try (JarInputStream jis = new JarInputStream(inputStream)) {
                        final Manifest manifest = jis.getManifest();
                        if (manifest != null) {
                            final Attributes attributes = manifest.getMainAttributes();
                            jarStartFunction = attributes.getValue(STARTMETHOD);
                            mainClass = attributes.getValue(MAINCLASS);

                            if (mainClass != null) {
                                mainClass = mainClass.replace('/', '.');
                            }

                            final String goalStr = attributes.getValue(ANALYSISGOAL);
                            if (goalStr != null) {
                                goal = HandlingMode.valueOfIgnoreCase(goalStr).get();
                            }
                        }
                        jis.close();
                        inputStream.close();
                    }
                }
            } catch (final IOException e) {
                throw new RuntimeException("Could not read jar file", e);
            }
        }

        if (jarStartFunction == null && startMethodFromAnnotation == null) {
            if (mainClass == null) {
                throw new RuntimeException("No start method given");
            }
            jarStartFunction = mainClass + ".main([Ljava/lang/String;)V";
        }
        final String startMethod = startMethodFromAnnotation != null ? startMethodFromAnnotation : jarStartFunction;
        return new JBCAnnotation(startMethod, annotationsForStartState, goal);
    }
}
