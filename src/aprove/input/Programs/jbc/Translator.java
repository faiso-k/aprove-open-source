package aprove.input.Programs.jbc;

import java.io.*;
import java.util.logging.*;

import aprove.runtime.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Java Byte Code Translator. It helps transforming a JBCProgram (which can be a file) into a JBCProblem (which also
 * needs a start state).
 * @author Carsten Otto
 */
public class Translator extends aprove.verification.oldframework.Input.Translator.TranslatorSkeleton {
    /**
     * The program to analyze
     */
    private JBCProgram jbcProgram;

    /**
     * runtime options, e.g. how to initialize static fields when assuming the class already was initialized
     */
    private RuntimeOptions runtimeOptions;

    /**
     * The method identifier of the start method
     */
    private MethodIdentifier methodId;

    /**
     * Information about annotations we need to add in the start state
     */
    private StartStateAnnotator startStateAnnotator;

    /** {@inheritDoc} */
    @Override
    public Object getState() {
        return this.jbcProgram;
    }

    /** {@inheritDoc} */
    @Override
    public Language getLanguage() {
        return Language.JBC;
    }

    /** {@inheritDoc} */
    @Override
    public void translate(final Reader reader) throws TranslationException {
        throw new IllegalArgumentException("Cannot parse JBC from a raw Reader - need a FileInput!");
    }

    /** {@inheritDoc} */
    @Override
    public void translate(final Input fileInput) throws TranslationException {
        this.jbcProgram = new JBCProgram(fileInput);
    }

    /**
     * @param cPath the class path
     * @param terminationGraph the termination graph of the returned state
     * @return the start state for the start method (maybe with additional annotations)
     */
    public State createStartState(final ClassPath cPath, final TerminationGraph terminationGraph) {
        final IClass c = cPath.getClass(this.methodId.getClassName());
        final IMethod parsedStartMethod = c.getLocalMethod(this.methodId);
        if (parsedStartMethod == null) {
            final String message = "Start method " + this.methodId + " not found";
            final Logger logger = Logger.getLogger("JBC Translator");
            logger.log(Level.SEVERE, message);
            throw new RuntimeException(message);
        }

        // create a state for the method and annotate the arguments according to the annotator
        final State startState = new State(cPath, terminationGraph, parsedStartMethod, this.startStateAnnotator);

        /*
         * If we are in competition mode and we are starting with main(String[]), assume that this array always exists:
         * Create it and mark it as existing.
         */
        if (terminationGraph.getJBCOptions().inputArrayExists() && parsedStartMethod.isMain()) {
            final AbstractVariableReference argumentArrayRef = startState.getCurrentStackFrame().getLocalVariable(0);

            final ObjectInstance jlO =
                    ConcreteInstance.newInstanceSliceType(cPath.getTypeTree(ClassName.Important.JAVA_LANG_OBJECT
                        .getClassName()));

            startState.addAbstractVariable(argumentArrayRef, jlO);

            // we know that you are there:
            startState.getHeapAnnotations().setExistenceIsKnown(argumentArrayRef);
        }
        return startState;
    }

    /**
     * Parse the string and find the method identifier of the start method
     * @param startMethodString a string representation of the start method
     */
    public void parseMethodString(final String startMethodString) {
        this.methodId = ParsedMethod.parseFullyQualifiedMethodNameWithSig(startMethodString);
    }

    /**
     * @param annotationsString a string representation giving information about annotations to add in the start state
     * (and for runtime options, e.g. related to static fields)
     */
    public void parseAnnotationsString(final String annotationsString) {
        final Pair<StartStateAnnotator, RuntimeOptions> pair = StartStateAnnotator.parse(annotationsString);
        this.startStateAnnotator = pair.x;
        this.runtimeOptions = pair.y;
    }

    /**
     * @return runtime options, e.g. how to initialize static fields when assuming the class already was initialized
     */
    public RuntimeOptions getRuntimeOptions() {
        return this.runtimeOptions;
    }

}
