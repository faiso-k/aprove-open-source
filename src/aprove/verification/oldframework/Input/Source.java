package aprove.verification.oldframework.Input;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.*;
import aprove.strategies.Parameters.*;
import aprove.strategies.Util.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Input.Annotators.*;
import aprove.verification.oldframework.Input.TypeAnalyzers.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.ObligationFactories.*;


/**
 * Class which stores and generates (obligation, strategy) tuples fetched by
 * BatchmodeProcessor.
 * @author Martin Mertens, Peter Schneider-Kamp
 * @version $Id$
 */
public class Source {

    private final static Logger log = Logger.getLogger("src.aprove.verification.oldframework.Input.Source");

    protected List<Input> inputs;
    protected TypeAnalyzer typeAnalyzer;
    protected PublicAnnotator annotator;
    protected ObligationFactory obligationFactory;
    protected StrategySource strategyFactory;
    protected int index;

    protected Source() {
        // Nothing to do.
    }

    public Source(Targets targets, PublicAnnotator annotator, ObligationFactory obligationFactory, StrategySource strategyFactory) {
        this.inputs = targets;
    this.typeAnalyzer = targets.getTypeAnalyzer();
        this.annotator = annotator;
        this.strategyFactory = strategyFactory;
        this.obligationFactory = obligationFactory;
        this.reset();
    }

    /**
     *
     * @param handlingMode can be null. Otherwise it will be tried to set the HandlingMode
     */
    public ObligationAndStrategy next(HandlingMode handlingMode) throws SourceException {
        if (this.hasNext()) {
            Input input = this.inputs.get(this.index);
            this.index++;
            TypedInput typedInput = this.typeAnalyzer.analyze(input);
            if (handlingMode != null){
                if (!typedInput.getModedType().setMode(handlingMode)) {
                    Source.log.info("Could not set handling mode " + handlingMode +
                            " for " + typedInput + ". Continuing with " +
                            "handling mode" +
                            typedInput.getHandlingMode() + ".");
                }
            }
            AnnotatedInput annotatedInput = this.annotator.annotate(typedInput);
//            int timeout = annotatedInput.getAnnotation().getTimeout();
            Pair<ObligationNode, List<BasicObligationNode>> rootAndPositions =
                    this.obligationFactory.getRootAndPositions(annotatedInput);
            ObligationNode root = rootAndPositions.x;
            List<BasicObligationNode> positions = rootAndPositions.y;
            StrategyProgram prog = this.strategyFactory.getStrategyProgram(annotatedInput);
//            proc.setTimeLimit(timeout*1000);
        return new ObligationAndStrategy(root, positions, prog, input.getPath(), this.getNextIndex());
    } else {
        return null;
    }
    }

    public void clearResult() {
        int i = this.index;
        this.reset();
        while (this.hasNext()) {
            Input input = this.inputs.get(this.index);
            this.index++;
            try{
                TypedInput typedInput = this.typeAnalyzer.analyze(input);
                AnnotatedInput annotatedInput = this.annotator.annotate(typedInput);
//          int timeout = annotatedInput.getAnnotation().getTimeout();
            this.obligationFactory.clearResult(annotatedInput);
 //            proc.setTimeLimit(timeout*1000);
           }
            catch (Exception e)
            {
            }
       }
       this.index=i;
    }

    public void reset() {
        this.index = 0;
    }

    public int getSize() {
        return this.inputs.size();
    }

    public int getNextIndex() {
        return this.index;
    }

    public boolean hasNext() {
    return this.index < this.inputs.size();
    }

}
