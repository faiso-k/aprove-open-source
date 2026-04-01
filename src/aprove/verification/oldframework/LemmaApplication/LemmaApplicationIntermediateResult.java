package aprove.verification.oldframework.LemmaApplication;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;

/**
 * In this class the result of a lemma application on term level is stored.
 * (@see aprove.verification.oldframework.LemmaApplication.LemmaApplicationResult)
 * The result is the new obtained term.
 * Additionally it is stored which lemma was applicated
 * at with position in the original term.
 * (The original term is not stored here.)
 *
 * @author dickmeis
 * @version $Id$
 */

public class LemmaApplicationIntermediateResult {

    /**
     * the lemma which has been applicated
     */
    protected Formula lemma;

    /**
     * in which dirction was the lemma applied?
     */
    protected LemmaApplicationDirection direction;

    /**
     * the position where the lemma has been applicated
     */
    protected Position position;

    /**
     * the result of the lemma application
     */
    protected AlgebraTerm result;

    /**
     * @param lemma     the lemma which has been applicated
     * @param direction the direction was the lemma applied from left to right or vice versa?
     * @param position  the position where the lemma has been applicated
     * @param result    the result of the lemma application
     */
    public LemmaApplicationIntermediateResult(Formula lemma, LemmaApplicationDirection direction,
            Position position, AlgebraTerm result){
        this.lemma = lemma;
        this.direction = direction;
        this.position = position;
        this.result = result;
    }

    public Formula getLemma(){
        return this.lemma;
    }

    public LemmaApplicationDirection getDirection(){
        return this.direction;
    }

    public Position getPosition(){
        return this.position;
    }

    public AlgebraTerm getResult(){
        return this.result;
    }

    public LemmaApplicationIntermediateResult deepcopy(){
        LemmaApplicationIntermediateResult lar =  new LemmaApplicationIntermediateResult(
                this.lemma.deepcopy(), this.direction, this.position.deepcopy(), this.result.deepcopy());
        return lar;
    }
}