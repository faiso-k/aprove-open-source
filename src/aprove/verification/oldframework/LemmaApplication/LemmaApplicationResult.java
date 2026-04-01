package aprove.verification.oldframework.LemmaApplication;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;

/**
 * In this class the result of a lemma application on formula level is stored.
 * The result is the new obtained formula.
 * Additionally it is stored which lemma was applicated
 * at with position in the original formula.
 * The original formula is stored here, too, to calculate the utility of the lemma application.
 *
 * @author dickmeis
 * @version $Id$
 */

public class LemmaApplicationResult implements Comparable{

    /**
     * When choosing this value be aware of buffer over runs
     * during the compareTo
     * Of course, this would happen if using Integer.MINVALUE
     */
    public static final int UnusefulValue = -1000;

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
    protected Formula result;

    /**
     * the original formula on which the lemma application took place
     */
    protected Formula original;

    /**
     * Only used for the interactive lemma application processor.
     * A flag indicating whether the result has been selected by the user
     * to be used for further proving.
     */
    protected boolean selected;

    /**
     * A flag indicating whether the utility measure has already been claculated.
     */
    protected boolean calculated;

    /**
     * The measure how util the lemma application might be for a proof.
     */
    protected int utilityEstimation;

    /**
     * @param lemma     the lemma which has been applicated
     * @param direction the direction was the lemma applied from left to right or vice versa?
     * @param position  the position where the lemma has been applicated
     * @param result    the result of the lemma applicatio
     * @param original  the original formula on which the lemma application took place
     */
    public LemmaApplicationResult(Formula lemma, LemmaApplicationDirection direction,
            Position position, Formula result, Formula original){
        this.lemma = lemma;
        this.direction = direction;
        this.position = position;
        this.result = result;
        this.original = original;
        this.selected = false;
        this.calculated = false;
        this.utilityEstimation = 0;
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

    public Formula getResult(){
        return this.result;
    }

    public boolean isSelected(){
        return this.selected;
    }

    public void setSelected(boolean selected){
        this.selected = selected;
    }

    public LemmaApplicationResult deepcopy(){
        LemmaApplicationResult lar =  new LemmaApplicationResult(
                this.lemma.deepcopy(), this.direction,
                this.position.deepcopy(), this.result.deepcopy(), this.original.deepcopy());
        lar.setSelected(this.selected);
        return lar;
    }

    public int getUtilityEstimation(){
        if (!this.calculated){
            this.calculateUtilityMeasure();
        }
        return this.utilityEstimation;
    }

    protected void calculateUtilityMeasure(){
        int lengthDecrease;
        int numberDefFunctionDecrease;

        lengthDecrease = this.original.getSize() - this.result.getSize();

        int ofs = this.original.getAllDefFunctionSymbols().size();
        int rfs = this.result.getAllDefFunctionSymbols().size();
        numberDefFunctionDecrease = ofs - rfs;

        this.utilityEstimation = lengthDecrease + 2 * numberDefFunctionDecrease;

        this.calculated = true;
    }

    public void setUnusful(){
        this.utilityEstimation = LemmaApplicationResult.UnusefulValue;
        this.calculated = true;
    }

    @Override
    public int compareTo(Object o) {
        if (o instanceof LemmaApplicationResult){
            LemmaApplicationResult oLAR = (LemmaApplicationResult) o;
            int thisUtilityMeasure = this.getUtilityEstimation();
            int oLarUtilityMeasure = oLAR.getUtilityEstimation();
            int diff = thisUtilityMeasure - oLarUtilityMeasure;
            return diff;
        }
        return 0;
    }
}