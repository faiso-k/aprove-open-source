package aprove.verification.idpframework.Core.Utility.Marking;





/**
 *
 * @author Martin Pluecker
 * @param <T>
 */
public interface Markable<ResultType extends MarkContent<ResultType, R>, M extends Markable<ResultType, M, R>, R>  {

    public MarksHandler<ResultType, M, R> getMarks();

}