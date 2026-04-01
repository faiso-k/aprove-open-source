package aprove.verification.idpframework.Core.Utility.Marking;

/**
 *
 * @author MP
 */
public interface SelfMarkable<ResultType extends MarkContent<ResultType, M>, M extends Markable<ResultType, M, M>> extends Markable<ResultType, M, M> {

    public ResultType getSelfMark();

}
