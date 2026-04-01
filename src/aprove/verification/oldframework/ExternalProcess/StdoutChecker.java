package aprove.verification.oldframework.ExternalProcess;

public interface StdoutChecker<T> extends Checker<T> {
    String getTempPrefix();
    String getInputTempSuffix();
}