package aprove.verification.oldframework.ExternalProcess;

public interface FileChecker<T> extends Checker<T> {
    String getTempPrefix();
    String getInputTempSuffix();
    String getOutputTempSuffix();
}