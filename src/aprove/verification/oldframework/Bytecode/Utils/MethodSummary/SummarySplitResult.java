package aprove.verification.oldframework.Bytecode.Utils.MethodSummary;

import org.json.JSONException;
import org.json.JSONObject;

import aprove.verification.oldframework.Bytecode.Utils.*;

public class SummarySplitResult implements SplitResult {

    public final ComplexitySummary summary;

    private String exception;

    private boolean exceptionRefinementDone;

    public SummarySplitResult(ComplexitySummary summary) {
        this.summary = summary;
        this.exception = null;
        this.exceptionRefinementDone = false;
    }

    private SummarySplitResult(ComplexitySummary summary, String exception, boolean exceptionRefinementDone) {
        this.summary = summary;
        this.exception = exception;
        this.exceptionRefinementDone = exceptionRefinementDone;
    }

    public boolean needsExceptionRefinement() {
        return !exceptionRefinementDone && !summary.throwsSet.isEmpty();
    }

    public SummarySplitResult shallowCopy() {
        return new SummarySplitResult(summary, exception, exceptionRefinementDone);
    }

    public SummarySplitResult replaceException(String exception) {
        this.exception = exception;
        this.exceptionRefinementDone = true;
        return this;
    }

    @Override
    public void toString(StringBuilder sb) {
        sb.append("Refined Complexity: [")
          .append(summary.lowerTime.toString())
          .append(", ")
          .append(summary.upperTime.toString())
          .append("]");
        if (exception != null) {
            sb.append(", throws: ")
              .append(exception);
        }
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        return summary.toJSON();
    }

    public String getException() {
        return exception;
    }

    public void setException(String exception) {
        this.exception = exception;
    }

    public boolean isExceptionRefinementDone() {
        return exceptionRefinementDone;
    }
}
