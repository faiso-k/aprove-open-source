package aprove.verification.oldframework.Input.Annotations;

import aprove.verification.oldframework.Input.*;

/**
 * @author Carsten Otto
 */
public class JBCAnnotation extends Annotation {

    private final String startMethodString;

    private final String annotationsString;

    private final HandlingMode goal;

    public JBCAnnotation() {
        this.startMethodString = null;
        this.annotationsString = null;
        this.goal = HandlingMode.Termination;
    }

    public JBCAnnotation(String startMethod, String annotationsStringParam, HandlingMode goal) {
        this.startMethodString = startMethod;
        this.annotationsString = annotationsStringParam;
        this.goal = goal == null ? HandlingMode.Termination : goal;
    }

    public String getStartMethodString() {
        return this.startMethodString;
    }

    public String getAnnotationsString() {
        return this.annotationsString;
    }

    public HandlingMode getGoal() {
        return goal;
    }
}
