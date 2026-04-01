package aprove.input.Programs.impact.Program;

import java.util.*;

public class FunctionDeclaration {

    private final String id;
    private final boolean isVoid;
    private final ArrayList<String> params;
    private final HashSet<String> labels;

    public FunctionDeclaration(
        final String id,
        final boolean isCurrentVoid,
        final ArrayList<String> params,
        final HashSet<String> labels)
    {
        this.id = id;
        this.isVoid = isCurrentVoid;
        this.params = (ArrayList<String>) params.clone();
        this.labels = (HashSet<String>) labels.clone();
    }



    public boolean isVoid() {
        return this.isVoid;
    }

    public ArrayList<String> getParams() {
        return this.params;
    }

    public boolean hasLabel(final String label) {
        return this.labels.contains(label);
    }
}
