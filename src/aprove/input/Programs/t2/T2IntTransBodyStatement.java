package aprove.input.Programs.t2;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;

public interface T2IntTransBodyStatement {
    /**
     * Export a String representation of the statement (as a single line) to a string builder
     * @param o the helper for that
     * @param sb the string builder holding the result
     */
    void export(Export_Util o, StringBuilder sb);

    /**
     * @return all variables occurring in this statement.
     */
    Set<TRSVariable> getVariables();
}
