package aprove.verification.oldframework.IntTRS;

import aprove.verification.oldframework.Utility.GenericStructures.*;

public interface VariableRenaming {

    /**
     * Get variable renaming in current obligation as CollectionMap
     *
     * @return variable renaming as CollectionMap
     */
    CollectionMap<String, String> getVariableRenaming();

    /**
     * Set variable renaming in current obligation with CollectionMap
     *
     * @param variableRenaming variable renaming as CollectionMap
     */
    void setVariableRenaming(CollectionMap<String, String> variableRenaming);

}
