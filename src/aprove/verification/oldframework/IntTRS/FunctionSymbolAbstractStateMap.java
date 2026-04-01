package aprove.verification.oldframework.IntTRS;

import java.util.*;

import aprove.input.Programs.llvm.states.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Similar to the Interface VariableRenaming, this interface demands a map to be saved.
 * This time, the function symbol and the corresponding abstract state in the SEGraph are stored.
 * 
 * @author cMensendiek
 */
public interface FunctionSymbolAbstractStateMap {

    /**
     * Get map of AbstractStates to FunctionSymbol
     *
     * @return the corresponding map
     */
    Map<FunctionSymbol, Node<LLVMAbstractState>> getFunctionSymbolAbstractStateMap();

    /**
     * Set map of AbstractStates to FunctionSymbol
     *
     * @param map map of AbstractStates to FunctionSymbol
     */
    void setFunctionSymbolAbstractStateMap(Map<FunctionSymbol, Node<LLVMAbstractState>> map);
    
}
