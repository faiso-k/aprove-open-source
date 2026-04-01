package aprove.verification.oldframework.Bytecode.Utils;

import java.util.*;

import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.OpCodes.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Instances of this class analyze the given method and for each opcode of that
 * method give information about the local variables that are needed. This
 * should be quite precise, but should be considered an overapproximation.
 * @author cotto
 */
public class MethodUsedVariables {
    /**
     * The method to analyze.
     */
    private final IMethod method;

    /**
     * The result of the analysis (map from opcode position to used variables).
     */
    private volatile CollectionMap<Integer, Integer> analysis;

    /**
     * Create a new instance for the given method.
     * @param methodParam the method to analyze
     */
    public MethodUsedVariables(final IMethod methodParam) {
        assert (methodParam != null);
        this.method = methodParam;
    }


    /**
     * @param pos the position of the opcode
     * @return the indices of used variables at the position
     */
    public Set<Integer> usedAt(int pos) {
        if (analysis == null) {
            synchronized (this) {
                if (analysis == null) {
                    this.analyze();
                }
            }
        }
        return (Set<Integer>)analysis.getNotNull(pos);
    }

    private void analyze() {
        Map<OpCode, UpdateListener> listeners = createListenerTree(method.getStart());
        propagateKnowledge(listeners);
        analysis = buildResult(listeners);
    }

    private Map<OpCode, UpdateListener> createListenerTree(OpCode start) {
        Map<OpCode, UpdateListener> res = new LinkedHashMap<>();

        Queue<UpdateListener> todo = new ArrayDeque<>();
        {//first element
            UpdateListener first = new UpdateListener(start);
            res.put(start, first);
            todo.add(first);
        }

        while (!todo.isEmpty()) {
            //pop queue head
            UpdateListener current = todo.remove();
            List<OpCode> successors = new ArrayList<>();

            //successors from exceptions
            for (Pair<ClassName, OpCode> handler : current.opCode.getExceptionTable()) {
                successors.add(handler.y);
            }
            //normal successors
            successors.addAll(current.opCode.getAllPossibleSuccessors());

            //deal with successors
            for (OpCode succ : successors) {
                //see if we already have a listener
                UpdateListener newListener = res.get(succ);
                if (newListener == null) {
                    //successor wasn't visited yet, create a new Listener
                    newListener = new UpdateListener(succ);
                    todo.add(newListener);
                    res.put(succ, newListener);
        }

                //add the current as listener to the new
                newListener.addListener(current);
            }
        }

        return res;
    }

    private void propagateKnowledge(Map<OpCode, UpdateListener> listeners) {
        for (UpdateListener listener : listeners.values()) {
            if (listener.opCode instanceof Inc
                    || listener.opCode instanceof Load
                    || listener.opCode instanceof Ret) {
                listener.update(null, new HashSet<> ());
            }
                }
            }

    private CollectionMap<Integer, Integer> buildResult(Map<OpCode, UpdateListener> listeners) {
        CollectionMap<Integer, Integer> res = new CollectionMap<>();
        for (UpdateListener listener : listeners.values()) {
            res.add(listener.opCode.getPos(), listener.activeVars);
        }
        return res;
    }

    /**
     * Essentially this class is used to build a Syntax tree for static code analysis.
     * Each node of the tree itself is a listener that will register itself to its successors.
     * Thus knowledge can be propagated from the leafs to the root by simply informing the registered listeners that something changed.
     */
    private static class UpdateListener {
        /**
         * The OpCode of the listener
         */
        final OpCode opCode;
        /**
         * All vars found to be active at the OpCode
         */
        Set<Integer> activeVars = new HashSet<>();
        /**
         * registered listeners
         */
        List<UpdateListener> listeners = new ArrayList<>();

        UpdateListener(OpCode opCode) {
            this.opCode = opCode;
        }

        void addListener (UpdateListener listener) {
            listeners.add(listener);
        }

        void update(UpdateListener from, Set<Integer> newActive) {
            //update
            boolean changed = updateInternal(newActive);

            //check if we want to propagate
            if (changed) {
                for (UpdateListener listener : listeners) {
                    //propagate
                    listener.update(this, new LinkedHashSet<>(newActive));
                }
            }
        }

        private boolean updateInternal(Set<Integer> newActive) {
            if (opCode instanceof LocalVariableUser) {
                boolean load;
                boolean store;
                final int varNum = ((LocalVariableUser) opCode).getUsedLocalVariableIndex();
                if (opCode instanceof Inc) {
                    load = true;
                    store = true;
                } else if (opCode instanceof Store) {
                    load = false;
                    store = true;
                } else if (opCode instanceof Load || opCode instanceof Ret) {
                    load = true;
                    store = false;
                } else {
                    assert (false);
                    load = false;
                    store = false;
                }

                if (store) {
                    //We just define the variable, so we do not need information about it from the predecessors.
                    newActive.remove(varNum);
                }
                if (load) {
                    //We load a variable, so we need information about it from the previous opcodes.
                    newActive.add(varNum);
                }
            }
            return activeVars.addAll(newActive);
        }
    }
}
