package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import immutables.*;

/**
 *
 * @author MP
 */
public interface ItpfAtomReplaceData extends MarkContent<Disjunction<Map.Entry<ItpfAtom, Boolean>>, Map.Entry<ItpfAtom, Boolean>>, ExecutionMarkable {

    public ImmutableSet<ITerm<?>> getS();

    public static class LiteralMapData implements ItpfAtomReplaceData {

        private final ImmutableMap<ItpfAtom, Boolean> literals;
        private final ImmutableSet<ITerm<?>> addToS;

        private final ExecutionMarksHandler executionMarksHandler;

        public LiteralMapData (final LiteralMap literals, final ImmutableSet<ITerm<?>> addToS) {
            if (Globals.useAssertions) {
                assert !literals.isUnsatisfiable() : "catch unsatisfiability";
            }
            this.literals = ImmutableCreator.create(literals);
            this.addToS = addToS;
            this.executionMarksHandler = new ExecutionMarksHandler(this);
        }

        @Override
        public boolean isEmpty() {
            return this.literals.isEmpty();
        }

        @Override
        public int size() {
            return this.literals.size();
        }

        @Override
        public ImmutableCollection<Entry<ItpfAtom, Boolean>> asCollection() {
            return ImmutableCreator.create(this.literals.entrySet());
        }

        @Override
        public boolean isSingleton(final Entry<ItpfAtom, Boolean> content) {
            return this.literals.size() == 1;
        }

        @Override
        public Iterator<Entry<ItpfAtom, Boolean>> iterator() {
            return this.literals.entrySet().iterator();
        }

        @Override
        public void addExecutionMark(final ExecutionUid mark) {
            this.executionMarksHandler.addExecutionMark(mark);
        }

        @Override
        public boolean isExecutionMarked(final ExecutionUid mark) {
            return this.executionMarksHandler.isExecutionMarked(mark);
        }

        @Override
        public Set<ExecutionUid> getExecutionMarks() {
            return this.executionMarksHandler.getExecutionMarks();
        }

        @Override
        public void collectExecutionMarks(final Map<ExecutionUid, ExecutionMarkable> executionMarks) {
            this.executionMarksHandler.collectExecutionMarks(executionMarks);
        }

        @Override
        public ImmutableSet<ITerm<?>> getS() {
            return this.addToS;
        }

    }

}