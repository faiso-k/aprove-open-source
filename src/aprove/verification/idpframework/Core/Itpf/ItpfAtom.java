/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Core.Itpf;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public interface ItpfAtom extends Exportable, XmlExportable, IDPExportable,
        Markable<Disjunction<ItpfAtomReplaceData>, ItpfAtom, ItpfAtomReplaceData>,
        HasVariables<IVariable<?>>,
        ExecutionMarkable {

    public ItpfAtom applySubstitution(PolyTermSubstitution sigma);

    public void collectFunctionSymbols(Set<IFunctionSymbol<?>> fss);

    public void collectVariables(Set<IVariable<?>> vars);

    public void collectNodes(Set<ImmutablePair<INode, ImmutableTermSubstitution>> nds);

    public void collectTerms(Set<ITerm<?>> terms, boolean drovVars);

    public Set<ITerm<?>> getTerms(boolean dropVars);

    public boolean isItp();

    public boolean isNodeUra();

    public boolean isTermUra();

    public boolean isEdgeUra();

    public boolean isPoly();

    public boolean isBoolPolyVar();

    public boolean isEdgeOrientation();

    @Deprecated
    public boolean isLogVar();

    public boolean isImplication();

    public YNM isTrivial();

    public void export(boolean negated,
        StringBuilder sb,
        Export_Util o,
        VerbosityLevel verbosityLevel,
        ExecutionStepColorization colors);

    public ItpfAtom replaceAllFunctionSymbols(FunctionSymbolReplacement replaceMap);

    public static abstract class ItpfAtomSkeleton extends ExecutionExportable.ExecutionExportableSkeleton implements ItpfAtom {

        private final MarksHandler<Disjunction<ItpfAtomReplaceData>, ItpfAtom, ItpfAtomReplaceData> marksHanlder;
        protected final ExecutionMarksHandler executionMarksHandler;

        public ItpfAtomSkeleton() {
            this.marksHanlder = new MarksHandler<Disjunction<ItpfAtomReplaceData>, ItpfAtom, ItpfAtomReplaceData>(this);
            this.executionMarksHandler = new ExecutionMarksHandler(this);
        }

        @Override
        public MarksHandler<Disjunction<ItpfAtomReplaceData>, ItpfAtom, ItpfAtomReplaceData> getMarks() {
            return this.marksHanlder;
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
        public Set<IVariable<?>> getVariables() {
            final Set<IVariable<?>> res = new LinkedHashSet<IVariable<?>>();
            this.collectVariables(res);
            return res;
        }

        @Override
        public Set<ITerm<?>> getTerms(final boolean dropVars) {
            final Set<ITerm<?>> res = new LinkedHashSet<ITerm<?>>();
            this.collectTerms(res, dropVars);
            return res;
        }


        @Override
        public boolean isItp() {
            return false;
        }

        @Override
        public boolean isNodeUra() {
            return false;
        }

        @Override
        public boolean isEdgeUra() {
            return false;
        }

        @Override
        public boolean isTermUra() {
            return false;
        }

        @Override
        public boolean isPoly() {
            return false;
        }

        @Override
        public boolean isBoolPolyVar() {
            return false;
        }

        @Override
        public boolean isEdgeOrientation() {
            return false;
        }

        @Override
        public boolean isLogVar() {
            return false;
        }

        @Override
        public boolean isImplication() {
            return false;
        }

        @Override
        public void export(final StringBuilder sb,
            final Export_Util o,
            final VerbosityLevel verbosityLevel,
            final ExecutionStepColorization colors) {
            this.export(false, sb, o, verbosityLevel, colors);
        }

    }


}
