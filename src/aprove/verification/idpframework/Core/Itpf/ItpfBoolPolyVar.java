package aprove.verification.idpframework.Core.Itpf;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class ItpfBoolPolyVar<C extends SemiRing<C>> extends ItpfAtom.ItpfAtomSkeleton {

    static <C extends SemiRing<C>> ItpfBoolPolyVar<C> create(final IVariable<C> var, final PolyInterpretation<C> interpretation, final ItpfFactory factory) {
        return new ItpfBoolPolyVar<C>(var, interpretation, factory);
    }

    private final IVariable<C> var;
    private final ItpfFactory factory;
    private final PolyInterpretation<C> interpretation;
    private int hashCode;

    private ItpfBoolPolyVar(final IVariable<C> var, final PolyInterpretation<C> interpretation, final ItpfFactory factory) {
        if (Globals.useAssertions) {
            assert (var.getDomain() != null);
            assert (var.getDomain().isSemiRingDomain());
            final SemiRingDomain<C> varRange = var.getDomain();
            assert varRange.isBoolRange();
        }
        this.var = var;
        this.interpretation = interpretation;
        this.factory = factory;

        {
            final int prime = 31;
            int result = 1;
            result = prime * result + interpretation.hashCode();
            this.hashCode = prime * result + var.hashCode();
        }
    }

    public IVariable<C> getPolyVar() {
        return this.var;
    }

    public ItpfFactory getFactory() {
        return this.factory;
    }

    @Override
    public ItpfAtom applySubstitution(final PolyTermSubstitution sigma) {
        final Polynomial<C> substituted = (sigma).substitutePoly(this.var);
        if (substituted == null) {
            return this;
        }

        if (substituted.isRealVariable()) {
            final IVariable<C> substitutedVar = substituted.getRealVariable();
            return this.factory.createBoolPolyVar(substitutedVar, this.interpretation);
        } else {
            return this.factory.createPoly(substituted.subtract(this.interpretation.getFactory().one(this.var.getDomain().getRing())), ConstraintType.EQ, this.interpretation);
        }
    }

    @Override
    public void collectExecutionMarks(final Map<ExecutionUid, ExecutionMarkable> executionMarks) {
        this.executionMarksHandler.collectExecutionMarks(executionMarks);
    }

    @Override
    public void collectFunctionSymbols(final Set<IFunctionSymbol<?>> fss) {
    }

    @Override
    public void collectVariables(final Set<IVariable<?>> vars) {
        vars.add(this.var);
    }

    @Override
    public void collectNodes(final Set<ImmutablePair<INode, ImmutableTermSubstitution>> nds) {
        // nothing to do here
    }

    @Override
    public void collectTerms(final Set<ITerm<?>> terms, final boolean dropVars) {
        if (!dropVars) {
            terms.add(this.var);
        }
    }

    @Override
    public void export(final boolean negated,
        final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel, final ExecutionStepColorization colors) {
        if (negated) {
            sb.append("!");
        }
        this.var.export(sb, o, verbosityLevel);
    }

    @Override
    public Map<String, String> getXmlAttribs(XmlExporter xe) {
        Map<String, String> m = new HashMap<String, String>();
        return m;
    }

    @Override
    public XmlContentsMap getXmlContents(XmlExporter xe) {
        XmlContentsMap contents = new XmlContentsMap();
        contents.add(this.var);
        return contents;
    }

    @Override
    public boolean isBoolPolyVar() {
        return true;
    }

    @Override
    public YNM isTrivial() {
        return YNM.MAYBE;
    }

    @Override
    public ItpfAtom replaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        return this;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final ItpfBoolPolyVar<?> other = (ItpfBoolPolyVar<?>) obj;
        return this.var.equals(other.var) && this.interpretation.equals(other.interpretation);
    }

}
