package aprove.verification.idpframework.Core.Itpf;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class ItpfPolyAtom<C extends SemiRing<C>> extends ItpfAtom.ItpfAtomSkeleton {

    /**
     * Encodes the type of constraint we are dealing with: Is the
     * (Simple/Var/...) Polynomial on the LHS equal to/greater or equal/greater
     * than 0?
     * @author Carsten Fuhs
     * @version $Id$
     */
    public static enum ConstraintType implements Exportable, XmlExportable {
        EQ, GE, GT;

        private ConstraintType() {
        }

        @Override
        public final String toString() {
            return this.export(new PLAIN_Util());
        }

        @Override
        public final String export(final Export_Util o) {
            return this.export(o, false);
        }

        public final String export(final Export_Util o, final boolean negated) {
            if (negated) {
                switch (this) {
                case EQ:
                    return o.notSign() + o.eqSign();
                case GE:
                    return o.ltSign();
                case GT:
                    return o.leSign();
                default:
                    throw new UnsupportedOperationException(
                        "Unknown relation type" + this);
                }
            } else {
                switch (this) {
                case EQ:
                    return o.eqSign();
                case GE:
                    return o.geSign();
                case GT:
                    return o.gtSign();
                default:
                    throw new UnsupportedOperationException(
                        "Unknown relation type" + this);
                }
            }
        }

        @Override
        public Map<String, String> getXmlAttribs(final XmlExporter xe) {
            final Map<String, String> m = new HashMap<String, String>();
            m.put("value", this.toString());
            return m;
        }

        @Override
        public XmlContentsMap getXmlContents(final XmlExporter xe) {
            return null;
        }

        public Func getFunction() {
            switch (this) {
            case EQ:
                return Func.Eq;
            case GE:
                return Func.Ge;
            case GT:
                return Func.Gt;
            default:
                throw new UnsupportedOperationException(
                    "Unknown relation type" + this);
            }
        }
    }

    static <C extends SemiRing<C>> ItpfPolyAtom<C> create(final Polynomial<C> poly,
        final ConstraintType constraintType,
        final PolyInterpretation<C> interpretation) {
        return new ItpfPolyAtom<C>(poly, constraintType, interpretation);
    }

    private final Polynomial<C> poly;
    private final ConstraintType constraintType;

    private final PolyInterpretation<C> interpretation;
    private final int hashCode;

    private ItpfPolyAtom(final Polynomial<C> poly,
            final ConstraintType constraintType,
            final PolyInterpretation<C> interpretation) {
        this.poly = poly;
        this.constraintType = constraintType;
        this.interpretation = interpretation;
        final int prime = 31;
        {
            int hash = 1;
            hash = prime * hash + constraintType.hashCode();
            hash = prime * hash + interpretation.hashCode();
            hash = prime * hash + poly.hashCode();
            this.hashCode = hash;
        }
    }

    @Override
    public ItpfPolyAtom<C> applySubstitution(final PolyTermSubstitution sigma) {
        final Polynomial<C> newPoly = this.poly.applySubstitution(sigma);
        if (this.poly != newPoly) {
            return this.interpretation.getConstraintFactory().createPoly(newPoly,
                this.getConstraintType(), this.interpretation);
        } else {
            return this;
        }
    }

    public PolyInterpretation<C> getInterpretation() {
        return this.interpretation;
    }

    @Override
    public void collectFunctionSymbols(final Set<IFunctionSymbol<?>> fss) {
        // nothing to do here
    }

    @Override
    public void collectExecutionMarks(final Map<ExecutionUid, ExecutionMarkable> executionMarks) {
        this.executionMarksHandler.collectExecutionMarks(executionMarks);
    }

    @Override
    public void collectVariables(final Set<IVariable<?>> vars) {
        vars.addAll(this.poly.getVariables());
    }

    @Override
    public void collectNodes(final Set<ImmutablePair<INode, ImmutableTermSubstitution>> nds) {
        // nothing to do here
    }

    @Override
    public void collectTerms(final Set<ITerm<?>> terms, final boolean dropVars) {
        if (!dropVars) {
            terms.addAll(this.poly.getVariables());
        }
    }

    @Override
    public boolean isPoly() {
        return true;
    }

    @Override
    public YNM isTrivial() {
        if (this.poly.isConstant()) {
            boolean satisfied;
            if (this.constraintType == ConstraintType.GT) {
                satisfied = this.poly.getConstantValue().semiCompareTo(this.poly.getRing().zero()) > 0;
            } else if (this.constraintType == ConstraintType.GE) {
                satisfied = this.poly.getConstantValue().semiCompareTo(this.poly.getRing().zero()) >= 0;
            } else if (this.constraintType == ConstraintType.EQ) {
                satisfied = this.poly.getConstantValue().equals(this.poly.getRing().zero());
            } else {
                throw new UnsupportedOperationException("unknown constraint type");
            }

            if (satisfied) {
                return YNM.YES;
            } else {
                return YNM.NO;
            }
        } else {
            return YNM.MAYBE;
        }
    }

    public Polynomial<C> getPoly() {
        return this.poly;
    }

    public ConstraintType getConstraintType() {
        return this.constraintType;
    }

    public Disjunction<ItpfPolyAtom<C>> negate() {
        switch (this.constraintType) {
        case EQ :
            final Set<ItpfPolyAtom<C>> disjunction = new LinkedHashSet<ItpfPolyAtom<C>>();
            disjunction.add(this.interpretation.getConstraintFactory().createPoly(this.poly, ConstraintType.GT, this.interpretation));
            disjunction.add(this.interpretation.getConstraintFactory().createPoly(this.poly.negate(), ConstraintType.GT, this.interpretation));
            return new Disjunction<ItpfPolyAtom<C>>(ImmutableCreator.create(disjunction));
        case GE :
            return new Disjunction<ItpfPolyAtom<C>>(this.interpretation.getConstraintFactory().createPoly(this.poly.negate(), ConstraintType.GT, this.interpretation));
        case GT :
            return new Disjunction<ItpfPolyAtom<C>>(this.interpretation.getConstraintFactory().createPoly(this.poly.negate(), ConstraintType.GE, this.interpretation));
        }
        throw new UnsupportedOperationException("unknown constraint type");
    }

    @Override
    public ItpfAtom replaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        return this;
    }

    @Override
    public void export(final boolean negated,
        final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel, final ExecutionStepColorization colors) {
        sb.append("P: ");
        sb.append(this.getPoly().export(o));
        sb.append(" ");
        sb.append(this.getConstraintType().export(o, negated));
        sb.append(" ");
        sb.append(this.interpretation.getFactory().zero(this.poly.getRing()).export(o));
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        return null;
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        final XmlContentsMap contents = new XmlContentsMap();
        contents.add("left", this.getPoly());
        contents.add(this.getConstraintType());
        contents.add("right", this.interpretation.getFactory().zero(this.poly.getRing()));
        return contents;
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
        if (!(obj instanceof ItpfPolyAtom<?>)) {
            return false;
        }
        final ItpfPolyAtom<?> other = (ItpfPolyAtom<?>) obj;
        return other.getConstraintType().equals(this.getConstraintType())
            && other.interpretation.equals(this.interpretation)
            && other.getPoly().equals(this.getPoly());
    }
}
