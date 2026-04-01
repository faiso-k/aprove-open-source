package aprove.input.Programs.prolog.structure;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * A PrologAbstractVariable is a special form of a PrologVariable used in
 * partial evalutation trees. Those variables can be instantiated by any
 * PrologTerm including variables (also other abstract variables). In
 * addition to that, abstract variables can be restricted to ground terms.
 * Then they cannot be instantiated by normal PrologVariables, but still
 * by abstract variables which have the same restriction.<br><br>
 *
 * Created: Dec 1, 2006<br>
 * Last modified: Dec 1, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public class PrologAbstractVariable extends PrologVariable {

    /**
     * Constructs a new PrologAbstractVariable with the specified name.
     * @param name The variable's name.
     */
    public PrologAbstractVariable(final String name) {
        super(name);
    }

    @Override
    public PrologTerm convertAbstractToNonAbstractVariables() {
        return new PrologNonAbstractVariable(this.getName());
    }

    @Override
    public Set<PrologAbstractVariable> createSetOfAllAbstractVariables() {
        final Set<PrologAbstractVariable> res = new LinkedHashSet<PrologAbstractVariable>();
        res.add(this);
        return res;
    }

    @Override
    public int hashCode() {
        return 19 * this.getName().hashCode();
    }

    @Override
    public boolean isAbstractVariable() {
        return true;
    }

    @Override
    public boolean isConstructorTerm(final Set<FunctionSymbol> preds) {
        return false;
    }

    @Override
    public PrologTerm rename(final String oldName, final String newName, final int arity) {
        if (arity == 0 && this.getName().equals(oldName)) {
            return new PrologAbstractVariable(newName);
        } else {
            return this;
        }
    }

    @Override
    public PrologTerm replaceName(final String name) {
        return new PrologAbstractVariable(name);
    }

    @Override
    public ITerm<BigInt> toComparisonTerm(final boolean negate, final IDPPredefinedMap pd) {
        throw new IllegalArgumentException("Arithmetic comparison must have a determined functor!");
    }

    @Override
    public ITerm<BigInt> toEvaluationTerm(final IDPPredefinedMap pd) {
        return ITerm.createVariable(this.getName(), DomainFactory.INTEGERS);
    }

    @Override
    public String toLaTeX(final KnowledgeBase kb) {
        final StringBuilder res = new StringBuilder();
        final boolean ground = kb.isGround(this);
        if (ground) {
            res.append("\\overline{");
        }
        if ("T".equals(this.getName())) {
            res.append("T");
        } else if (this.getName().startsWith("T")) {
            res.append("T_{");
            res.append(this.getName().substring(1));
            res.append("}");
        } else {
            res.append("\\mathit{");
            res.append(this.getName());
            res.append("}");
        }
        if (ground) {
            res.append("}");
        }
        return res.toString();
    }

    @Override
    protected boolean equalsVariable(final PrologVariable v) {
        return v instanceof PrologAbstractVariable;
    }

}
