package aprove.input.Programs.prolog.structure;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.SemiRings.*;

/**
 * NonAbstractVariable.<br><br>
 *
 * Created: May 23, 2007<br>
 * Last modified: May 23, 2007
 *
 * @author cryingshadow
 * @version $Id$
 */
public class PrologNonAbstractVariable extends PrologVariable {

    /**
     * Constructs a new PrologVariable with the specified name.
     * @param name The variable's name.
     */
    public PrologNonAbstractVariable(final String name) {
        super(name);
    }

    @Override
    public boolean containsNonAbstractVariable() {
        return true;
    }

    @Override
    public Set<PrologNonAbstractVariable> createSetOfAllNonAbstractVariables() {
        final Set<PrologNonAbstractVariable> res = new LinkedHashSet<PrologNonAbstractVariable>();
        res.add(this);
        return res;
    }

    @Override
    public int hashCode() {
        return 13 * this.getName().hashCode();
    }

    @Override
    public boolean isNonAbstractVariable() {
        return true;
    }

    @Override
    public boolean isUnderscore() {
        return "_".equals(this.getName());
    }

    @Override
    public PrologTerm rename(final String oldName, final String newName, final int arity) {
        if (arity == 0 && this.getName().equals(oldName)) {
            return new PrologNonAbstractVariable(newName);
        } else {
            return this;
        }
    }

    @Override
    public PrologTerm renameNonAbstractVariablesCanonically(
        final Map<PrologNonAbstractVariable, PrologNonAbstractVariable> renaming)
    {
        if (!renaming.containsKey(this)) {
            renaming.put(this, new PrologNonAbstractVariable("X" + (renaming.size() + 1)));
        }
        return renaming.get(this);
    }

    @Override
    public PrologTerm replaceName(final String name) {
        return new PrologNonAbstractVariable(name);
    }

    @Override
    public ITerm<BigInt> toComparisonTerm(final boolean negate, final IDPPredefinedMap pd) {
        throw new IllegalArgumentException("Arithmetic expressions may not contain non-abstract variables!");
    }

    @Override
    public ITerm<BigInt> toEvaluationTerm(final IDPPredefinedMap pd) {
        throw new IllegalArgumentException("Arithmetic expressions may not contain non-abstract variables!");
    }

    @Override
    public String toLaTeX(final KnowledgeBase kb) {
        if ("X".equals(this.getName())) {
            return "X";
        }
        if (this.getName().startsWith("X")) {
            return "X_{" + this.getName().substring(1) + "}";
        }
        return "\\mathit{" + this.getName() + "}";
    }

    @Override
    protected boolean equalsVariable(final PrologVariable v) {
        return v instanceof PrologNonAbstractVariable;
    }

}
