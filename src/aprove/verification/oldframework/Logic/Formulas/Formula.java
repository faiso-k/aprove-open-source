package aprove.verification.oldframework.Logic.Formulas;

import java.io.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.LemmaDatabase.Index.*;
import aprove.verification.oldframework.Logic.Formulas.Visitors.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Basic abstract class for formulas
 * also contains basic algorithm for formula manipulation.*
 * @author Burak Emir, Eugen Yu
 */
public abstract class Formula implements TermOrFormula, Serializable, HTML_Able, LaTeX_Able, Exportable {

    /** @return all variables (also quantified ones)
     */
    final public Set<AlgebraVariable> getAllVariables() {
        return GetAllVariablesVisitor.apply(this);
    }

    /** Renames the variables in this term such according to
     *  a given FreshVarGenerator.
     *
     *  Note: This is a destructive method.
     *  @param fg FreshVarGenerator to use.
     */
    final public void renameVars(final FreshVarGenerator fg) {
        final RenameVarsVisitor v = new RenameVarsVisitor(fg);
        this.apply(v);
    }

    /** changes this formula such that it contains no variable
     *   from sv
     * @param sv is the set of variable that will not occur in this formula after this operation
     *  note: destructive
     */
    final public void renameAllVars(final Set<AlgebraVariable> sv) {
        if (sv.size() != 0) {
            final RenameAllVarsVisitor v = new RenameAllVarsVisitor(sv);
            this.apply(v);
        }
    }

    /** Same method as renameAllVars() but return the substitution used for
     *   renaming
     * @param sv is the set of variable that will not occur in this formula after renaming
     * @return substitution, a mapping of the renamed variables
     */
    final public AlgebraSubstitution renameAllVarsWithSubs(final Set<AlgebraVariable> sv) {
        if (sv.size() == 0) {
            return VarRenaming.create();
        }

        final Formula cp = this.deepcopy();
        this.renameAllVars(sv);

        AlgebraSubstitution subs = cp.matches(this);

        if (subs == null) {
            subs = AlgebraSubstitution.create();
        }

        return subs;
    }

    //method for visitor pattern
    public abstract <T> T apply(FineFormulaVisitor<T> fv);

    //method for visitor pattern
    public abstract <T> T apply(FineFormulaVisitorException<T> fv) throws InvalidPositionException;

    //method for visitor pattern
    public abstract <T> T apply(CoarseFormulaVisitor<T> cfv);

    //  method for visitor pattern
    public abstract <T> T apply(CoarseFormulaVisitorException<T> cfve) throws InvalidPositionException;

    //method  that should replace clone()
    //it returns a copy where all arguments will be copied as well
    public abstract Formula deepcopy();

    //method  that should replace clone();
    public abstract Formula shallowcopy();

    //This method is now forbidden
    @Override
    public Object clone() {
        throw new RuntimeException("clone deprecated -- use deepcopy / shallowcopy instead");
    }

    /**
     * Apply substitution to this formula, varaible with the same symbol will be substituted by a term.
      *@param sub is the substitution to be applie
     *@return the formula with the substituted terms
     */
    final public Formula apply(final AlgebraSubstitution sub) {
        return SubstitutionVisitor.apply(sub, this);
    }

    /**
     * This method is safe, just the output of a formula
     *@return a string that represent this formula
     */
    @Override
    public String toString() {
        return ToStringFormulaVisitor.apply(this);
    }

    //Static flags to identify the type of a quantifier
    protected static int NO_QUANTIFIER = 0;
    protected static int UNIVERSAL_QUATIFIER = 1;
    protected static int EXISTENTIAL_QUANTIFIER = 2;

    /** As above but with the deafult mode which is ONLY_ATOMIC_FORMULA
     * @return a set of positions, which can be used to fetch atomic subformulas
     */
    public Set<Position> getAllFormulaPositions() {
        return GetAllPositionsVisitor.apply(this);
    }

    /**
     *note: this method is safe
     *@param f is the formula to be matched
     *@return substition substitution such that this  formula  matches that formula
     */
    public AlgebraSubstitution matches(final Formula f) {
        try {
            final AlgebraSubstitution substitution = this.matchesWithIdentities(f, AlgebraSubstitution.create());
            for (final VariableSymbol variableSymbol : substitution.getDomain()) {
                if (substitution.get(variableSymbol).getSymbol().equals(variableSymbol)) {
                    substitution.remove(variableSymbol);
                }
            }
            return substitution;
        } catch (final UnificationException e) {
            return null;
        }
    }

    //    /**
    //     * note: this method is safe
    //     * @param that is the formula to be matched
    //     * @param sv is the setofvariables that will not be matched in this formula
    //     * @return substition substitution such that this  formula  matches that formula
    //     */
    //    public Substitution matchesWithForbiddenVars(Formula that, Set<Variable> sv) throws UnificationException{
    //       return matchesWithIdentities(that, VarRenaming.getIdentity(sv));
    //    }

    /**
     *note: this method is safe
     * @param that is the formula to be matched
     * @param subs is the substitution found so far
     * @return substition substitution such that this  formula  matches that formula
     */
    public abstract AlgebraSubstitution matchesWithIdentities(Formula that, AlgebraSubstitution subs) throws UnificationException;

    /**this method replace a subformula at a specified position of
     * this formula
     *note: This visitor is safe, but be aware that the resulting formula contains the subformula as a part
     *@param newSubformula is the new subformula replacing the old one
     *@param pos is the position of the subformula that should be replaced
     *@return a formula with the specified subformula replaced
     */
    public Formula replaceFormulaAt(final Formula newSubformula, final Position position)
        throws InvalidPositionException
    {
        try {
            return ReplaceSubFormulaOrSubTermVisitor.apply(this, newSubformula, position);
        } catch (final Exception e) {
            throw new InvalidPositionException(position, e.getMessage());
        }
    }

    /**This method get the a subterm according to the position
     * first part of position is used for finding an equation,
     * next integer decide left (0) or right(1) part of this eq
     * the rest is used to fetch a subterm from a term
     *note: this is potentailly unsafe, change of resulting term will affect this formula
     *@param p is the position of the term
     *@return the term at the specific position
     */
    @Override
    public TermOrFormula getSubPart(final Position p) throws InvalidPositionException {

        final TermOrFormula returnValue = SubPartVisitor.apply(this, p);

        if (returnValue == null) {
            throw new InvalidPositionException(p, "Position not contained in formula.");
        } else {
            return returnValue;
        }

    }

    /** given a term and a valid position
     * this method replace the term of the specified position with
     * the new term
     * note: safe, because replaceFormula is safe as well, but beware that t is a part of this formula
     * @param t is the term to replace
     * @return a formula where the term at position p is replaced by t
     */
    public Formula replaceTermAt(final AlgebraTerm t, final Position p) throws InvalidPositionException {
        try {
            return ReplaceSubFormulaOrSubTermVisitor.apply(this, t, p);
        } catch (final Exception e) {
            throw new InvalidPositionException(p, e.getMessage());
        }
    }

    /**
     * produces a new formula where all occurrences of the
     * FIND-term are replaced by the REPLACE term
     * @param find the term to be found
     * @param replace the term to be inserted instead
     * @return a new formula
     */
    final public Formula replaceTermByTerm(final AlgebraTerm find, final AlgebraTerm replace) {
        final Formula newFormula = FormulaReplaceTermByTerm.apply(this, find, replace);
        return newFormula;
    }

    /**
     * Check if symbolic evaluation is applicable
     * @param ev
     * @return true if formula can be evaluated
     */
    public boolean evaluable(final Evaluator ev) {
        return EvaluableVisitor.applyTo(this, ev);
    }

    /**
     * For simplicity reasons all for Formulas with the same string representation
     * should have the same hash code. Should be substituted by a better hashCode in
     * a later version.
     */
    @Override
    final public int hashCode() {
        return 200;
    }

    /**
     * Converts formula to a html string
     * @return Formula as a html string
     */
    @Override
    final public String toHTML() {
        return ToHTMLFormulaVisitor.apply(this);
    }

    final public String toHTML(final Set<VariableSymbol> allquantifiedVariables) {
        return ToHTMLFormulaVisitor.apply(this, allquantifiedVariables);
    }

    /**
     * Converts formula to ascii string
     * @return Formula as a ascii string
     */
    final public String toASCII() {
        return ToASCIIFormulaVisitor.apply(this);
    }

    final public String toASCII(final Set<VariableSymbol> allquantifiedVariables) {
        return ToASCIIFormulaVisitor.apply(this, allquantifiedVariables);
    }

    /**
     * converts to latex string
     * @return Formula as latex string
     */
    @Override
    final public String toLaTeX() {
        return ToLaTeXVisitor.apply(this);
    }

    /**
     * converts a formula to a latex string and
     * quantifies the given variables
     * @return Formula as a latex string
     */
    final public String toLatex(final Set<VariableSymbol> allquantifiedVariables) {
        return ToLaTeXVisitor.apply(this, allquantifiedVariables);
    }

    public abstract boolean isAtomic();

    public abstract boolean isEquation();

    public abstract boolean isImplication();

    public Map<TermOrFormula, List<Position>> getAllSubFormulasAndTermsWithPosition() {
        return GetAllSubFormulasAndTermsWithPositionVisitor.apply(this);
    }

    public List<Equation> getAllEquations() {
        return GetAllEquationsVisitor.applyTo(this);
    }

    public Map<Equation, List<Position>> getEquationsWithPositions() {
        return GetAllSubPartsOfClassWithPosition.apply(this, Equation.class);
    }

    public Map<Implication, List<Position>> getImplicationsWithPositions() {
        return GetAllSubPartsOfClassWithPosition.apply(this, Implication.class);
    }

    @Override
    public boolean isFormula() {
        return true;
    }

    @Override
    public boolean isTerm() {
        return false;
    }

    public Set<Position> getAllModifiablePositions(final Program program) {
        return GetAllModifiablePositionsVisitor.apply(this, program);
    }

    /**
     *
     */
    public Formula normalise() {
        return NormalisingVisitor.apply(this);
    }

    public List<IndexSymbol> getRepresentationString() {
        return GetRepresentationStringVisitor.apply(this);
    }

    public Set<DefFunctionSymbol> getAllDefFunctionSymbols() {
        return GetAllFunctionSymbolsVisitor.apply(this);
    }

    public Set<AlgebraTerm> getAllSubTerms() {
        return GetAllSubTermsVisitor.apply(this);
    }

    public Set<VariableSymbol> getAllVariableSymbols() {
        return GetAllVariableSymbolsVisitor.apply(this);
    }

    public int getSize() {
        return FormulaSizeVisitor.apply(this);
    }

    public Formula erase() {
        return EraseAnnotatedFormulaVisitor.apply(this);
    }

    @Override
    public String export(final Export_Util o) {
        if (o instanceof HTML_Util) {
            return this.toHTML();
        }
        if (o instanceof LaTeX_Util) {
            return this.toLaTeX();
        }
        if (o instanceof PLAIN_Util) {
            return this.toString();
        }

        throw new RuntimeException("Unknown Export_Util");
    }

    public void toACL2(
        final StringBuffer sb,
        final int indent,
        final FreshNameGenerator fng,
        final boolean fullLists,
        final boolean noGeneralize)
    {
        ToACL2FormulaVisitor.apply(this, sb, indent, fng, fullLists, noGeneralize);
    }
}
