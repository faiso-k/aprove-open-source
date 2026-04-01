package aprove.input.Programs.prolog.structure;

import java.util.*;

import org.json.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

/**
 * Class representing a clause in Prolog.<br><br>
 * If the clause is a fact, it consists of a head term only. Otherwise
 * it consists of a head and a body term.<br><br>
 *
 * Created: Sep 8, 2006<br>
 * Last modified: Aug 19, 2015
 *
 * @author cryingshadow
 * @version $Id$
 */
public class PrologClause implements Exportable, PrettyStringable, Immutable, JSONExport {

    private final PrologTerm body;

    private final PrologTerm head;

    /**
     * Constructs a new PrologClause with the specified head and body
     * terms.
     * @param h The head term for the clause.
     * @param b The body term for the clause.
     * @throws NullPointerException If the head term is null.
     */
    public PrologClause(final PrologTerm h, final PrologTerm b) throws NullPointerException {
        if (h == null) {
            throw new NullPointerException("Head must not be null!");
        }
        this.head = h;
        this.body = b;
    }

    public Map<PrologNonAbstractVariable, PrologNonAbstractVariable> computeNonAbstractVarNameRefreshment(
        final FreshNameGenerator fridge)
    {
        final Set<PrologNonAbstractVariable> vars = this.getHead().createSetOfAllNonAbstractVariables();
        if (this.getBody() != null) {
            vars.addAll(this.getBody().createSetOfAllNonAbstractVariables());
        }
        final Map<PrologNonAbstractVariable, PrologNonAbstractVariable> res =
            new LinkedHashMap<PrologNonAbstractVariable, PrologNonAbstractVariable>();
        for (final PrologNonAbstractVariable v : vars) {
            res.put(v, new PrologNonAbstractVariable(fridge.getFreshName("X", false)));
        }
        return res;
    }

    public boolean containsCut() {
        return this.getBody() == null ? false : this.getBody().containsCut();
    }

    public PrologClause convertAbstractToNonAbstractVariables() {
        return new PrologClause(this.getHead().convertAbstractToNonAbstractVariables(), this.isFact() ? null : this
            .getBody()
            .convertAbstractToNonAbstractVariables());
    }

    /**
     * Creates a new FunctionSymbol out of the clauses head term. The
     * FunctionSymbol has the name and arity of the clauses head term.
     * @return A new FunctionSymbol representing the clauses head term.
     */
    public FunctionSymbol createFunctionSymbol() {
        return this.getHead().createFunctionSymbol();
    }

    public Set<String> createSetOfAllFunctionSymbolNames() {
        final Set<String> res = new LinkedHashSet<String>();
        this.walkAll(new TermWalker() {

            @Override
            public boolean goDeeper(final PrologTerm term) {
                return true;
            }

            @Override
            public boolean isApplicable(final PrologTerm term) {
                return !term.isVariable();
            }

            @Override
            public void performAction(final PrologTerm term) {
                res.add(term.getName());
            }

        });
        return res;
    }

    /**
     * Returns a set of all FunctionSymbols used in this clause. That
     * means that for every different predicate and every different
     * constructor symbol a FunctionSymbol is created and added to this
     * set.
     * @return A set of all FunctionSymbols used in this clause.
     */
    public Set<FunctionSymbol> createSetOfAllFunctionSymbols() {
        final Set<FunctionSymbol> res = new LinkedHashSet<FunctionSymbol>();
        this.walkAll(new TermWalker() {

            @Override
            public boolean goDeeper(final PrologTerm term) {
                return true;
            }

            @Override
            public boolean isApplicable(final PrologTerm term) {
                return !term.isVariable();
            }

            @Override
            public void performAction(final PrologTerm term) {
                res.add(term.createFunctionSymbol());
            }

        });
        return res;
    }

    /**
     * @return
     */
    public Set<FunctionSymbol> createSetOfAllPredicates() {
        final Set<FunctionSymbol> res = new LinkedHashSet<FunctionSymbol>();
        res.add(this.getHead().createFunctionSymbol());
        this.walkBody(new TermWalker() {

            @Override
            public boolean goDeeper(final PrologTerm term) {
                return term.isGoalJunctor();
            }

            @Override
            public boolean isApplicable(final PrologTerm term) {
                return !term.isVariable() && !term.isConjunction();
            }

            @Override
            public void performAction(final PrologTerm term) {
                res.add(term.createFunctionSymbol());
            }

        });
        return res;
    }

    /**
     * @return
     */
    public Set<String> createSetOfAllSymbolNames() {
        final NameWalker walker = new NameWalker();
        this.getHead().walk(walker);
        if (this.getBody() != null) {
            this.getBody().walk(walker);
        }
        return walker.getResult();
    }

    public Set<String> createSetOfAllVariableNames() {
        final Set<String> res = new LinkedHashSet<String>();
        for (final PrologVariable v : this.createSetOfAllVariables()) {
            res.add(v.getName());
        }
        return res;
    }

    /**
     * Creates a new set containing all variables used in this clause.
     * @return A new set containing all variables used in this clause.
     */
    public Set<PrologVariable> createSetOfAllVariables() {
        final Set<PrologVariable> res = new LinkedHashSet<PrologVariable>();
        res.addAll(this.getHead().createSetOfAllVariables());
        if (this.getBody() != null) {
            res.addAll(this.getBody().createSetOfAllVariables());
        }
        return res;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(final Object o) {
        if (o instanceof PrologClause) {
            final PrologClause c = (PrologClause) o;
            return this.hashCode() == c.hashCode()
                && (this.isFact() ? c.isFact() && this.getHead().equals(c.getHead()) : this.getHead().equals(
                    c.getHead())
                    && this.getBody().equals(c.getBody()));
        }
        return false;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Utility.Exportable#export(aprove.verification.oldframework.Utility.Export_Util)
     */
    @Override
    public String export(final Export_Util o) {
        if (this.getBody() == null) {
            return this.getHead().export(o);
        }
        final StringBuilder res = new StringBuilder();
        res.append(this.getHead().export(o));
        res.append(o.appSpace());
        res.append(o.export(":-"));
        res.append(o.appSpace());
        res.append(this.getBody().export(o));
        return res.toString();
    }

    public String export(final Export_Util o, final Set<FunctionSymbol> preds) {
        if (this.getBody() == null) {
            return this.getHead().export(o, preds);
        }
        final StringBuilder res = new StringBuilder();
        res.append(this.getHead().export(o, preds));
        res.append(o.appSpace());
        res.append(o.export(":-"));
        res.append(o.appSpace());
        res.append(this.getBody().export(o, preds));
        return res.toString();
    }

    public PrologClause flattenOutConjunctions() {
        return new PrologClause(this.getHead(), this.isFact() ? null : this.getBody().flattenOutConjunctions());
    }

    /**
     * Returns the body term of this clause. May be null (see isFact()).
     * @return The body term of this clause.
     * @see PrologClause.isFact()
     */
    public PrologTerm getBody() {
        return this.body;
    }

    /**
     * Returns the head term of this clause.
     * @return The head term of this clause.
     */
    public PrologTerm getHead() {
        return this.head;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return 3 * this.getHead().hashCode() + (this.getBody() == null ? 0 : 5 * this.getBody().hashCode());
    }

    /**
     * Tests whether or not this clause is a fact, i.e. it has no body.
     * @return True, if this clause is a fact. False otherwise.
     */
    public boolean isFact() {
        return this.getBody() == null;
    }

    /**
     * Tests whether or not this clause is compatible to a logic program.
     * This means the clause has to consist of an atom on the left side
     * and a list of atoms on the right side.
     * @return True, if this clause is logic program compatible.
     *         False otherwise.
     */
    public boolean isLogicProgramCompatible(final Set<FunctionSymbol> preds) {
        return this.getHead().isAtom(preds)
            && (this.getBody() == null || this.getBody().isConjunctionListOfAtoms(preds));
    }

    public PrologClause nonAbstractVariablesRefreshed(final FreshNameGenerator fridge) {
        final Map<PrologNonAbstractVariable, PrologNonAbstractVariable> rho =
            this.computeNonAbstractVarNameRefreshment(fridge);
        return new PrologClause(this.getHead().applySubstitution(rho), this.isFact() ? null : this
            .getBody()
            .applySubstitution(rho));
    }

    @Override
    public String prettyToString() {
        if (this.getBody() == null) {
            return this.getHead().prettyToString();
        }
        return this.getHead().prettyToString() + " :- " + this.getBody().prettyToString();
    }

    /**
     * Renames all terms in this body which have the specified name and
     * arity to the specified freshName.
     * @param name The name of the terms to be renamed.
     * @param arity The arity of the terms to be renamed.
     * @param freshName The new name.
     */
    public PrologClause rename(final String name, final int arity, final String freshName) {
        return new PrologClause(this.getHead().rename(name, freshName, arity), this.getBody() == null ? null : this
            .getBody()
            .rename(name, freshName, arity));
    }

    public PrologClause renameNonAbstractVariablesCanonically() {
        final Map<PrologNonAbstractVariable, PrologNonAbstractVariable> renaming =
            new LinkedHashMap<PrologNonAbstractVariable, PrologNonAbstractVariable>();
        return new PrologClause(this.getHead().renameNonAbstractVariablesCanonically(renaming), this.isFact()
            ? null
                : this.getBody().renameNonAbstractVariablesCanonically(renaming));
    }

    /**
     * Replaces all occurences of oldTerm in this PrologClause with
     * newTerm. If oldTerm is a subterm of newTerm, occurences of
     * oldTerm in already replaced terms will not be replaced, because
     * the replacement would not terminate then.
     * @param oldTerm The term to be replaced.
     * @param newTerm The term to replace.
     * @return The PrologClause where oldTerm has been replaced by newTerm.
     */
    public PrologClause replaceAll(final PrologTerm oldTerm, final PrologTerm newTerm) {
        return new PrologClause(this.getHead().replaceAll(oldTerm, newTerm), this.isFact() ? null : this
            .getBody()
            .replaceAll(oldTerm, newTerm));
    }

    /**
     * Replaces all occurences of oldTerm in the body of this
     * PrologClause with newTerm. If oldTerm is a subterm of newTerm,
     * occurences of oldTerm in already replaced terms will not be
     * replaced, because the replacement would not terminate then.
     * @param oldTerm The term to be replaced.
     * @param newTerm The term to replace.
     * @return The PrologClause where oldTerm has been replaced by newTerm in
     *         its body.
     */
    public PrologClause replaceAllInBody(final PrologTerm oldTerm, final PrologTerm newTerm) {
        return this.isFact() ? this : new PrologClause(this.getHead(), this.getBody().replaceAll(oldTerm, newTerm));
    }

    /**
     * Replaces all occurences of oldTerm in the head of this
     * PrologClause with newTerm. If oldTerm is a subterm of newTerm,
     * occurences of oldTerm in already replaced terms will not be
     * replaced, because the replacement would not terminate then.
     * @param oldTerm The term to be replaced.
     * @param newTerm The term to replace.
     * @return The PrologClause where oldTerm has been replaced by newTerm in
     *         its head.
     */
    public PrologClause replaceAllInHead(final PrologTerm oldTerm, final PrologTerm newTerm) {
        return new PrologClause(this.getHead().replaceAll(oldTerm, newTerm), this.getBody());
    }

    /**
     * Sets the body of this clause.
     * @param term The new body.
     */
    public PrologClause replaceBody(final PrologTerm term) {
        return new PrologClause(this.getHead(), term);
    }

    /**
     * Sets the head of this clause.
     * @param term The new head.
     * @throws NullPointerException If the new head is null.
     */
    public PrologClause replaceHead(final PrologTerm term) throws NullPointerException {
        if (term == null) {
            throw new NullPointerException();
        }
        return new PrologClause(term, this.getBody());
    }

    public PrologClause replacePredicates(final Collection<? extends FunctionSymbol> preds, final PrologTerm term) {
        return new PrologClause(this.getHead(), this.getBody().replacePredicates(preds, term));
    }

    @Override
    public JSONArray toJSON() {
        return new JSONArray(new Object[]{JSONExportUtil.toJSON(this.head), JSONExportUtil.toJSON(this.body)});
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        if (this.getBody() == null) {
            return this.getHead().toString();
        }
        return this.getHead().toString() + " :- " + this.getBody().toString();
    }

    public PrologClause transformUnderscores() {
        final FreshNameGenerator fridge =
            new FreshNameGenerator(this.createSetOfAllVariableNames(), FreshNameGenerator.PROLOG_VARS);
        return new PrologClause(
            PrologTerms.transformUnderscores(this.getHead(), fridge),
            PrologTerms.transformUnderscores(this.getBody(), fridge));
    }

    public PrologClause walkAll(final ReplacementWalker walker) {
        return new PrologClause(this.getHead().walk(walker), this.isFact() ? null : this.getBody().walk(walker));
    }

    /**
     * Method for using a TermWalker on the head and body of this clause.
     * This method will pass the TermWalker through the head and body
     * terms of this clause using its goDeeper() and isApplicable()
     * methods and calling the performAction() method on applicable
     * (sub-)terms.
     * @param walker The TermWalker to use.
     */
    public void walkAll(final TermWalker walker) {
        this.walkHead(walker);
        this.walkBody(walker);
    }

    public PrologClause walkBody(final ReplacementWalker walker) {
        if (this.getBody() != null) {
            return new PrologClause(this.getHead(), this.getBody().walk(walker));
        } else {
            if (walker.isApplicable(null)) {
                return new PrologClause(this.getHead(), walker.replace(null));
            } else {
                return this;
            }
        }
    }

    /**
     * Method for using a TermWalker on the body of this clause. This
     * method will pass the TermWalker through the body term of this
     * clause using its goDeeper() and isApplicable() methods and calling
     * the performAction() method on applicable (sub-)terms.
     * @param walker The TermWalker to use.
     */
    public void walkBody(final TermWalker walker) {
        if (this.getBody() != null) {
            this.getBody().walk(walker);
        }
    }

    /**
     * Method for using a TermWalker on the conjunctions in the body of
     * this clause. This method will pass the TermWalker through the
     * conjuncted terms in the body term of this clause using its
     * isApplicable() method and calling the performAction() method on
     * applicable (sub-)terms.
     * @param walker The TermWalker to use.
     */
    public void walkConjunction(final TermWalker walker) {
        if (this.getBody() != null) {
            this.getBody().walkConjunction(walker);
        }
    }

    public PrologClause walkHead(final ReplacementWalker walker) {
        return new PrologClause(this.getHead().walk(walker), this.getBody());
    }

    /**
     * Method for using a TermWalker on the head of this clause. This
     * method will pass the TermWalker through the head term of this
     * clause using its isApplicable() method and calling the
     * performAction() method on applicable (sub-)terms.
     * @param walker The TermWalker to use.
     */
    public void walkHead(final TermWalker walker) {
        this.getHead().walk(walker);
    }

    /**
     * Method for using a TermWalker on the head and the conjunctions in
     * the body of this clause. This method will pass the TermWalker
     * through the head term and the conjuncted terms in the body term of
     * this clause using its goDeeper() and isApplicable() methods and
     * calling the performAction() method on applicable (sub-)terms.
     * @param walker The TermWalker to use.
     */
    public void walkHeadAndConjunction(final TermWalker walker) {
        this.getHead().walkConjunction(walker);
        this.walkConjunction(walker);
    }

    /**
     * @param termWalker
     */
    public void walkPredication(final TermWalker walker) {
        if (this.getBody() != null) {
            this.getBody().walkPredication(walker);
        }
    }

}
