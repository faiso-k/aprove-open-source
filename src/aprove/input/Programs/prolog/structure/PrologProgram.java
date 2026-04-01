package aprove.input.Programs.prolog.structure;

import java.math.*;
import java.util.*;

import org.json.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.processors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.JSON.*;

/**
 * Class representing a Prolog program. A PrologProgram consists of a
 * list of clauses, a list of directives, a set of queries and a set of
 * operators.<br><br>
 *
 * Created: Sep 8, 2006<br>
 * Last modified: Aug 19, 2015
 *
 * @author cryingshadow
 * @version $Id$
 */
public class PrologProgram implements Exportable, JSONExport {

    /**
     * A program is a logic program if two conditions are met: First, all
     * clauses must consist of an atom on the left hand side and a set of atoms
     * on the right hand side. Second, no builtin predicates may be used.
     *
     * @param prologProg
     *            The PrologProgram to test.
     * @return True, if prologProg is a logic program. False otherwise.
     */
    public static boolean isLogicProgram(PrologProgram program) {
        Set<FunctionSymbol> preds = program.createSetOfAllPredicates();
        for (PrologClause clause : program.getClauses()) {
            if (!clause.isLogicProgramCompatible(preds)) {
                return false;
            }
        }
        return program.createSetOfDefinedPredicates().equals(preds);
    }

    /**
     * Calculates a hash value for a collection as the sum of the hash
     * values of the collection's items.
     * @param collection The collection to calculate a hash value for.
     * @return A hash value for the specified collection.
     */
    private static int calcHashFromCollection(Collection<?> collection) {
        int res = 0;
        for (Object o : collection) {
            res += o.hashCode();
        }
        return res;
    }

    /**
     * The clauses.
     */
    private List<PrologClause> clauses;

    /**
     * The directives.
     */
    private final List<PrologDirective> directives;

    /**
     * The operator set.
     */
    private PrologOperatorSet ops;

    public PrologProgram() {
        this(PrologOperatorSet.createStandardSet());
    }

    public PrologProgram(PrologOperatorSet set) {
        this.clauses = new ArrayList<PrologClause>();
        this.directives = new ArrayList<PrologDirective>();
        this.ops = set;
    }

    /**
     * @param clause
     */
    public boolean addClause(PrologClause clause) {
        return this.clauses.add(clause);
    }

    public void addClauses(Collection<? extends PrologClause> clauses) {
        this.clauses.addAll(clauses);
    }

    /**
     * Creates a new PrologProgram equal to this program, but with new
     * instances of every clause, directive and the set of operators.
     * The queries, however, are the same objects and are no new
     * instances.
     * @return A deep copy of this PrologProgram.
     */
    public PrologProgram copy() {
        PrologProgram res = new PrologProgram(this.ops.copy());
        for (PrologClause clause : this.clauses) {
            res.clauses.add(clause);
        }
        for (PrologDirective directive : this.directives) {
            res.directives.add(directive);
        }
        return res;
    }

    public Pair<PrologTerm, PrologTerm> createFailurePreds() {
        PrologFNG fridge = this.createFreshNameGenerator();
        String failure = fridge.getFreshName("failure", false);
        List<PrologTerm> a = new ArrayList<PrologTerm>();
        List<PrologTerm> b = new ArrayList<PrologTerm>();
        a.add(new PrologTerm(fridge.getFreshName("a", false)));
        b.add(new PrologTerm(fridge.getFreshName("b", false)));
        return new Pair<PrologTerm, PrologTerm>(new PrologTerm(failure, a), new PrologTerm(failure, b));
    }

    /**
     * Creates a new FreshNameGenerator with a set of used names
     * containing all defined predicates.
     * @return A new FreshNameGenerator with a set of used names
     *         containing all defined predicates.
     */
    public PrologFNG createFreshNameGenerator() {
        final Set<String> used = new LinkedHashSet<String>();
        final Set<FunctionSymbol> preds = this.createSetOfAllPredicates();
        final TermWalker walker = new TermWalker() {

            @Override
            public boolean goDeeper(PrologTerm term) {
                return true;
            }

            @Override
            public boolean isApplicable(PrologTerm term) {
                return !term.isAtom(preds) && !term.isVariable();
            }

            @Override
            public void performAction(PrologTerm term) {
                used.add(term.getName());
            }

        };
        for (PrologClause clause : this.clauses) {
            clause.walkAll(walker);
        }
        return new PrologFNG(used, FreshNameGenerator.PROLOG_FUNCS);
    }

    /**
     * Defined predicates with number of clauses.
     */
    public Map<FunctionSymbol, Integer> createMapOfDefinedPredicates() {
        Map<FunctionSymbol, Integer> res = new LinkedHashMap<FunctionSymbol, Integer>();
        for (PrologClause clause : this.clauses) {
            FunctionSymbol f = clause.createFunctionSymbol();
            Integer num = res.get(f);
            if (num == null) {
                num = 0;
            }
            num++;
            res.put(f, num);
        }
        return res;
    }

    public Map<FunctionSymbol, Integer> createMapOfRecursivePredicates() {
        Map<FunctionSymbol, Integer> res = this.createMapOfDefinedPredicates();
        res.keySet().removeAll(this.createSetOfNonRecursivePredicates());
        return res;
    }

    public Set<String> createSetOfAllFunctionSymbolNames() {
        Set<String> res = new LinkedHashSet<String>();
        for (PrologClause clause : this.clauses) {
            res.addAll(clause.createSetOfAllFunctionSymbolNames());
        }
        return res;
    }

    public Set<FunctionSymbol> createSetOfAllFunctionSymbols() {
        Set<FunctionSymbol> res = new LinkedHashSet<FunctionSymbol>();
        for (PrologClause clause : this.clauses) {
            res.addAll(clause.createSetOfAllFunctionSymbols());
        }
        return res;
    }

    /**
     * Creates a set of all predicates in this PrologProgram
     * (without predefined predicates).
     * @return A set of all predicates in this PrologProgram.
     */
    public Set<FunctionSymbol> createSetOfAllPredicates() {
        return this.createSetOfAllPredicates(false);
    }

    /**
     * Creates a set of all predicates in this PrologProgram.
     * @param withPredefined Indicates whether or not predefined
     *                       predicates should be in the set.
     * @return A set of all predicates in this PrologProgram.
     */
    public Set<FunctionSymbol> createSetOfAllPredicates(boolean withPredefined) {
        Set<FunctionSymbol> res = new LinkedHashSet<FunctionSymbol>();
        for (PrologClause clause : this.clauses) {
            res.addAll(clause.createSetOfAllPredicates());
        }
        if (withPredefined) {
            res.addAll(PrologBuiltins.BUILTIN_PREDICATES);
        }
        //        res.remove(PrologBuiltin.CUT_PREDICATE);
        return res;
    }

    /**
     * @return
     */
    public Set<String> createSetOfAllSymbolNames() {
        Set<String> res = new LinkedHashSet<String>();
        for (PrologClause clause : this.clauses) {
            res.addAll(clause.createSetOfAllSymbolNames());
        }
        for (PrologDirective directive : this.directives) {
            res.addAll(directive.createSetOfAllSymbolNames());
        }
        return res;
    }

    /**
     * Creates a set of all defined predicates in this PrologProgram
     * (without predefined predicates). A predicate is defined if at
     * least one clause exists with this predicate as head term.
     * @return A set of all defined predicates in this PrologProgram.
     */
    public Set<FunctionSymbol> createSetOfDefinedPredicates() {
        Set<FunctionSymbol> res = new LinkedHashSet<FunctionSymbol>();
        for (PrologClause clause : this.clauses) {
            res.add(clause.createFunctionSymbol());
        }
        return res;
    }

    /**
     * Creates a set of all defined predicates in this PrologProgram.
     * A predicate is defined, if at least one clause exists with this
     * predicate as head term.
     * @param withPredefined Indicates whether or not predefined
     *                       predicates should be in the set.
     * @return A set of all defined predicates in this PrologProgram.
     */
    public Set<FunctionSymbol> createSetOfDefinedPredicates(boolean withPredefined) {
        Set<FunctionSymbol> res = new LinkedHashSet<FunctionSymbol>();
        for (PrologClause clause : this.clauses) {
            res.add(clause.createFunctionSymbol());
        }
        if (withPredefined) {
            res.addAll(PrologBuiltins.BUILTIN_PREDICATES);
        }
        return res;
    }

    /**
     * Creates a set of all non-recursive predicates in this
     * PrologProgram. A predicate is non-recursive, if there is no
     * chain of predicate calls starting with the predicate in
     * question, such that there is a predicate that occurs more than
     * once in the chain.
     * @return A set of all non-recursive predicates in this
     *         PrologProgram.
     */
    public Set<FunctionSymbol> createSetOfNonRecursivePredicates() {
        Set<FunctionSymbol> res = new LinkedHashSet<FunctionSymbol>();
        for (FunctionSymbol symbol : this.createSetOfDefinedPredicates()) {
            if (this.isNonRecursivePredicate(symbol, new LinkedHashSet<FunctionSymbol>())) {
                res.add(symbol);
            }
        }
        return res;
    }

    public Set<Integer> createSetOfRecursiveClauseNumbers(Map<FunctionSymbol, Integer> recursivePredicates) {
        Set<Integer> res = new LinkedHashSet<Integer>();
        for (int i = 0; i < this.clauses.size(); i++) {
            PrologTerm body = this.clauses.get(i).getBody();
            if (body != null) {
                boolean in = false;
                for (PrologTerm predication : body.createConjunctionListOfPredications()) {
                    FunctionSymbol symbol = predication.createFunctionSymbol();
                    if (recursivePredicates.containsKey(symbol)
                        || PrologBuiltins.RECURSIVE_BUILTIN_PREDICATES.containsKey(symbol))
                    {
                        in = true;
                        break;
                    }
                }
                if (in) {
                    res.add(i);
                }
            }
        }
        return res;
    }

    public Set<FunctionSymbol> createSetOfRecursivePredicates() {
        Set<FunctionSymbol> res = this.createSetOfDefinedPredicates();
        res.removeAll(this.createSetOfNonRecursivePredicates());
        return res;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        if (o instanceof PrologProgram) {
            //@TODO
        }
        return false;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Utility.Exportable#export(aprove.verification.oldframework.Utility.Export_Util)
     */
    @Override
    public String export(Export_Util eu) {
        Set<FunctionSymbol> preds = this.createSetOfAllPredicates(true);
        StringBuilder res = new StringBuilder();
        res.append(eu.export("Clauses:"));
        res.append(eu.linebreak());
        res.append(eu.linebreak());
        for (PrologClause c : this.clauses) {
            res.append(c.export(eu, preds));
            res.append(eu.export("."));
            res.append(eu.linebreak());
        }
        if (!this.directives.isEmpty()) {
            res.append(eu.linebreak());
            res.append(eu.export("Directives:"));
            res.append(eu.linebreak());
            res.append(eu.linebreak());
            for (PrologDirective d : this.directives) {
                res.append(d.export(eu, preds));
                res.append(eu.export("."));
                res.append(eu.linebreak());
            }
        }
        return res.toString();
    }

    public void flattenOutConjunctions() {
        List<PrologClause> newList = new ArrayList<PrologClause>();
        for (PrologClause clause : this.clauses) {
            newList.add(clause.flattenOutConjunctions());
        }
        this.clauses = newList;
    }

    public BigInteger getBiggestAbsoluteNumber() {
        MaxInt res = new MaxInt();
        res.value = BigInteger.valueOf(0);
        this.walkAll(new TermWalker() {

            @Override
            public boolean goDeeper(PrologTerm term) {
                return true;
            }

            @Override
            public boolean isApplicable(PrologTerm term) {
                return term.isInt();
            }

            @Override
            public void performAction(PrologTerm term) {
                BigInteger next = ((PrologInt) term).getValue().abs();
                if (res.value.compareTo(next) < 0) {
                    res.value = next;
                }
            }

        });
        return res.value;
    }

    /**
     * Returns the clause with the specified index.
     * @param clauseIndex The index of the clause.
     * @return The clause with the specified index.
     */
    public PrologClause getClause(int clauseIndex) {
        return this.clauses.get(clauseIndex);
    }

    /**
     * Returns a list of all indices of the clauses with the specified
     * predicate as head term.
     * @param predicate The predicate to look for.
     * @return A list of all indices of the clauses with the specified
     *         predicate as head term.
     */
    public List<Integer> getClauseIndicesForPredicate(FunctionSymbol predicate) {
        ArrayList<Integer> res = new ArrayList<Integer>();
        for (int i = 0; i < this.clauses.size(); i++) {
            if (this.clauses.get(i).createFunctionSymbol().equals(predicate)) {
                res.add(i);
            }
        }
        return res;
    }

    /**
     * Returns a list of all indices of the clauses with the specified
     * predicate called in the body term.
     * @param predicate The predicate to look for.
     * @return A list of all indices of the clauses with the specified
     *         predicate called in the body term.
     */
    public List<Integer> getClauseIndicesWithPredicate(FunctionSymbol predicate) {
        ArrayList<Integer> res = new ArrayList<Integer>();
        for (int i = 0; i < this.clauses.size(); i++) {
            PrologTerm body = this.clauses.get(i).getBody();
            if (body != null && body.occurs(predicate.getName(), predicate.getArity())) {
                res.add(i);
            }
        }
        return res;
    }

    /**
     * Returns the clauses.
     * @return The clauses.
     */
    public List<PrologClause> getClauses() {
        return this.clauses;
    }

    /**
     * Returns a list of all clauses with the specified predicate as head
     * term.
     * @param predicate The predicate to look for.
     * @return A list of all clauses with the specified predicate as head
     *         term.
     */
    public List<PrologClause> getClausesForPredicate(FunctionSymbol predicate) {
        ArrayList<PrologClause> res = new ArrayList<PrologClause>();
        for (PrologClause clause : this.clauses) {
            if (clause.createFunctionSymbol().equals(predicate)) {
                res.add(clause);
            }
        }
        return res;
    }

    /**
     * Returns a list of all clauses with the specified predicate called
     * in the body term.
     * @param predicate The predicate to look for.
     * @return A list of all clauses with the specified predicate called
     *         in the body term.
     */
    public List<PrologClause> getClausesWithPredicate(FunctionSymbol predicate) {
        ArrayList<PrologClause> res = new ArrayList<PrologClause>();
        for (PrologClause clause : this.clauses) {
            PrologTerm body = clause.getBody();
            if (body != null && body.occurs(predicate.getName(), predicate.getArity())) {
                res.add(clause);
            }
        }
        return res;
    }

    /**
     * Returns the directives.
     * @return The directives.
     */
    public List<PrologDirective> getDirectives() {
        return this.directives;
    }

    public String getLatexCommandsForSymbols() {
        StringBuilder res = new StringBuilder();
        for (String name : this.createSetOfAllFunctionSymbolNames()) {
            if (name.equals(PrologBuiltin.CONJUNCTION_NAME)) {
                continue;
            }
            res.append("\\newcommand{\\F");
            res.append(PrologBuiltins.toLaTeX(name));
            res.append("}{\\mathsf{");
            res.append(name);
            res.append("}}\n");
        }
        return res.toString();
    }

    /**
     * Returns the set of operators.
     * @return The set of operators.
     */
    public PrologOperatorSet getOperators() {
        return this.ops;
    }

    /**
     * Returns a set containing all variable names used in this
     * PrologProgram.
     * @return A set containing all variable names used in this
     *         PrologProgram.
     */
    public Set<String> getVariableNames() {
        final Set<String> res = new LinkedHashSet<String>();
        this.walkAll(new TermWalker() {

            @Override
            public boolean goDeeper(PrologTerm term) {
                return true;
            }

            @Override
            public boolean isApplicable(PrologTerm term) {
                return term.isVariable();
            }

            @Override
            public void performAction(PrologTerm term) {
                res.add(term.getName());
            }

        });
        return res;
    }

    /**
     * @return
     */
    public boolean hasDisjunction() {
        for (PrologClause clause : this.clauses) {
            PrologTerm body = clause.getBody();
            if (body != null && body.hasDisjunction()) {
                return true;
            }
        }
        return false;
    }

    /**
     * Returns true if there is a fact in the program which occurs after a
     * rule (also if the fact and the rule belong to different predicates).
     */
    public boolean hasFactAfterRule() {
        boolean fact = true;
        for (PrologClause clause : this.getClauses()) {
            if (fact && !clause.isFact()) {
                fact = false;
            } else if (!fact && clause.isFact()) {
                return true;
            }
        }
        return false;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return PrologProgram.calcHashFromCollection(this.clauses)
            + PrologProgram.calcHashFromCollection(this.directives)
            + this.ops.hashCode();
    }

    /**
     * Tests whether or not the specified predicate occurs anywhere in
     * this PrologProgram.
     * @param pred The predicate to look for.
     * @return True, if the predicate occurs in this program.
     *         False otherwise.
     */
    public boolean hasPredicate(FunctionSymbol pred) {
        return this.createSetOfAllPredicates().contains(pred);
    }

    public boolean isCutFree() {
        for (PrologClause clause : this.clauses) {
            if (clause.containsCut()) {
                return false;
            }
        }
        for (PrologDirective directive : this.directives) {
            if (directive.getBody().containsCut()) {
                return false;
            }
        }
        return true;
    }

    /**
     * @param failPredicate
     * @return
     */
    public boolean isDefined(FunctionSymbol symbol) {
        for (PrologClause clause : this.clauses) {
            if (clause.getHead().createFunctionSymbol().equals(symbol)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Replaces all occurences of oldTerm in this PrologProgram with
     * newTerm. If oldTerm is a subterm of newTerm, occurences of
     * oldTerm in already replaced terms will not be replaced, because
     * the replacement would not terminate then.
     * @param oldTerm The term to be replaced.
     * @param newTerm The term to replace.
     */
    public void replaceAll(PrologTerm oldTerm, PrologTerm newTerm) {
        List<PrologClause> newList = new ArrayList<PrologClause>();
        for (PrologClause clause : this.clauses) {
            newList.add(clause.replaceAll(oldTerm, newTerm));
        }
        this.clauses = newList;
    }

    /**
     * Sets the set of operators.
     * @param ops The new set of operators.
     * @throws NullPointerException If ops is null.
     */
    public void setOperators(PrologOperatorSet ops) throws NullPointerException {
        if (ops == null) {
            throw new NullPointerException("A PrologProgram must have a PrologOperatorSet!");
        }
        this.ops = ops;
    }

    @Override
    public JSONObject toJSON() {
        JSONObject res = new JSONObject();
        res.put("clauses", JSONExportUtil.toJSON(this.clauses));
        res.put("directives", JSONExportUtil.toJSON(this.directives));
        return res;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        StringBuilder build = new StringBuilder();
        build.append("Clauses:\n\n");
        for (PrologClause c : this.clauses) {
            build.append(c.toString());
            build.append(".\n");
        }
        if (!this.directives.isEmpty()) {
            build.append("\nDirectives:\n\n");
            for (PrologDirective d : this.directives) {
                build.append(d.toString());
                build.append(".\n");
            }
        }
        return build.toString();
    }

    public void transformUnderscores() {
        List<PrologClause> newList = new ArrayList<PrologClause>();
        for (PrologClause clause : this.clauses) {
            newList.add(clause.transformUnderscores());
        }
        this.clauses = newList;
    }

    public void walkAll(ReplacementWalker walker) {
        List<PrologClause> newList = new ArrayList<PrologClause>();
        for (PrologClause clause : this.clauses) {
            newList.add(clause.walkAll(walker));
        }
        this.clauses = newList;
    }

    /**
     * Method for using a TermWalker on the head and body of all clauses.
     * This method will pass the TermWalker through the head and body
     * terms of all clauses using its goDeeper() and isApplicable()
     * methods and calling the performAction() method on applicable
     * (sub-)terms.
     * @param walker The TermWalker to use.
     */
    public void walkAll(TermWalker walker) {
        for (PrologClause clause : this.clauses) {
            clause.walkAll(walker);
        }
    }

    /**
     * Method for using a TermWalker on the body of all clauses. This
     * method will pass the TermWalker through the body term of all
     * clauses using its goDeeper() and isApplicable() methods and
     * calling the performAction() method on applicable (sub-)terms.
     * @param walker The TermWalker to use.
     */
    public void walkAllBodies(TermWalker walker) {
        for (PrologClause clause : this.clauses) {
            clause.walkBody(walker);
        }
    }

    /**
     * Method for using a TermWalker on the conjunctions in the body of
     * all clauses. This method will pass the TermWalker through the
     * conjuncted terms in the body term of all clauses using its
     * isApplicable() method and calling the performAction() method on
     * applicable (sub-)terms.
     * @param walker The TermWalker to use.
     */
    public void walkAllConjunctions(TermWalker walker) {
        for (PrologClause clause : this.clauses) {
            clause.walkConjunction(walker);
        }
    }

    /**
     * Method for using a TermWalker on the head of all clauses. This
     * method will pass the TermWalker through the head term of all
     * clauses using its isApplicable() method and calling the
     * performAction() method on applicable (sub-)terms.
     * @param walker The TermWalker to use.
     */
    public void walkAllHeads(TermWalker walker) {
        for (PrologClause clause : this.clauses) {
            clause.walkHead(walker);
        }
    }

    /**
     * Method for using a TermWalker on the head and the conjunctions in
     * the body of all clauses. This method will pass the TermWalker
     * through the head term and the conjuncted terms in the body term of
     * all clauses using its goDeeper() and isApplicable() methods and
     * calling the performAction() method on applicable (sub-)terms.
     * @param walker The TermWalker to use.
     */
    public void walkAllHeadsAndConjunctions(TermWalker walker) {
        for (PrologClause clause : this.clauses) {
            clause.walkHead(walker);
            clause.walkConjunction(walker);
        }
    }

    /**
     * Method for using a ClauseWalker on all clauses. This method will
     * call the ClauseWalker's performAction() method on every clause
     * which results in a true value by calling the ClauseWalker's
     * isApplicable() method.
     * @param walker The ClauseWalker to use.
     */
    public void walkClauses(ClauseWalker walker) {
        for (PrologClause clause : this.clauses) {
            if (walker.isApplicable(clause)) {
                walker.performAction(clause);
            }
        }
    }

    /**
     * @param symbol
     * @param name
     * @return
     */
    private boolean isNonRecursivePredicate(FunctionSymbol symbol, LinkedHashSet<FunctionSymbol> called) {
        if (called.contains(symbol)) {
            return false;
        } else {
            called = new LinkedHashSet<FunctionSymbol>(called);
            called.add(symbol);
            boolean res = true;
            for (PrologClause clause : this.getClausesForPredicate(symbol)) {
                if (!clause.isFact()) {
                    PrologTerm body = clause.getBody();
                    if (body.isConjunction()) {
                        Set<FunctionSymbol> calls = new LinkedHashSet<FunctionSymbol>();
                        for (PrologTerm atom : body.createConjunctionListOfPredications()) {
                            calls.add(atom.createFunctionSymbol());
                        }
                        for (FunctionSymbol predicate : calls) {
                            res &= this.isNonRecursivePredicate(predicate, called);
                            if (!res) {
                                break;
                            }
                        }
                    } else {
                        res &= this.isNonRecursivePredicate(body.createFunctionSymbol(), called);
                    }
                }
                if (!res) {
                    break;
                }
            }
            return res;
        }
    }

    /**
     * @author cryingshadow
     *
     */
    private static class MaxInt {

        /**
         *
         */
        private BigInteger value;

    }

}
