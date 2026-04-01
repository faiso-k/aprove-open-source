package aprove.verification.oldframework.Algebra.Terms;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.Visitors.*;
import aprove.verification.oldframework.Algebra.Terms.Visitors.RenameVarsVisitor;
import aprove.verification.oldframework.Algebra.Terms.Visitors.SubstitutionVisitor;
import aprove.verification.oldframework.Algebra.Terms.Visitors.ToLaTeXVisitor;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.LinearArithmetic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Visitors.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.oldframework.Unification.*;
import aprove.verification.oldframework.Unification.Utility.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

/** Basic abstract class for representing terms.
 *  <p>
 *  This class also contains all the basic algorithms for
 *  term manipulation. See the documentation below.
 *
 * 2011 note: You most likely do not wish to use this class.
 * It has been superseded for general use by
 * aprove.verification.dpframework.BasicStructures.Term and only remains
 * because the inductive theorem prover of AProVE makes use
 * of this class as underlying data structure..
 *
 * @author Burak Emir, Peter Schneider-Kamp, Carsten Pelikan, Achim Luecking
 * @version $Id$
 */
public abstract class AlgebraTerm
implements TermOrFormula, HTML_Able, LaTeX_Able, DOT_Able, Exportable, java.io.Serializable {

  protected enum Pos {
      skeleton,wavefront;
  }

  protected Symbol sym;

  /** A hashtable to set arbitrary attributes. (For example labels)
   */
  protected Hashtable<String,Object> attributes;

  protected AlgebraTerm() {
  }

  public void setAttribute(String key, Object value) {
      if (this.attributes == null) {
      this.attributes = new Hashtable<String,Object>();
      }
      this.attributes.put(key, value);
  }

  public Object getAttribute(Object key) {
      if (this.attributes == null) {
      return null;
      }
      return this.attributes.get(key);
  }

  public Object removeAttribute(Object key) {
      if (this.attributes == null) {
      return null;
      }
      return this.attributes.remove(key);
  }

  public void setAttributes(Hashtable<String,Object> attrs) {
      this.attributes = attrs;
  }

  public Hashtable<String,Object> getAttributes() {
      return this.attributes;
  }

  /** Returns true if this term equals t.
   *  <p>
   *  Note: This requires hashCode to be implemented such that
   *        equal terms have the same hash code.
   */
  @Override
  public abstract boolean equals(Object t);
  
  
  @Override
  public abstract int hashCode();

  /** Subclasses implement this method to allow CoarseGrainedTermVisitor.
   */
  public abstract <T> T apply(CoarseGrainedTermVisitor<T> ctv);

  /** Subclasses implement this method to allow FineGrainedTermVisitor.
   */
  public abstract <T> T apply(FineGrainedTermVisitor<T> ftv);

  public abstract <T> T apply(CoarseGrainedTermVisitorException<T> ctve)
          throws InvalidPositionException;

  /** Returns the (root) symbol of this term.
   */
  public Symbol getSymbol() {
    return this.sym;
  }

  /** Implementing class should return true if the term is a variable.
   */
  public abstract boolean isVariable();

  /** Returns a list of arguments if this is a function application, null
   *  otherwise. Changing the list does not change this term in any way.
   */
  @Override
public abstract List<AlgebraTerm> getArguments();

  /** Returns the i-th argument if this is a function application, throws
   *  an exception otherwise.
   */
  public abstract AlgebraTerm getArgument(int index);

  public abstract AlgebraTerm createWithFriendlyNames(FreshNameGenerator ngen, Program prog);

  /** Returns a set containing all variables appearing in this term.
   * Potentially destructive.
   */
  final public Set<AlgebraVariable> getVars() {
    return (Set<AlgebraVariable>) GetVariablesVisitor.apply(this, true);
  }

  /** Returns a set containing the symbols of all variables appearing
   * in this term.
   * As potentially destructive as getVars()
   */
  final public Set<VariableSymbol> getVariableSymbols() {
    return (Set<VariableSymbol>) GetVariableSymbolsVisitor.apply(this, true);
  };

  /** Returns a list of all variables appearing in this term.
   * Potentially destructive.
   */
  final public List<AlgebraVariable> getListOfVars() {
    return (List<AlgebraVariable>) GetVariablesVisitor.apply(this, false);
  }

  /** Renames the variables in this term such that it does not
   *  contain any variable from a given set.
   *  <p>
   *  Note: This is a destructive method.
   *  @param sv Set of variables that this term may not contain.
   */
  final public void renameVars(Set<AlgebraVariable> sv) {
    this.renameVars(new FreshVarGenerator(sv));
  }

  /** Renames the variables in this term.
   *  <p>
   *  Note: This is a destructive method.
   */
  final public void renameVars() {
    this.renameVars(new FreshVarGenerator());
  }

  /** Renames the variables in this term such according to
   *  a given FreshVarGenerator.
   *  <p>
   *  Note: This is a destructive method.
   *  @param fg FreshVarGenerator to use.
   */
  final public void renameVars(FreshVarGenerator fg) {
    RenameVarsVisitor v = new RenameVarsVisitor(fg);
    this.apply(v);
  }

  /**
   * Computes the number of function symbols in this term.
   */
  final public int length() {
    return LengthVisitor.apply(this);
  }

  /**
   * Computes the total number of occurrences of variables in this term.
   * @return the total number of occurrences
   */
  final public int getNumberOfVarOcc() {
    int result = 0;
    List<AlgebraTerm> terms = this.getAllSubterms();
    Iterator it = terms.iterator();
    while (it.hasNext()) {
      AlgebraTerm tmp = (AlgebraTerm) it.next();
      if (tmp.isVariable()) {
        result += 1;
      }
    }
    return result;
  }

  /**
   * Computes the number occurencies of a variable v in this term.
   * @param v the variable
   * @return the number of occurencies
   */
  final public int getNumberOfVarOcc(AlgebraVariable v) {
    int result = 0;
    List<AlgebraTerm> terms = this.getAllSubterms();
    Iterator it = terms.iterator();
    while (it.hasNext()) {
      AlgebraTerm tmp = (AlgebraTerm) it.next();
      if (tmp.isVariable()) {
        AlgebraVariable tmpv = (AlgebraVariable) tmp;
        if (v.equals(tmpv)) {
            result += 1;
        }
      }
    }
    return result;
  }

  /**
   * Computes the number occurencies of a function symbol f in this term.
   * @param f the function symbol
   * @return the number of occurencies
   */
  final public int getNumberOfFctSymOcc(SyntacticFunctionSymbol f) {
    int result = 0;
    List<AlgebraTerm> terms = this.getAllSubterms();
    Iterator it = terms.iterator();
    while (it.hasNext()) {
      AlgebraTerm tmp = (AlgebraTerm) it.next();
      if (!tmp.isVariable()) {
        SyntacticFunctionSymbol tmpf = (SyntacticFunctionSymbol) tmp.getSymbol();
        if (f.equals(tmpf)) {
            result += 1;
        }
      }
    }
    return result;
  }

  /**
   * Filter a term with a given mapping.
   * @param map Mapping from function symbols to filter parameter.
   * @return A new term which is the result of filtering this term.
   */
  final public AlgebraTerm filter(Map map) {
    FilterVisitor v = new FilterVisitor(map);
    return (AlgebraTerm) this.apply(v);
  }

    /**
     * Determine the needed function symbols for this given a certain filtering.
     */
    final public Set<SyntacticFunctionSymbol> getNeeded(Map map) {
        GetNeededVisitor v = new GetNeededVisitor(map);
        this.apply(v);
        return v.getNeeded();
    }

  /**
     * Filter a term with a given mapping that will not allow null-filter
     * (if a filter is not set, then a null will be returned)
     * @param map Mapping from function symbols to filter parameter.
     * @return A new term which is the result of filtering this term.
     */
    final public AlgebraTerm filterStrict(Map map) {
      FilterVisitor v = new FilterVisitor(map,false);
      return (AlgebraTerm) this.apply(v);
    }


  /** Returns the subterm at a given Position.
   * <p>
   * Note: Changing the returned subterm will change this term!
   * Deepcopy if you are going to change the subterm.
   */
  final public AlgebraTerm getSubterm(Position p) {
    return GetPositionOfTermVisitor.apply(this, p);
  }

  /** Returns the subterm at position i.
   */
  final public AlgebraTerm getSubterm(int i) {
    return GetPositionOfTermVisitor.apply(this, i);
  }

  /** Returns a list of terms containing all subterms of this term,
   *  including the term itself.
   *  <p>
   *  Note: Returning a set instead will break
   *  at least isLinear() and maybe other methods.
   */
  final public List<AlgebraTerm> getAllSubterms() {
    return GetSubtermsVisitor.apply(this);
  }

  /** Returns a list of terms containing all subterms of this term,
   *  not including the term itself.
   */
  final public List<AlgebraTerm> getAllProperSubterms() {
    return GetSubtermsVisitor.applyProper(this);
  }

  /** Returns the substitution under that this term matches the
   *  given term.
   * @throws UnificationException
   */
  public AlgebraSubstitution matches(AlgebraTerm that) throws UnificationException {
    return this.matches(that, AlgebraSubstitution.create());
  }

  /** Given a term and a set of variables this method tries to match without
   *  substituting variables from the given set of variables.
   * @param that The term to be matched with.
   * @param forbidden The set of variables that will not be substituted.
   * @return The substitution neccessary to make both terms equal.
   */
  public AlgebraSubstitution matchesWithForbiddenVars(AlgebraTerm that, Set<AlgebraVariable> forbidden)
    throws UnificationException {
    return this.matches(that, VarRenaming.getIdentity(forbidden));
  }

  /** Given a term and a substitution this method tries to match this term
   *  to that term under the given substitution.
   * @param that The term to be matched with.
   * @param sub The substitution to be used in matching.
   * @return The substitution necessary to make both terms equal, where replacements of the form x/x may occur.
   * @throws UnificationException iff there is a match failure.
   */
  public AlgebraSubstitution matchesWithIdentities(AlgebraTerm that, AlgebraSubstitution sub)
            throws UnificationException {
        if (this.isVariable()) {
            VariableSymbol var = (VariableSymbol) this.getSymbol();
            if (sub.get(var) != null) {
                if (!this.apply(sub).equals(that)) {
                    throw new MatchFailureException("match failure", this, that);
                }
            } else {
                sub.put(var, that);

            }
        } else if (that.isVariable()) {
            throw new MatchFailureException("match failure", this, that);
        } else {
            if (this.getSymbol().equals(that.getSymbol())) {
                for (int i = 0; i < this.getArguments().size(); i++) {
                    sub = this.getArgument(i).matchesWithIdentities(that.getArgument(i), sub);
                    if (sub == null) {
                        throw new MatchFailureException("match failure", this,
                                that);
                    }
                }
            } else {
                throw new MatchFailureException("match failure", this, that);
            }
        }
        return sub;
    }

  /** Given another term, this method tries to match this term to that term.
   * @param that The term to be matched with.
   * @return The substitution necessary to make both terms equal, where replacements of the form x/x may occur.
   * @throws UnificationException iff there is a match failure.
   */
  public AlgebraSubstitution matchesWithIdentities(AlgebraTerm that) throws UnificationException {
      return this.matchesWithIdentities(that, AlgebraSubstitution.create());
  }

  /** Given a term and a substitution this method tries to match this term
   *  to that term under the given substitution.
   * @param that The term to be matched with.
   * @param sub The substitution to be used in matching.
   * @return The substitution necessary to make both terms equal.
   * @throws UnificationException iff there is a match failure.
   */
  public AlgebraSubstitution matches(AlgebraTerm that, AlgebraSubstitution sub) throws UnificationException {
          this.matchesWithIdentities(that, sub);
        AlgebraSubstitution subRed = AlgebraSubstitution.create();
        for(Map.Entry<VariableSymbol, AlgebraTerm> subEnt : sub.getMapping().entrySet()) {
            if (!subEnt.getKey().equals(subEnt.getValue().getSymbol())) {
                subRed.put(subEnt.getKey(), subEnt.getValue());
            }
        }
        return subRed;
  }

  /** Given a term this method unifies the term with this term,
   *  if not unifiable an exception occurs else a minimal
   *  substitution will be returned.
   *  @param that The term to be unified with.
   *  @return A substitution which is a most general unifier.
   */
  public AlgebraSubstitution unifies(AlgebraTerm that) throws UnificationException {
    return this.unifies(that, AlgebraSubstitution.create());
  }

  /** Given a term and a substitution this method extends the substitution
   *  to an unifier with the term; if not unifiable, an exception will
   *  be thrown, else a substitution will be returned.
   * @param that The term to be unified with.
   * @param sub The substitution which unifies preceeding term nodes.
   * @return A substitution which is a unifier.
   * @throws UnificationException iff there is a symbol clash or the occurs check fails.
   */
  public AlgebraSubstitution unifies(AlgebraTerm that, AlgebraSubstitution sub) throws UnificationException {
    Set<PairOfTerms> list = new LinkedHashSet<PairOfTerms>();
    list.add(new SimplePairOfTerms(this, that));
    return AlgebraTerm.solveUP(list,sub);
  }

  /** Given an unfification problem and a substitution this method extends the substitution
   *  to an unifier; if not unifiable, an exception will
   *  be thrown, else a substitution will be returned.
   * @param inlist list of term pairs - the unification problem
   * @param sub The substitution which unifies preceeding term nodes.
   * @return A substitution which is a unifier.
   * @throws UnificationException iff there is a symbol clash or the occurs check fails.
   */
  public static AlgebraSubstitution solveUP(Set<PairOfTerms> inlist, AlgebraSubstitution sub) throws UnificationException {
    Set<PairOfTerms> list = new LinkedHashSet<PairOfTerms>(inlist);
    while (!list.isEmpty()) {
      Iterator i = list.iterator();
      PairOfTerms pair = (PairOfTerms) i.next();
      list.remove(pair);
      AlgebraTerm s = pair.getLeft();
      AlgebraTerm t = pair.getRight();

      /* just do nothing if they are equal anyway (Trivial) */
      if (!s.equals(t)) {
        if (t.isVariable() && !s.isVariable()) {
          /* swap them (Orient) */
          AlgebraTerm tmp;
          tmp = s;
          s = t;
          t = tmp;
        }
        if (s.isVariable()) {
          if (t.getVars().contains(s)) {
            /* (Occurs Check) */
            throw new OccurCheckException("occurs check", s, t, sub, list);
          } else {
            /* (Variable Elimination) */
            /* map {s/t} in the hash set */
            AlgebraSubstitution sigma = AlgebraSubstitution.create();
            sigma.put(((AlgebraVariable) s).getVariableSymbol(), t);
            Set<PairOfTerms> transformed = new LinkedHashSet<PairOfTerms>();
            i = list.iterator();
            while (i.hasNext()) {
              pair = (PairOfTerms) i.next();
              transformed.add(
                new SimplePairOfTerms(pair.getLeft().apply(sigma), pair.getRight().apply(sigma)));
            }
            list = transformed;
            /* change sub */
            sub = sub.compose(sigma);
          }
        } else {
          /* no variable */
          if (s.getSymbol().equals(t.getSymbol())) {
            /* (Decomposition) */
            for (int j = 0; j < s.getArguments().size(); j++) {
              list.add(new SimplePairOfTerms(s.getArgument(j), t.getArgument(j)));
            }
          } else {
            /* (Symbol Clash) */
            throw new SymbolClashException("symbol clash", s, t, sub, list);
          }
        }
      }
    }

    return sub;
  }

  /** Apply a substitution to this term and return the result
   *  as a new term.
   * @param sub Substitution to apply.
   * @return A new term that is the result of applying sub to this term.
   */
  public AlgebraTerm apply(AlgebraSubstitution sub) {
    return SubstitutionVisitor.apply(this, sub);
  }

  /** Replace the subterm at a given position of this term.
   * @param t Term to replace the subterm.
   * @param p Position that designates the subterm to be replaced.
   * return A new term that is the result of replacing the subterm.
   */
  public AlgebraTerm replaceAt(AlgebraTerm t, Position p) {
    return ReplaceSubtermVisitor.apply(this.deepcopy(), t, p);
  }

  /**
   * Returns a list containing all possible positions of this term
   * in leftmost-outermost order.
   */
  final public Set<Position> getPositions() {
    return this.getPositions(Position.create());
  }

  /** Appends the positions of this term to the given prefix.
   */
  final Set<Position> getPositions(Position prefix) {
    Set<Position> poss = new LinkedHashSet<Position>();
    poss.add(prefix);
    if (!this.isVariable()) {
      Iterator j = this.getArguments().iterator();
      for (int i = 0; j.hasNext(); i++) {
        AlgebraTerm s = (AlgebraTerm) j.next();
        Position newpos = prefix.shallowcopy();
        newpos.add(i);
        poss.addAll(s.getPositions(newpos));
      }
    }
    return poss;
  }

  /**
   * Returns a list containing all possible positions of this term
   * in leftmost-innermost order.
   */
  final public Set<Position> getInnermostPositions() {
    return this.getInnermostPositions(Position.create());
  }

  /** Appends the positions of this term to the given prefix.
   */
  final Set<Position> getInnermostPositions(Position prefix) {
    Set<Position> poss = new LinkedHashSet<Position>();
    if (!this.isVariable()) {
      Iterator j = this.getArguments().iterator();
      for (int i = 0; j.hasNext(); i++) {
        AlgebraTerm s = (AlgebraTerm) j.next();
        Position newpos = prefix.shallowcopy();
        newpos.add(i);
        poss.addAll(s.getInnermostPositions(newpos));
      }
    }
    poss.add(prefix);
    return poss;
  }

    /**
    * Returns a list containing all possible positions of this term
    * in leftmost-outermost order.
    */
    final public Set<Position> getOutermostPositions() {
    Set<Position> poss = new LinkedHashSet<Position>();
    this.getOutermostPositions(poss, Position.create());
    return poss;
    }

    final protected void getOutermostPositions(Set<Position> poss, Position prefix) {
    poss.add(prefix);
    if (!this.isVariable()) {
        Iterator it = this.getArguments().iterator();
        for (int i=0; it.hasNext(); i++) {
        AlgebraTerm t = (AlgebraTerm)it.next();
        Position p = prefix.shallowcopy();
        p.add(i);
        t.getOutermostPositions(poss, p);
        }
    }
    }

  /** Gets all positions starting with a certain  symbol.
   */
  public final Set<Position> getPositionsWithSymbol(Symbol fsym) {
    Set<Position> result = new LinkedHashSet<Position>();
    Set<Position> allSubtermPos = this.getPositions();
    for (Iterator i = allSubtermPos.iterator(); i.hasNext();) {
      Position p = (Position) i.next();
      AlgebraTerm t = this.getSubterm(p);
      if( t.sym.equals(fsym)) {
          result.add(p);
      }
    }
    return result;
  }

  /* Forbidden for security's and sanity's sake */
  @Override
protected Object clone() {
    throw new RuntimeException("clone deprecated -- use deepcopy / shallowcopy instead");
  }

  /** Returns a shallow copy of this object, i.e. a term that uses the
   *  same symbol and argument list.
   *  <p>
   *  Note: Changing the arguments of the copied term will result in
   *  changes to the original term!
   */
  public abstract AlgebraTerm shallowcopy();

  /** Returns a deep copy of this object, i.e. a term that has the
   *  same structure and uses the same symbols.
   *  <p>
   *  Note: Changing the symbols will result in changes to the
   *  original term.
   */
  public abstract AlgebraTerm deepcopy();

  /* Returns a paranoid copy of this object, i.e. a term that
   *  has the same structure and all the symbols are copied, too.
   *  <p>
   *  Note: Safe, but incredibly ineffecient. Also makes changes
   *  to the function symbols difficult.
   *
  public abstract Term paranoidcopy();*/

  /**
   * Returns a string representation of this term.
   */
  @Override
public String toString() {
    return ToStringVisitor.apply(this,false);
  }

  @Override
public String export(Export_Util o){
      if (o instanceof HTML_Util) {
        return this.toHTML();
      }
      if (o instanceof LaTeX_Util) {
          return this.toLaTeX();
      }
      if (o instanceof PLAIN_Util ) {
          return this.toString();
      }

      throw new RuntimeException("Unknown Export_Util");
  }

  /**
   * Returns a HTML representation of this term.
   */
  @Override
public String toHTML() {
    return ToHTMLVisitor.apply(this);
  }

  /**
   * Returns a LaTeX representation of this term.
   */
  @Override
public String toLaTeX() {
      return ToLaTeXVisitor.apply(this);
  }

  /**
   * Returns a LaTeX representation of this term.
   */
  public String toSimpleLaTeX() {
      return ToSimpleLaTeXVisitor.apply(this);
  }

  /**
   * Returns a graph representation of this term.
   */
  public Graph toGraph() {
      return ToGraphVisitor.apply(this);
  }

  /**
   * Returns a dotty representation of this term.
   */
  @Override
public String toDOT() {
      return this.toGraph().toDOT();
  }

  /**
   * Returns a representation of this term that is suitable for TTT.
   */
  public String toTTT() {
      return ToTTTVisitor.apply(this);
  }

  /**
   * Returns a representation of this term that is suitable for Termptation.
   */
  public String toTERMPTATION(FreshNameGenerator vars, FreshNameGenerator funcs) {
      return ToTERMPTATIONVisitor.apply(this, vars, funcs);
  }

  /**
   * Returns a representation of this term that is suitable for Haskell.
   */
  public String toHASKELL() {
      return ToHASKELLVisitor.apply(this);
  }

  /**
   *@param pos is the postion to be marked
   *@return the string represntation with positon marked
   */
  public String highlight(Position pos, boolean useHTML) {
    return HighlightTermVisitor.apply(this, pos, useHTML);
  }

  /**
   *@param v is the variable to be highlighted
   *@return the string represntation with positon marked
   */
  public String highlightVars(AlgebraVariable v, boolean useHTML) {
    return HighlightVarsInTerm.apply(this, v, useHTML);
  }

  /**
   * Extremely verbose string representation of this term.
   */
  public abstract String verboseToString();

  // methods for Checkable interface
  final public void check() {
    CheckTermVisitor.apply(this);
  }

  final public void check(Set<CheckTermVisitor> s) {
    CheckTermVisitor.apply(this, s);
  }

  /**
   * Return a set of all subterms that start with a defined function symbol.
   * @return A new set containing all subterms starting with a defined function symbol.
   */
  public Set<AlgebraTerm> getDefFunctionSubterms() {
    Set<AlgebraTerm> defFunctionSubterms = new LinkedHashSet<AlgebraTerm>();
    Iterator i = this.getAllSubterms().iterator();
    while (i.hasNext()) {
      AlgebraTerm term = (AlgebraTerm) i.next();
      if (term instanceof DefFunctionApp) {
        defFunctionSubterms.add(term);
      }
    }
    return defFunctionSubterms;
  }

  /**
   * Return the set of all proper subterms that start with a defined function symbol.
   * @return A new set of all proper subterms that start with a defined function symbol
   */
  public Set<AlgebraTerm> getInnerDefFunctionSubterms() {
    Set<AlgebraTerm> defFunctionSubterms = new LinkedHashSet<AlgebraTerm>();
    Iterator i = this.getAllProperSubterms().iterator();
    while (i.hasNext()) {
      AlgebraTerm term = (AlgebraTerm) i.next();
      if (term instanceof DefFunctionApp) {
        defFunctionSubterms.add(term);
      }
    }
    return defFunctionSubterms;
  }

  /**
   * Return a set of all subterms that start with a function symbol.
   * @return A new set of all subterms that start with a function symbol.
   */
  public Set<AlgebraTerm> getFunctionSubterms() {
    Set<AlgebraTerm> functionSubterms = new LinkedHashSet<AlgebraTerm>();
    Iterator i = this.getAllSubterms().iterator();
    while (i.hasNext()) {
      AlgebraTerm term = (AlgebraTerm) i.next();
      if (term instanceof AlgebraFunctionApplication) {
        functionSubterms.add(term);
      }
    }
    return functionSubterms;
  }

  /**
   * Return a set of all subterms that start with a constructor symbol.
   * @return A set of all subterms that start with a constructor symbol.
   */
  public Set<ConstructorApp> getConstructorSubterms() {
    Set<ConstructorApp> constructorSubterms = new LinkedHashSet<ConstructorApp>();
    for (AlgebraTerm term : this.getAllSubterms()) {
      if (term instanceof ConstructorApp) {
        constructorSubterms.add((ConstructorApp) term);
      }
    }
    return constructorSubterms;
  }

  /**
   * Return true if this term is unifiable with the given term.
   * @return true if this term is unifiable with the given term.
   */
  public boolean isUnifiable(AlgebraTerm that) {
    try {
      this.unifies(that);
    } catch (UnificationException e) {
      return false;
    }
    return true;
  }

  /** Returns true if there exists a term from the given set
   *  that is unifiable with this term.
   */
  public boolean isUnifiable(Set<AlgebraTerm> termSet) {
    Iterator i = termSet.iterator();
    while (i.hasNext()) {
      AlgebraTerm term = (AlgebraTerm) i.next();
      if (this.isUnifiable(term)) {
        return true;
      }
    }
    return false;
  }

  /** Returns the sort of this term.
   */
  public Sort getSort() {
    return this.sym.getSort();
  }

  /** Returns true if a term is linear.
   */
  public boolean isLinear() {
    return CheckLinearVisitor.apply(this);
  }

  /** Replaces each occurance of the old variable in this term
   *  by the given new variable.
   * @param oldVariable Variable to replace.
   * @param newVariable Variable that replaces oldVariable.
   * @return A new term where all occurances of oldVariable are replaced by newVariable.
   */
  public AlgebraTerm replaceVariable(AlgebraVariable oldVariable, AlgebraVariable newVariable) {
    AlgebraSubstitution sub = AlgebraSubstitution.create();
    sub.put(oldVariable.getVariableSymbol(), newVariable);
    return this.apply(sub);
  }

  /** Replaces each occurance of the old variable in this term
   *  by the given new term.
   * @param oldVariable Variable to replace.
   * @param newTerm Term that replaces oldVariable.
   * @return A new term where all occurances of oldVariable are replaced by newTerm.
   */
  public AlgebraTerm replaceVariable(AlgebraVariable oldVariable, AlgebraTerm newTerm) {
    AlgebraSubstitution sub = AlgebraSubstitution.create();
    sub.put(oldVariable.getVariableSymbol(), newTerm);
    return this.apply(sub);
  }

  /** Returns the set of all defined function symbols in this term.
   */
  public Set<DefFunctionSymbol> getDefFunctionSymbols() {
    Set<DefFunctionSymbol> defFunctionSymbols = new LinkedHashSet<DefFunctionSymbol>();
    // Bestimme alle Subterme, die ein definiertes Wurzelsymbol haben und
    // nimm dieses in die Ergebnismenge auf
    Iterator i = this.getDefFunctionSubterms().iterator();
    while (i.hasNext()) {
      AlgebraTerm term = (AlgebraTerm) i.next();
      defFunctionSymbols.add((DefFunctionSymbol) term.getSymbol());
    }
    return defFunctionSymbols;
  }

  /** Returns the set of all defined function symbols in this term that occur below the root.
   */
  public Set<DefFunctionSymbol> getInnerDefFunctionSymbols() {
    Set<DefFunctionSymbol> defFunctionSymbols = new LinkedHashSet<DefFunctionSymbol>();
    Iterator i = this.getInnerDefFunctionSubterms().iterator();
    while (i.hasNext()) {
      AlgebraTerm term = (AlgebraTerm) i.next();
      defFunctionSymbols.add((DefFunctionSymbol) term.getSymbol());
    }
    return defFunctionSymbols;
  }

  /** Returns the set of all function symbols in this term that occur below the root.
   */
  public Set<SyntacticFunctionSymbol> getInnerFunctionSymbols() {
    Set<SyntacticFunctionSymbol> functionSymbols = new LinkedHashSet<SyntacticFunctionSymbol>();
    Iterator i = this.getAllProperSubterms().iterator();
    while (i.hasNext()) {
      AlgebraTerm term = (AlgebraTerm) i.next();
      Symbol symb = term.getSymbol();
      if(symb instanceof SyntacticFunctionSymbol) {
          functionSymbols.add((SyntacticFunctionSymbol) symb);
      }
    }
    return functionSymbols;
  }

  /** Returns the set of all function symbols in this term.
   */
  public Set<SyntacticFunctionSymbol> getFunctionSymbols() {
    return GetFunctionsVisitor.apply(this);
  }

  /** Returns the set of all constants in this term.
  */
  public Set<SyntacticFunctionSymbol> getConstants() {
    Set<SyntacticFunctionSymbol> tmp = new LinkedHashSet<SyntacticFunctionSymbol>(this.getFunctionSymbols());
    Iterator it = tmp.iterator();
    while (it.hasNext()) {
      SyntacticFunctionSymbol fs = (SyntacticFunctionSymbol) it.next();
      if (!fs.isConstant()) {
        tmp.remove(fs);
    }
    }
    return tmp;
  }

  /** Returns the set of all constructor symbols in this term.
   */
  public Set<ConstructorSymbol> getConstructorSymbols() {
    Set<ConstructorSymbol> constructorSymbols = new LinkedHashSet<ConstructorSymbol>();
    for (ConstructorApp term : this.getConstructorSubterms()) {
      constructorSymbols.add((ConstructorSymbol) term.getSymbol());
    }
    return constructorSymbols;
  }

  /** Evaluates and returns the result as a new term.
   */
  public AlgebraTerm eval(Evaluator evaluator) {
    return evaluator.eval(this);
  }

  public boolean isMatchable(AlgebraTerm that) {
    try {
      this.matches(that);
    } catch (UnificationException e) {
      return false;
    }
    return true;
  }

  /**
   * Loescht aus dem Term jeden Subterm mit einem definiertem Funktionssymbol
   * und ersetzt diesen durch eine Variable. Der urspruengliche Term wird
   * dabei nicht veraendert.
   * @return Ein Term, in dem jeder Subterm mit einem definiertem Funktionssymbol
   * durch eine Variable ersetzt wurde.
   */
  public AlgebraTerm cap(FreshVarGenerator generator) {
    AlgebraTerm term = this.deepcopy();
    if (term.isVariable()) {
      return term;
    } else {
      SyntacticFunctionSymbol functionSymbol = (SyntacticFunctionSymbol) term.getSymbol();
      if (functionSymbol instanceof DefFunctionSymbol) {
        return generator.getFreshVariable("x", functionSymbol.getSort(), false);
      } else {
        Vector<AlgebraTerm> arguments = new Vector<AlgebraTerm>();
        for (int i = 0; i < functionSymbol.getArity(); i++) {
          AlgebraTerm subterm = term.getArgument(i);
          arguments.addElement(subterm.cap(generator));
        }
        return ConstructorApp.create((ConstructorSymbol) functionSymbol, arguments);
      }
    }
  }

  /**
   * Loescht aus dem Term jeden Subterm mit einem definiertem Funktionssymbol
   * und ersetzt diesen durch eine Variable. Der urspruengliche Term wird
   * dabei nicht veraendert.
   * @return Ein Term, in dem jeder Subterm mit einem definiertem Funktionssymbol
   * durch eine Variable ersetzt wurde.
   */
  public AlgebraTerm cap(AlgebraTerm s, FreshVarGenerator generator, Collection<Rule> rules) {
    //System.out.println("s = "+s+"\nrules = "+rules);
    Set<AlgebraTerm> allSubs = new HashSet<AlgebraTerm>(s.getAllSubterms());
    AlgebraTerm term = this.deepcopy();
    if (term.isVariable()) {
      return term;
    } else {
      SyntacticFunctionSymbol functionSymbol = (SyntacticFunctionSymbol) term.getSymbol();
      Vector<AlgebraTerm> arguments = new Vector<AlgebraTerm>();
      for (int i = 0; i < functionSymbol.getArity(); i++) {
          AlgebraTerm subterm = term.getArgument(i);
          arguments.addElement(subterm.cap(s, generator, rules));
      }
      AlgebraFunctionApplication fapp = AlgebraFunctionApplication.create(functionSymbol, arguments);
      if (functionSymbol instanceof DefFunctionSymbol && !allSubs.contains(fapp)) {
          Iterator i = rules.iterator();
          while (i.hasNext()) {
              Rule rule = (Rule)i.next();
              //System.out.println("left = "+rule.getLeft().toDOT()+"\nfapp = "+fapp.toDOT());
              try {
                  AlgebraSubstitution sub = rule.getLeft().unifies(fapp);
                  if (!sub.isNormal(rules)) { // better: check if left-side of dependency-pair is instantiated to normal form
                      //System.out.println("UNNORMAL");
                      continue;
                  }
                  //System.out.println("WONDERFUL");
                  return generator.getFreshVariable("x", functionSymbol.getSort(), false);
              } catch (UnificationException e) {
                  //System.out.println("NO");
                  // pass
              }
          }
          fapp = (AlgebraFunctionApplication)term;
      }
      return fapp;
    }
  }

  /**
   * Returns a new term that has all proper subterms with a defined root symbol replaced by a fresh variable.
   */
  public AlgebraTerm capE(FreshVarGenerator generator) {
      AlgebraTerm term = this.deepcopy();
      if(term.isVariable()) {
          return term;
      } else {
          SyntacticFunctionSymbol functionSymbol = (SyntacticFunctionSymbol) term.getSymbol();
          Vector<AlgebraTerm> arguments = new Vector<AlgebraTerm>();
          for(int i = 0; i < functionSymbol.getArity(); i++) {
              AlgebraTerm subterm = term.getArgument(i);
              arguments.addElement(subterm.cap(generator));
          }
          return AlgebraFunctionApplication.create(functionSymbol, arguments);
      }
  }

  /**
    * Replaces all subterms that are not guaranteed to be normal by fresh variables.
    */
   public AlgebraTerm rencapAC(AlgebraTerm s, FreshVarGenerator generator, Set<SyntacticFunctionSymbol> ACs, Set<SyntacticFunctionSymbol> Cs) {
       Set<ACnCTerm> allNormalSubs = ACnCTerm.create(s, ACs, Cs).getNormalSubs();
       AlgebraTerm caped = this.capAChelper(generator, ACs, Cs, true, allNormalSubs);
       return caped.renAC(generator, ACs, Cs, allNormalSubs);
   }

   private AlgebraTerm capAChelper(FreshVarGenerator generator, Set<SyntacticFunctionSymbol> ACs, Set<SyntacticFunctionSymbol> Cs, boolean root, Set<ACnCTerm> allNormalSubs) {
       AlgebraTerm term = this.deepcopy();
       if(term.isVariable()) {
           return term;
       } else {
           SyntacticFunctionSymbol functionSymbol = (SyntacticFunctionSymbol) term.getSymbol();
           if(!root && (functionSymbol instanceof DefFunctionSymbol)) {
               if(allNormalSubs.contains(ACnCTerm.create(term, ACs, Cs))) {
                   return term;
               } else {
                   return generator.getFreshVariable("x", functionSymbol.getSort(), false);
               }
           } else {
               Vector<AlgebraTerm> arguments = new Vector<AlgebraTerm>();
               for(int i = 0; i < functionSymbol.getArity(); i++) {
                   AlgebraTerm subterm = term.getArgument(i);
                   arguments.addElement(subterm.capAChelper(generator, ACs, Cs, false, allNormalSubs));
               }
               return AlgebraFunctionApplication.create(functionSymbol, arguments);
           }
       }
   }
   private AlgebraTerm renAC(FreshVarGenerator generator, Set<SyntacticFunctionSymbol> ACs, Set<SyntacticFunctionSymbol> Cs, Set<ACnCTerm> allNormalSubs) {
       AlgebraTerm term = this.deepcopy();
       if(term.isVariable()) {
           boolean useMemory = false;
           if(allNormalSubs.contains(ACnCTerm.create(term, ACs, Cs))) {
               useMemory = true;
           }
           return generator.getFreshVariable((AlgebraVariable)term, useMemory);
       } else {
           SyntacticFunctionSymbol functionSymbol = (SyntacticFunctionSymbol) term.getSymbol();
           Vector<AlgebraTerm> arguments = new Vector<AlgebraTerm>();
           for(int i = 0; i < functionSymbol.getArity(); i++) {
               AlgebraTerm subterm = term.getArgument(i);
               arguments.addElement(subterm.renAC(generator, ACs, Cs, allNormalSubs));
           }
           if(functionSymbol instanceof DefFunctionSymbol) {
               return DefFunctionApp.create((DefFunctionSymbol) functionSymbol, arguments);
           } else {
               return ConstructorApp.create((ConstructorSymbol) functionSymbol, arguments);
           }
       }
   }

  /**
   * CAP^-1 for EDG*
   */
  public AlgebraTerm cap_1(FreshVarGenerator generator, Set<SyntacticFunctionSymbol> rootSymbols) {
    AlgebraTerm term = this.deepcopy();
    if (term.isVariable()) {
      return term;
    } else {
      SyntacticFunctionSymbol functionSymbol = (SyntacticFunctionSymbol) term.getSymbol();
      if (rootSymbols.contains(functionSymbol)) {
        return generator.getFreshVariable("x", functionSymbol.getSort(), false);
      } else {
        Vector<AlgebraTerm> arguments = new Vector<AlgebraTerm>();
        for (int i = 0; i < functionSymbol.getArity(); i++) {
          AlgebraTerm subterm = term.getArgument(i);
          arguments.addElement(subterm.cap_1(generator, rootSymbols));
        }
        return AlgebraFunctionApplication.create(functionSymbol, arguments);
      }
    }
  }

  /* propably incorrect
   * CAP^-1_s for EDG*
   *
  public Term cap_1(Term s, FreshVarGenerator generator, Set<FunctionSymbol> rootSymbols) {
      Set<Term> allSubs = new HashSet<Term>(s.getAllSubterms());
      Term term = this.deepcopy();
      if (term.isVariable()) {
          return term;
      } else {
          FunctionSymbol functionSymbol = (FunctionSymbol)term.getSymbol();
          if (rootSymbols.contains(functionSymbol)) {
              if (allSubs.contains(term)) {
                  return term;
              } else {
                  return generator.getFreshVariable("x", functionSymbol.getSort(), false);
              }
          } else {
              Vector<Term> arguments = new Vector<Term>();
              for (int i=0; i<functionSymbol.getArity(); i++) {
                  Term subterm = term.getArgument(i);
                  arguments.addElement(subterm.cap_1(s, generator, rootSymbols));
              }
              return FunctionApplication.create(functionSymbol, arguments);
          }
      }
  }*/

  /**
   * Deletes all subterms headed by a defined symbol from t, if the subterm is not
   * a subterm of s as well. The deleted subterm is replaced by a fresh variable.
   * This method is not destructive.
   * @param s The term containing the normal subterme..
   * @return A new term as defined by cap_s.
   */
  public AlgebraTerm cap(AlgebraTerm s, FreshVarGenerator generator) {
    Set<AlgebraTerm> allSubs = new HashSet<AlgebraTerm>(s.getAllSubterms());
    AlgebraTerm term = this.deepcopy();
    if (term.isVariable()) {
      return term;
    } else {
      SyntacticFunctionSymbol functionSymbol = (SyntacticFunctionSymbol) term.getSymbol();
      if (functionSymbol instanceof DefFunctionSymbol) {
        if (allSubs.contains(term)) {
          return term;
        } else {
          return generator.getFreshVariable("x", functionSymbol.getSort(), false);
        }
      } else {
        Vector<AlgebraTerm> arguments = new Vector<AlgebraTerm>();
        for (int i = 0; i < functionSymbol.getArity(); i++) {
          AlgebraTerm subterm = term.getArgument(i);
          arguments.addElement(subterm.cap(s, generator));
        }
        return ConstructorApp.create((ConstructorSymbol) functionSymbol, arguments);
      }
    }
  }


  /**
   * Loescht aus dem Term t jeden Teilterm der ein subterm von s ist
   * und ersetzt diese durch die Variable "x".
   * @param s Der Term, dessen Subterme ersetzt werden
   */
  public AlgebraTerm dropS(AlgebraTerm s) {
      if (this.isSubtermOf(s)) {
          VariableSymbol x = VariableSymbol.create("x",this.getSort());
          AlgebraVariable xt = AlgebraVariable.create(x);
          return xt;
      }
      if (this.isVariable()) {
        return this.deepcopy();
    }
      AlgebraFunctionApplication t = (AlgebraFunctionApplication) this;
    SyntacticFunctionSymbol functionSymbol = (SyntacticFunctionSymbol) t.getSymbol();
    Vector<AlgebraTerm> arguments = new Vector<AlgebraTerm>();
    for (int i = 0; i < functionSymbol.getArity(); i++) {
          AlgebraTerm subterm = t.getArgument(i);
          arguments.addElement(subterm.dropS(s));
    }
    return AlgebraFunctionApplication.create(functionSymbol, arguments);
  }



  /**
   * Returns a term that is result of replacing all the variables in this term
   * by new variables. The original term is not changed.
   * @param generator The generator for new variables.
   * @param useMemory True means each occurance of a variable x is replaced
   *                  by the same new variable x'.
   * @return A term where all the variables have been replaced.
   */
  public AlgebraTerm ren(FreshVarGenerator generator, boolean useMemory) {
    AlgebraTerm term = this.deepcopy();
    if (term.isVariable()) {
      AlgebraVariable var = (AlgebraVariable) term;
      return generator.getFreshVariable(var, useMemory);
    } else {
      SyntacticFunctionSymbol functionSymbol = (SyntacticFunctionSymbol) term.getSymbol();
      Vector<AlgebraTerm> arguments = new Vector<AlgebraTerm>();
      for (int i = 0; i < functionSymbol.getArity(); i++) {
        AlgebraTerm subterm = term.getArgument(i);
        arguments.addElement(subterm.ren(generator, useMemory));
      }
      if (functionSymbol instanceof DefFunctionSymbol) {
        return DefFunctionApp.create((DefFunctionSymbol) functionSymbol, arguments);
      } else {
        return ConstructorApp.create((ConstructorSymbol) functionSymbol, arguments);
      }
    }
  }

  /**
   * Rewrite this term to a new term with the given rule at the
   * given position.
   */
  public AlgebraTerm rewrite(Rule rule, Position pos) {
      AlgebraSubstitution sub;
      try {
          sub = rule.getLeft().matches(this.getSubterm(pos));
      } catch (UnificationException e) {
          throw new RuntimeException("internal error: rewrite of "+this+" at "+pos+" not possible using "+rule+"!");
      }
      return this.replaceAt(rule.getRight().apply(sub), pos);
  }

    /** Computes the set of all possible one-step rewrites of a term.
     */
    public Set<AlgebraTerm> doOneRewriteStep(Set<Rule> rules) {
        Set<Position> positions = this.getPositions();
        Set<AlgebraTerm> terms = new LinkedHashSet<AlgebraTerm>();
        Iterator i = positions.iterator();
        while (i.hasNext()) {
            Position position = (Position) i.next();
            AlgebraTerm subterm = this.getSubterm(position);
            Iterator j = rules.iterator();
            while (j.hasNext()) {
                Rule rule = (Rule) j.next();
                AlgebraTerm leftTerm = rule.getLeft();
                try {
                    AlgebraSubstitution sub = leftTerm.matches(subterm);
                    AlgebraTerm rightTerm = rule.getRight();
                    AlgebraTerm substitutedTerm = rightTerm.apply(sub);
                    AlgebraTerm completeTerm = this.replaceAt(substitutedTerm, position);
                    terms.add(completeTerm);
                } catch (UnificationException e) {
                }
            }
        }
        return terms;
    }

  /**
   * Determine if this term is normal.
   * @param rules The set of rules which might be used to rewrite this term.
   * @return True if this term cannot be rewritten further.
   */
  public boolean isNormal(Collection<Rule> rules) {
    Iterator i = this.getAllSubterms().iterator();
    while (i.hasNext()) {
      AlgebraTerm sub = (AlgebraTerm) i.next();
      Iterator j = rules.iterator();
      while (j.hasNext()) {
        AlgebraTerm left = ((Rule) j.next()).getLeft();
        if (left.isMatchable(sub)) {
          return false;
        }
      }
    }
    return true;
  }

  /**
   * Determine if this term is normal.
   * @param rules The set of rules which might be used to rewrite this term.
   * @param unif The matching algorithm to be used.
   * @return True if this term cannot be rewritten further.
   */
  public boolean isNormal(Collection<Rule> rules, GeneralUnification unif) {
    Iterator i = this.getAllSubterms().iterator();
    while (i.hasNext()) {
      AlgebraTerm sub = (AlgebraTerm) i.next();
      Iterator j = rules.iterator();
      while (j.hasNext()) {
        AlgebraTerm left = ((Rule) j.next()).getLeft();
        if (unif.matchable(left, sub)) {
          return false;
        }
      }
    }
    return true;
  }

  /**
   * Determine if the root symbol is a constant.
   * @return True if the root symbol is a constant, false otherwise.
   */
  public boolean isConstant() {
      if (this.isVariable()) {
        return false;
    }
      SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol) this.getSymbol();
      return (fsym.isConstant());
  }

  /** Determine a normal form of this term.
   * If the rules are not terminating, this method may not finish.
   * @param rules The set of rules which might be used to rewrite this term.
   * @return A new term that is a normal form of this term w.r.t. the rules.
   */
  public AlgebraTerm normalize(Collection<Rule> rules) {
    boolean rewritten = true;
    AlgebraTerm result = this.deepcopy();

    while (rewritten) {
      rewritten = false;
      Set<Position> positions = result.getPositions();
      Iterator i = positions.iterator();
      while (i.hasNext() && !rewritten) {
        Position position = (Position) i.next();
        AlgebraTerm subterm = result.getSubterm(position);
        Iterator j = rules.iterator();
        while (j.hasNext() && !rewritten) {
          Rule rule = (Rule) j.next();
          AlgebraTerm leftTerm = rule.getLeft();
          try {
            AlgebraSubstitution sub = leftTerm.matches(subterm);
            AlgebraTerm rightTerm = rule.getRight();
            AlgebraTerm substitutedTerm = rightTerm.apply(sub);
            result = result.replaceAt(substitutedTerm, position);
            rewritten = true;
          } catch (UnificationException e) {
          }
        }
      }
    }

    return result;
  }

  /**
   *
   * @return true if this term can be evaluated by the evalautor
   */
  public boolean evaluable(Evaluator ev){
        return ev.evaluable(this);
  }

  //returns maximum depth of a term
  public int getMaxDepth() {
    return TermMaxDepth.getVal(this);
  }

  //Index indictaes the complexity of a term
  public int getIndex1() {
    return TermIndex1.getVal(this);
  }

  public void inferType(Program.SortMap sorted, Object rule) {
    TypeInferenceVisitor.apply(this, sorted, rule);
  }

  public int count(Symbol sym) {
      return CountVisitor.apply(this, sym);
  }

    /** Returns this if the symbol of this term is not a TupleSymbol, otherwise
     * the term origination from this by replacement of the TupleSymbol by the corresponding
     * DefFunctionSymbol is returned.
     */
    public AlgebraTerm getUntupleed() {
    if(!(this.sym instanceof TupleSymbol)) {
        return this;
    }
    TupleSymbol tup = (TupleSymbol)this.sym;
    return AlgebraFunctionApplication.create(tup.getOrigin(), this.getArguments());
    }

    public AlgebraTerm convertTupleSymbol() {
        if (!(this.sym instanceof TupleSymbol)) {
            return this;
        }
        TupleSymbol tup = (TupleSymbol)this.sym;
        DefFunctionSymbol newSym = DefFunctionSymbol.create(tup.getName(), tup.getArgSorts(), tup.getSort());
        newSym.setFixity(tup.getFixity(), tup.getFixityLevel());
        return AlgebraFunctionApplication.create(newSym, this.getArguments());
    }

    /** Returns true iff this term is a subterm of the given term.
     */
    public boolean isSubtermOf(AlgebraTerm that) {
    if (this.equals(that)) {
        return true;
    }
    if (!that.isVariable()) {
        Iterator it = that.getArguments().iterator();
        while (it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)it.next();
        if (this.isSubtermOf(arg)) {
            return true;
        }
        }
    }
    return false;
    }

    public AlgebraTerm limitRewriteStep(int labellimit, int iterlimit, int depthlimit, Map<SyntacticFunctionSymbol,Set<Rule>> rwrules) {
    return this.limitRewriteStep(labellimit, iterlimit, depthlimit, rwrules, 0);
    }

    /** Performs a rewrite step with respect to a certain limit using
     *  a given set of rewrite-rules.
     */
    public AlgebraTerm limitRewriteStep(int labellimit, int iterlimit, int depthlimit, Map<SyntacticFunctionSymbol,Set<Rule>> rwrules, int depth) {
      if (depth > depthlimit || this.isVariable()) {
        return null;
    }
    SyntacticFunctionSymbol sym = (SyntacticFunctionSymbol)this.getSymbol();
    Set<Rule> rules = rwrules.get(sym);
    if (rules != null) {
        Hashtable label = (Hashtable)this.getAttribute("label");
        Integer count = (Integer)label.get(sym.getName());
        if (count == null || count.intValue() < labellimit) {
        Iterator it = rules.iterator();
        while (it.hasNext()) {
            Rule r = (Rule)it.next();
            AlgebraTerm rewritten = this.deepcopy().rewrite(labellimit, iterlimit, depthlimit, r, rwrules, depth);
            if (rewritten != null) {
            return rewritten;
            }
        }
        }
    }
    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    Iterator it = this.getArguments().iterator();
    while (it.hasNext()) {
        AlgebraTerm ta = (AlgebraTerm)it.next();
        AlgebraTerm tan = ta.limitRewriteStep(labellimit, iterlimit, depthlimit, rwrules, depth);
        if (tan != null) {
        args.add(tan);
        while(it.hasNext()) {
            args.add((AlgebraTerm) it.next());
        }
        AlgebraTerm t = AlgebraFunctionApplication.create(sym, args);
        t.setAttributes(this.getAttributes());
        return t;
        }
        args.add(ta);
    }
    return null;
    }

    public AlgebraTerm limitRewriteStep(Map<SyntacticFunctionSymbol,Set<Rule>> rwrules, Set<DefFunctionSymbol> preferredFuncs, int limit) {
    Iterator it = this.getRewritePositions(preferredFuncs).iterator();
    while (it.hasNext()) {
        Position pi = (Position)it.next();
        AlgebraTerm t = this.getSubterm(pi);
        DefFunctionSymbol fsym = (DefFunctionSymbol)t.getSymbol();
        Set<Rule> rules = rwrules.get(fsym);
        if (rules != null) {
        Hashtable<String,Integer> label = (Hashtable<String,Integer>)t.getAttribute("label");
        Integer count = label.get(fsym.getName());
        int countv = (count == null) ? 0 : count.intValue();
        if (countv < limit) {
            Iterator r_it = rules.iterator();
            while (r_it.hasNext()) {
            Rule r = (Rule)r_it.next();
            try {
                AlgebraSubstitution sigma = r.getLeft().matches(t);
                AlgebraTerm right = r.getRight();
                label.put(fsym.getName(), Integer.valueOf(countv+1));
                right.labelTerm(label);
                t = right.apply(sigma);
                return this.replaceAt(t, pi);
            }
            catch (UnificationException e) { }
            }
        }
        }
    }
    return null;
    }

    protected Vector<Position> getRewritePositions(Set<DefFunctionSymbol> preferredFuncs) {
    Vector<Position> pps = new Vector<Position>();
    Vector<Position> ops = new Vector<Position>();
    this.getRewritePositions(preferredFuncs, pps, ops, Position.create());
    pps.addAll(ops);
    return pps;
    }

    protected void getRewritePositions(Set<DefFunctionSymbol> preferredFuncs, Vector<Position> pps, Vector<Position> ops, Position pi) {
    if (!this.isVariable()) {
        Symbol sym = this.getSymbol();
        if (sym instanceof DefFunctionSymbol) {
        (preferredFuncs.contains(sym) ? pps : ops).add(pi);
        }
        Iterator it = this.getArguments().iterator();
        for (int i=0; it.hasNext(); i++) {
        AlgebraTerm t = (AlgebraTerm)it.next();
        Position tau = pi.shallowcopy();
        tau.add(i);
        t.getRewritePositions(preferredFuncs, pps, ops, tau);
        }
    }
    }

    public AlgebraTerm rewrite(int labellimit, int iterlimit, int depthlimit, Rule r, Map<SyntacticFunctionSymbol,Set<Rule>> rwrules, int depth) {
    try {
        AlgebraSubstitution sigma = r.getLeft().matches(this);
        return this.rewrite(labellimit, iterlimit, depthlimit, r, sigma, rwrules, depth);
    }
    catch (UnificationException e) {
        return null;
    }
    }

    public AlgebraTerm rewrite(int labellimit, int iterlimit, int depthlimit, Rule r, AlgebraSubstitution sigma, Map<SyntacticFunctionSymbol,Set<Rule>> rwrules, int depth) {
    Hashtable<String,Integer> label = (Hashtable<String,Integer>)this.getAttribute("label");
    if (label == null) {
        label = new Hashtable<String,Integer>();
    }
    Integer count = label.get(r.getLeft().getSymbol().getName());
    count = Integer.valueOf(count == null ? 1 : count.intValue()+1);
    label.put(this.sym.getName(), count);
    this.labelTerm(label);
    Iterator it = r.getConds().iterator();
    while (it.hasNext()) {
        Rule cond = (Rule)it.next();
        AlgebraTerm lc = cond.getLeft().apply(sigma);
        lc.labelTerm(label);
        AlgebraTerm rc = cond.getRight();
        AlgebraSubstitution tau = null;
        for (int j=0; j<iterlimit && tau == null && lc != null; j++) {
        try {
            tau = rc.matches(lc);
        }
        catch (UnificationException e) {
            lc = lc.limitRewriteStep(labellimit, iterlimit, depthlimit, rwrules, depth+1);
        }
        }
        if (tau == null) {
        return null;
        }
        sigma = sigma.compose(tau);
    }
    AlgebraTerm result = r.getRight();
    result.labelTerm(label);
    return result.apply(sigma);
    }

    /** Labels the term with a given label. E.g. every subterm whose
     *  root-symbol is a defining function-symbol gets the attribute
     *  "label" with the value given as label.
     *  @param label The label.
     */
    public void labelTerm(Hashtable<String,Integer> label) {
    if (this.isVariable()) {
        return;
    }
    if (this.getSymbol() instanceof DefFunctionSymbol) {
        this.setAttribute("label", new Hashtable<String,Integer>(label));
    }
    Iterator it = this.getArguments().iterator();
    while (it.hasNext()) {
        ((AlgebraTerm)it.next()).labelTerm(label);
    }
    }

    public void labelUnlabeled(Hashtable<String,Integer> label) {
    if (this.isVariable()) {
        return;
    }
    if (this.getAttribute("label") == null) {
        this.setAttribute("label", new Hashtable<String,Integer>(label));
        Iterator it = this.getArguments().iterator();
        while (it.hasNext()) {
        ((AlgebraTerm)it.next()).labelTerm(label);
        }
    }
    }

    /** Removes the labels from the term and its subterms.
     */
    public void unlabelTerm() {
    if (this.isVariable()) {
        return;
    }
    this.removeAttribute("label");
    Iterator it = this.getArguments().iterator();
    while (it.hasNext()) {
        ((AlgebraTerm)it.next()).unlabelTerm();
    }
    }

    /** Returns true iff all occuring function-symbols are terminating.
     */
    abstract public boolean isTerminating();

    /** Returns all positions where the root-symbol is a defining
     * function */
    public List<Position> getDefFunctionPositions() {
    Vector<Position> result = new Vector<Position>();
    Vector<AlgebraTerm> terms = new Vector<AlgebraTerm>();
    Vector<Position> positions = new Vector<Position>();
    terms.add(this);
    positions.add(Position.create());
    while (!terms.isEmpty()) {
        Position p = positions.remove(0);
        AlgebraTerm t = terms.remove(0);
        Symbol sym = t.getSymbol();
        if (sym instanceof DefFunctionSymbol) {
        result.add(p);
        }
        if (sym instanceof SyntacticFunctionSymbol) {
        int i = 0;
        Iterator it = t.getArguments().iterator();
        while (it.hasNext()) {
            AlgebraTerm nt = (AlgebraTerm)it.next();
            terms.add(nt);
            Position np = p.shallowcopy();
            np.add(i);
            positions.add(np);
            i++;
        }
        }
    }
    return result;
    }

    /** Returns a term where all subterms that are in the key-set of
     *  replacements are replaced by the corresponding value.
     */
    public AlgebraTerm termReplace(Hashtable replacements) {
    AlgebraTerm replacement = (AlgebraTerm)replacements.get(this);
    if (replacement != null) {
        return replacement.deepcopy();
    }
    if (this.isVariable()) {
        return this;
    }
    Vector<AlgebraTerm> newargs = new Vector<AlgebraTerm>();
    List<AlgebraTerm> args = this.getArguments();
    Iterator it = args.iterator();
    while (it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)it.next();
        newargs.add(arg.termReplace(replacements));
    }
    AlgebraTerm res = AlgebraFunctionApplication.create((SyntacticFunctionSymbol)this.getSymbol(), newargs);
    res.setAttributes(this.getAttributes());
    return res;
    }

    /** Returns whether this is a constructor-term. */
    public abstract boolean isConstructorTerm();

    /** Returns whether this is a ground-term. */
    public abstract boolean isGroundTerm();

    /** Returns whether this is a constructor-ground-term. */
    public boolean isConstructorGroundTerm() {
        return (this.isConstructorTerm() && this.isGroundTerm());
    }


    /** Returns the size of the term. */
    public abstract int size();

    public String toStringLabel() {
    StringBuffer out = new StringBuffer(this.getSymbol().getName());
    Hashtable label = (Hashtable)this.getAttribute("label");
    if (label != null) {
        out.append(label);
    }
    if (this.isVariable()) {
        return out.toString();
    }
    out.append("(");
    Iterator it = this.getArguments().iterator();
    while (it.hasNext()) {
        AlgebraTerm t = (AlgebraTerm)it.next();
        out.append(t.toStringLabel());
        if (it.hasNext()) {
        out.append(", ");
        }
    }
    out.append(")");
    return out.toString();
    }

    /** Create a set of constructor-terms that represent a
     *  non-satisfying equality-test with this term. We assume, that
     *  this term is a linear constructor term.
     */
    public Vector<AlgebraTerm> computeNoMatchConditions(FreshNameGenerator namegen, TypeContext typeContext) {
    Vector<AlgebraTerm> pattern = new Vector<AlgebraTerm>();
    pattern.add(AlgebraVariable.create(VariableSymbol.create(namegen.getFreshName("x",false), this.getSymbol().getSort())));
    Vector<Vector<AlgebraTerm>> patterns = new Vector<Vector<AlgebraTerm>>();
    patterns.add(pattern);
    pattern = new Vector<AlgebraTerm>();
    pattern.add(this);
    Program.considerPatternInToDoPatterns(patterns, pattern, namegen, typeContext);
    Vector<AlgebraTerm> out = new Vector<AlgebraTerm>();
    Iterator<Vector<AlgebraTerm>> it = patterns.iterator();
    while (it.hasNext()) {
        pattern = it.next();
        out.add(pattern.get(0));
    }
    return out;
    }

    /**
     * produces a new term where all occurrences of the
     * FIND-term are replaced by the REPLACE term
     * @param find
     * @param replace
     * @return a new term
     */
    final public AlgebraTerm replaceTermByTerm(AlgebraTerm find, AlgebraTerm replace) {
       if  (this.equals(find)) {
        return replace;
    }
       if (this.isVariable()) {
        return this;
    }
       if (this instanceof AlgebraFunctionApplication) {
           Iterator args = this.getArguments().iterator();
           List<AlgebraTerm> newArgs = new Vector<AlgebraTerm>();
           while (args.hasNext()) {
               AlgebraTerm arg = (AlgebraTerm) args.next();
               newArgs.add(arg.replaceTermByTerm(find,replace));
           }
           SyntacticFunctionSymbol f = (SyntacticFunctionSymbol) this.getSymbol();
           return AlgebraFunctionApplication.create(f,newArgs);
       } else {
           return null;
       }

    }

    /**
     * Checks if this term only contains unary function symbols
     */
    public boolean isUnary() {
        return CheckUnaryVisitor.apply(this);
    }

    /**
     * Checks if this term only contains unary function symbols or
     * constants
     */
    public boolean isMaxUnary() {
        return CheckMaxUnaryVisitor.apply(this);
    }



    /**
     * Reverse this term. Only possible for terms where isMaxUnary is True.
     * @return A new term in reverse order.
     */
    public AlgebraTerm reverse(FreshNameGenerator fg) {
        return ReverseVisitor.apply(this, fg);
    }

    /**
     * Updates which symbols are constructors and which are defined function symbols.
     */
    public AlgebraTerm updateConsDef(Set<SyntacticFunctionSymbol> toCons, Set<SyntacticFunctionSymbol> toDef) {
        return UpdateConsDefVisitor.apply(this, toCons, toDef);
    }

    public Map<AlgebraTerm, List<Position>> getSubTermsWithPositions() {
        return GetSubTermsWithPositionsVisitor.apply(this);
    }

    @Override
    public boolean isFormula() {
        return false;
    }

    @Override
    public boolean isTerm() {
        return true;
    }

    public boolean isMetaFunctionApplication() {
        return false;
    }

    public abstract int width();

    public AlgebraTerm erase() {
        return EraseAnnotatedFormulaVisitor.apply(this);
    }

    public Formula toFormula(Program program) {
        return TermToFormulaVisitor.apply(this, program);
    }

    @Override
    public TermOrFormula getSubPart(Position p) throws InvalidPositionException {

        TermOrFormula returnValue = SubPartVisitor.apply(this, p);

        if (returnValue == null) {
            throw new InvalidPositionException(p,
                    "Position not contained in Term.");
        } else {
            return returnValue;
        }

    }

    public Set<Position> getModifiablePosition(Program program) {
        return GetAllModifiablePositionsVisitor.apply(this, program);
    }

    public abstract aprove.verification.dpframework.BasicStructures.TRSTerm toNewTerm();

    /**
     * states whether the term is an LA term
     *
     * @param laProgram the context
     * @return true iff the term is an LA term
     */
    public boolean isLA(LAProgramProperties laProgram) {
        if(laProgram == null){
            return false;
        }

        Sort termSort = this.getSort();
        if(!termSort.equals(laProgram.sortNat)){
            return false;
        }

        LinearTermNormalizer ltn = new LinearTermNormalizer(laProgram);
        this.apply(ltn);

        return ltn.isLinearTerm();
    }

    public void toACL2(StringBuffer sb, int indent, FreshNameGenerator fng, Program.RuleInfo ruleInfo, boolean fullLists) {
        ToACL2Visitor.apply(this, sb, indent, fng, ruleInfo, fullLists);
    }



}
