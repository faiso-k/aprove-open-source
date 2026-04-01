package aprove.verification.theoremprover.Simplifier;

import java.util.*;
import java.util.logging.*;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

@NoParams
public class BoolPredefSimplifier extends SimplifierProcessor {

    public SimplifierObligation obl;

    public BoolPredefSimplifier(){
        super("BoolPredef Simplifier","BPT","BoolPredef Transformation");
    }

    @Override
    public SimplifierObligation simplify(SimplifierObligation obl) {
        this.obl = obl.shallowcopy();
        if (this.boolPredefTransformation()) {
            this.setMessage("BoolPredef Transformation");
            return this.obl;
        }
        return null;
    }


    /** Performs various transformation of predefined boolean functions.
     *  This algorithm accumulates the transformation-algorithm of
     *  this class to an automated transformation of all functions
     *  that are listed in defs.
     *  @return true iff something has changed due to the transformation.
     */
    public boolean boolPredefTransformation() {
    //log.log(Level.FINER, "Simplifier: Performing simplification of predefined boolean function.\n");
    boolean changed = this.liftMatching();
    Iterator it = (new Vector<DefFunctionSymbol>(this.obl.defs)).iterator();
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
        int sig = fsym.getSignatureClass();
        if (sig == Symbol.MAINSIG || (sig == Symbol.DEFAULTSIG && !this.obl.isProjection(fsym))) {
        if (this.boolPredefTransformation(fsym)) {
            changed = true;
            this.obl.symbolicEvaluation(fsym);
        }
        }
    }
    return changed;
    }

    /** Performs various transformation of predefined boolean functions
     *  on the function given by fsym.
     *  @return true iff something has changed due to the transformation.
     */
    public boolean boolPredefTransformation(DefFunctionSymbol fsym) {
    boolean changed = false;
    while (this.phiTransformation(fsym) ||
        this.isaTransformation(fsym) ||
        this.equalityCheckTransformation(fsym) ||
        this.obl.liftMatching(fsym) ||
        this.obl.conditionMatchTransformation(fsym)) {
        changed = true;
    }
    return changed;
    }


    /* IsA-Transform */

    /** Performs an IsA-transformation on all functions if possible.
     *  @return true iff an IsA-transformation could be done.
     */
    public boolean isaTransformation() {
    SimplifierProcessor.log.log(Level.FINER, "Simplifier: Performing IsA-transformation.\n");
    Iterator it = (new Vector<DefFunctionSymbol>(this.obl.defs)).iterator();
    boolean changed = false;
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
        int sig = fsym.getSignatureClass();
        if (sig == Symbol.MAINSIG || (sig == Symbol.DEFAULTSIG && !this.obl.isProjection(fsym))) {
        changed = this.isaTransformation(fsym) || changed;
        }
    }
    this.liftMatching();
    return changed;
    }

    /** Performs an IsA-transformation on the function fsym if possible.
     *  @return true iff an IsA-transformation could be done.
     */
    public boolean isaTransformation(DefFunctionSymbol fsym) {
    //log.log(Level.FINEST, "Simplifier: Performing IsA-Transformation on "+fsym.getName()+".\n");
    Vector<Rule> defrules = new Vector<Rule>((Set<Rule>)this.obl.defsrules.get(fsym));
    Set<Rule> newdefrules = new HashSet<Rule>();
    boolean changed = false;
    while (!defrules.isEmpty()) {
        Rule r1 = defrules.remove(0);
        Vector<Rule> rulesubset = new Vector<Rule>();
        rulesubset.add(r1);
        Iterator it = defrules.iterator();
        while (it.hasNext()) {
        Rule r2 = (Rule)it.next();
        if (r2.getLeft().equals(r1.getLeft())) {
            it.remove();
            rulesubset.add(r2);
        }
        }
        changed = this.isaTransformation(rulesubset, newdefrules, 0) || changed;
    }
    if (changed) {
        this.obl.defsrules.put(fsym, newdefrules);
        this.obl.updateSymbol(fsym, newdefrules);
        return true;
    }
    return false;
    }

    /** Performs an IsA-transformation on a given rulesubset of a given
     *  function where the first n conditions are equal and are ignored.
     *  Returns true if an IsA-transformation could be done.
     */
    protected boolean isaTransformation(Vector<Rule> rulesubset, Set<Rule> newdefrules, int n) {
        if (rulesubset.size() == 0) {
            return false;
        }
    Rule r = rulesubset.get(0);
    if (r.getConds().size() <= n) {
        newdefrules.addAll(rulesubset);
        return false;
    }
    else {
        boolean changed = false;
        while (!rulesubset.isEmpty()) {
        Rule r1 = rulesubset.remove(0);
        Rule cond1 = r1.getConds().get(n);
        Vector<Rule> equivCondsRules = new Vector<Rule>();
        equivCondsRules.add(r1);
        Iterator<Rule> it = rulesubset.iterator();
        while (it.hasNext()) {
            Rule r2 = it.next();
            Rule cond2 = r2.getConds().get(n);
            if (cond1.equals(cond2)) {
            it.remove();
            equivCondsRules.add(r2);
            }
        }
        AlgebraTerm condLeft = cond1.getLeft();
        AlgebraTerm condRight = cond1.getRight();
        String name = condLeft.getSymbol().getName();
        if (name.startsWith("isa_")) {
            changed = true;
            ConstructorSymbol csym = this.obl.program.getConstructorSymbol(name.substring(4));

            AlgebraTerm csymType = TypeTools.getResultTerm(this.obl.typeContext.getSingleTypeOf(csym).getTypeMatrix());
            TypeDefinition td = this.obl.typeContext.getTypeDef(csymType.getSymbol().getName());

            name = this.obl.symbnames.getFreshName("x", false);
            condLeft = condLeft.getArgument(0);
            AlgebraTerm condTrue = AlgebraFunctionApplication.createWithDisjointVars(csym, this.obl.symbnames);
            Vector<AlgebraTerm> condFalse = new Vector<AlgebraTerm>();

            Set<ConstructorSymbol> consSymbs = new HashSet(td.getDeclaredSymbols());
            Iterator<ConstructorSymbol> it2 = consSymbs.iterator();


            //Iterator<ConstructorSymbol> it2 = sort.getConstructorSymbols().iterator();
            while (it2.hasNext()) {
            ConstructorSymbol csym2 = it2.next();
            if (!csym.equals(csym2)) {
                condFalse.add(AlgebraFunctionApplication.createWithDisjointVars(csym2, this.obl.symbnames));
            }
            }

            Vector<Rule> equivCondRules2 = new Vector<Rule>();
            it = equivCondsRules.iterator();
            while (it.hasNext()) {
            Rule r2 = it.next();
            List<Rule> conds = r2.getConds();
            Rule cond2 = conds.get(n);
            if (cond2.getRight().getSymbol().equals(this.obl.cTrue)) {
                Vector<Rule> newconds = new Vector<Rule>(conds);
                newconds.set(n, Rule.create(condLeft.deepcopy(), condTrue.deepcopy()));
                equivCondRules2.add(Rule.create(newconds, r2.getLeft(), r2.getRight()));
            }
            else {
                Iterator c_it = condFalse.iterator();
                while (c_it.hasNext()) {
                AlgebraTerm t = (AlgebraTerm)c_it.next();
                Vector<Rule> newconds = new Vector<Rule>(conds);
                newconds.set(n, Rule.create(condLeft.deepcopy(), t.deepcopy()));
                equivCondRules2.add(Rule.create(newconds, r2.getLeft(), r2.getRight()));
                }
            }
            }
            equivCondsRules = equivCondRules2;
        }
        changed = this.isaTransformation(equivCondsRules, newdefrules, n+1) || changed;
        }
        return changed;
    }
    }

    /** lifts the matching of the first condition into the lhs of the rule.
     *  @return true iff transformation was possible.
     */
    protected boolean liftMatching() {
    boolean changed = false;
    Iterator it = (new Vector(this.obl.defs)).iterator();
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
        int sig = fsym.getSignatureClass();
        if (sig == Symbol.MAINSIG || (sig == Symbol.DEFAULTSIG && !this.obl.isProjection(fsym))) {
        changed = this.obl.liftMatching(fsym) || changed;
        }
    }
    return changed;
    }

    /* Phi-Transform */

    /** Performs a Phi-transformation on all functions if possible.
     *  @return true iff an IsA-transformation could be done.
     */
    public boolean phiTransformation() {
    Iterator it = (new Vector(this.obl.defs)).iterator();
    boolean changed = false;
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
        int sig = fsym.getSignatureClass();
        if (sig == Symbol.MAINSIG || (sig == Symbol.DEFAULTSIG && !this.obl.isProjection(fsym))) {
        changed = this.phiTransformation(fsym) || changed;
        }
    }
    this.liftMatching();
    return changed;
    }

    /** Performs a Phi-transformation on the function fsym if possible.
     *  @return true iff an IsA-transformation could be done.
     */
    public boolean phiTransformation(DefFunctionSymbol fsym) {
    //log.log(Level.FINEST, "Simplifier: Performing phi-transformation on "+fsym.getName()+".\n");
    Vector<Rule> defrules = new Vector<Rule>((Set<Rule>)this.obl.defsrules.get(fsym));
    Set<Rule> newdefrules = new HashSet<Rule>();
    boolean changed = false;
    while (!defrules.isEmpty()) {
        Rule r1 = defrules.remove(0);
        Vector<Rule> rulesubset = new Vector<Rule>();
        rulesubset.add(r1);
        Iterator it = defrules.iterator();
        while (it.hasNext()) {
        Rule r2 = (Rule)it.next();
        if (r2.getLeft().equals(r1.getLeft())) {
            it.remove();
            rulesubset.add(r2);
        }
        }
        changed = this.phiTransformation(rulesubset, newdefrules, 0) || changed;
    }
    if (changed) {
        this.obl.defsrules.put(fsym, newdefrules);
        this.obl.updateSymbol(fsym, newdefrules);
        return true;
    }
    return false;
    }

    /** Performs an Phi-transformation on a given rulesubset of a given
     *  function where the first n conditions are equal and are ignored.
     *  Returns true if an IsA-transformation could be done.
     */
    protected boolean phiTransformation(Vector<Rule> rulesubset, Set<Rule> newdefrules, int n) {
    Rule r = rulesubset.get(0);
    if (r.getConds().size() <= n) {
        newdefrules.addAll(rulesubset);
        return false;
    }
    else {
        boolean changed = false;
        while (!rulesubset.isEmpty()) {
        Rule r1 = rulesubset.remove(0);
        Rule cond1 = r1.getConds().get(n);
        Vector<Rule> equivCondsRules = new Vector<Rule>();
        equivCondsRules.add(r1);
        Iterator<Rule> it = rulesubset.iterator();
        while (it.hasNext()) {
            Rule r2 = it.next();
            Rule cond2 = r2.getConds().get(n);
            if (cond1.equals(cond2)) {
            it.remove();
            equivCondsRules.add(r2);
            }
        }
        AlgebraTerm condLeft = cond1.getLeft();
        AlgebraTerm condRight = cond1.getRight();
        Symbol sym = condLeft.getSymbol();
        if (sym.equals(this.obl.fAnd)) {
            changed = true;
            AlgebraTerm condA = condLeft.getArgument(0);
            AlgebraTerm condB = condLeft.getArgument(1);
            Vector<Rule> equivCondRules2 = new Vector<Rule>();
            it = equivCondsRules.iterator();
            while (it.hasNext()) {
            Rule r2 = it.next();
            List<Rule> conds = r2.getConds();
            Rule condn = conds.get(n);
            if (condn.getRight().getSymbol().equals(this.obl.cTrue)) {
                // true, true
                Vector<Rule> newconds = new Vector<Rule>(conds);
                newconds.set(n, Rule.create(condA.deepcopy(), AlgebraFunctionApplication.create(this.obl.cTrue)));
                newconds.insertElementAt(Rule.create(condB.deepcopy(), AlgebraFunctionApplication.create(this.obl.cTrue)), n+1);
                equivCondRules2.add(Rule.create(newconds, r2.getLeft(), r2.getRight()));
            }
            else {
                // true, false
                Vector<Rule> newconds = new Vector<Rule>(conds);
                newconds.set(n, Rule.create(condA.deepcopy(), AlgebraFunctionApplication.create(this.obl.cTrue)));
                newconds.insertElementAt(Rule.create(condB.deepcopy(), AlgebraFunctionApplication.create(this.obl.cFalse)), n+1);
                equivCondRules2.add(Rule.create(newconds, r2.getLeft(), r2.getRight()));
                // false, true
                newconds = new Vector<Rule>(conds);
                newconds.set(n, Rule.create(condA.deepcopy(), AlgebraFunctionApplication.create(this.obl.cFalse)));
                newconds.insertElementAt(Rule.create(condB.deepcopy(), AlgebraFunctionApplication.create(this.obl.cTrue)), n+1);
                equivCondRules2.add(Rule.create(newconds, r2.getLeft(), r2.getRight()));
                // false, false
                newconds = new Vector<Rule>(conds);
                newconds.set(n, Rule.create(condA.deepcopy(), AlgebraFunctionApplication.create(this.obl.cFalse)));
                newconds.insertElementAt(Rule.create(condB.deepcopy(), AlgebraFunctionApplication.create(this.obl.cFalse)), n+1);
                equivCondRules2.add(Rule.create(newconds, r2.getLeft(), r2.getRight()));
            }
            }
            equivCondsRules = equivCondRules2;
            this.phiTransformation(equivCondsRules, newdefrules, n);
        }
        else if (sym.equals(this.obl.fOr)) {
            changed = true;
            AlgebraTerm condA = condLeft.getArgument(0);
            AlgebraTerm condB = condLeft.getArgument(1);
            Vector<Rule> equivCondRules2 = new Vector<Rule>();
            it = equivCondsRules.iterator();
            while (it.hasNext()) {
            Rule r2 = it.next();
            List<Rule> conds = r2.getConds();
            Rule condn = conds.get(n);
            if (condn.getRight().getSymbol().equals(this.obl.cTrue)) {
                // true, true
                Vector<Rule> newconds = new Vector<Rule>(conds);
                newconds.set(n, Rule.create(condA.deepcopy(), AlgebraFunctionApplication.create(this.obl.cTrue)));
                newconds.insertElementAt(Rule.create(condB.deepcopy(), AlgebraFunctionApplication.create(this.obl.cTrue)), n+1);
                equivCondRules2.add(Rule.create(newconds, r2.getLeft(), r2.getRight()));
                // true, false
                newconds = new Vector<Rule>(conds);
                newconds.set(n, Rule.create(condA.deepcopy(), AlgebraFunctionApplication.create(this.obl.cTrue)));
                newconds.insertElementAt(Rule.create(condB.deepcopy(), AlgebraFunctionApplication.create(this.obl.cFalse)), n+1);
                equivCondRules2.add(Rule.create(newconds, r2.getLeft(), r2.getRight()));
                // false, true
                newconds = new Vector<Rule>(conds);
                newconds.set(n, Rule.create(condA.deepcopy(), AlgebraFunctionApplication.create(this.obl.cFalse)));
                newconds.insertElementAt(Rule.create(condB.deepcopy(), AlgebraFunctionApplication.create(this.obl.cTrue)), n+1);
                equivCondRules2.add(Rule.create(newconds, r2.getLeft(), r2.getRight()));
            }
            else {
                // false, false
                Vector<Rule> newconds = new Vector<Rule>(conds);
                newconds.set(n, Rule.create(condA.deepcopy(), AlgebraFunctionApplication.create(this.obl.cFalse)));
                newconds.insertElementAt(Rule.create(condB.deepcopy(), AlgebraFunctionApplication.create(this.obl.cFalse)), n+1);
                equivCondRules2.add(Rule.create(newconds, r2.getLeft(), r2.getRight()));
            }
            }
            equivCondsRules = equivCondRules2;
            this.phiTransformation(equivCondsRules, newdefrules, n);
        }
        else if (sym.equals(this.obl.fNot)) {
            changed = true;
            AlgebraTerm condA = condLeft.getArgument(0);
            Vector<Rule> equivCondRules2 = new Vector<Rule>();
            it = equivCondsRules.iterator();
            while (it.hasNext()) {
            Rule r2 = it.next();
            List<Rule> conds = r2.getConds();
            Rule condn = conds.get(n);
            if (condn.getRight().getSymbol().equals(this.obl.cTrue)) {
                // false
                Vector<Rule> newconds = new Vector<Rule>(conds);
                newconds.set(n, Rule.create(condA.deepcopy(), AlgebraFunctionApplication.create(this.obl.cFalse)));
                equivCondRules2.add(Rule.create(newconds, r2.getLeft(), r2.getRight()));
            }
            else {
                // true
                Vector<Rule> newconds = new Vector<Rule>(conds);
                newconds.set(n, Rule.create(condA.deepcopy(), AlgebraFunctionApplication.create(this.obl.cTrue)));
                equivCondRules2.add(Rule.create(newconds, r2.getLeft(), r2.getRight()));
            }
            }
            equivCondsRules = equivCondRules2;
            this.phiTransformation(equivCondsRules, newdefrules, n);
        }
        else {
            changed = this.phiTransformation(equivCondsRules, newdefrules, n+1) || changed;
        }
        }
        return changed;
    }
    }


    /* Equality-Check-Transform */

    /** Performs an equality-check-transformation on the function given by fsym.
     *  If a condition has the form t_1 == t_2 -&gt; true and t_2 is a
     *  constructor-groundterm, than this condition can be replaced by
     *  t_1 -&gt; t_2. If the rhs of the conditon is false, one has to
     *  create new rules where this conditon is replaced with a condition
     *  t_1 -&gt; t_2' where t_2' is a constructor-term that does not
     *  match t_2.
     *  It t_1 is a constructor-groundterm one can proceed analogously.
     */
    public boolean equalityCheckTransformation(DefFunctionSymbol fsym) {
//    log.log(Level.FINEST, "Simplifier: Performing equality-check-transformation on "+fsym.getName()+".\n");
    Vector<Rule> defrules = new Vector<Rule>((Set<Rule>)this.obl.defsrules.get(fsym));
    Set<Rule> newdefrules = new HashSet<Rule>();
    boolean changed = false;
    while (!defrules.isEmpty()) {
        Rule r1 = defrules.remove(0);
        Vector<Rule> rulesubset = new Vector<Rule>();
        rulesubset.add(r1);
        Iterator<Rule> it = defrules.iterator();
        while (it.hasNext()) {
        Rule r2 = it.next();
        if (r2.getLeft().equals(r1.getLeft())) {
            it.remove();
            rulesubset.add(r2);
        }
        }
        changed = this.equalityCheckTransformation(rulesubset, newdefrules, 0) || changed;
    }
    if (changed) {
        this.obl.defsrules.put(fsym, newdefrules);
        this.obl.updateSymbol(fsym, newdefrules);
        return true;
    }
    return false;
    }

    protected boolean equalityCheckTransformation(Vector<Rule> rulesubset, Set<Rule> newdefrules, int n) {
    Rule r = rulesubset.get(0);
    if (r.getConds().size() <= n) {
        newdefrules.addAll(rulesubset);
        return false;
    }
    else {
        boolean changed = false;
        while (!rulesubset.isEmpty()) {
        Rule r1 = rulesubset.remove(0);
        Rule cond1 = r1.getConds().get(n);
        Vector<Rule> equivCondsRules = new Vector<Rule>();
        equivCondsRules.add(r1);
        Iterator<Rule> it = rulesubset.iterator();
        while (it.hasNext()) {
            Rule r2 = it.next();
            Rule cond2 = r2.getConds().get(n);
            if (cond1.equals(cond2)) {
            it.remove();
            equivCondsRules.add(r2);
            }
        }
        AlgebraTerm condLeft = cond1.getLeft();
        AlgebraTerm condRight = cond1.getRight();
        Symbol sym = condLeft.getSymbol();
        if (sym.getName().startsWith("equal_")) {
            AlgebraTerm condA = null; // The constructor-ground-term that has to be matched.
            AlgebraTerm condB = null; // The term that has to match.
            if (condLeft.getArgument(0).isConstructorGroundTerm()) {
            condA = condLeft.getArgument(0);
            condB = condLeft.getArgument(1);
            }
            else if (condLeft.getArgument(1).isConstructorGroundTerm()) {
            condB = condLeft.getArgument(0);
            condA = condLeft.getArgument(1);
            }
            if (condA != null) {
            changed = true;
            Rule newcond = Rule.create(condB, condA);
            Vector<Rule> no_match_conds = new Vector<Rule>();
            Iterator nmc_it = condA.computeNoMatchConditions(this.obl.symbnames, this.obl.typeContext).iterator();
            while (nmc_it.hasNext()) {
                AlgebraTerm nmc = (AlgebraTerm)nmc_it.next();
                no_match_conds.add(Rule.create(condB, nmc));
            }
            Vector<Rule> equivCondRules2 = new Vector<Rule>();
            it = equivCondsRules.iterator();
            while (it.hasNext()) {
                Rule r2 = it.next();
                List<Rule> conds = r2.getConds();
                Rule condn = conds.get(n);
                if (condn.getRight().getSymbol().equals(this.obl.cTrue)) {
                // match against the constructor-ground-term
                Vector<Rule> newconds = new Vector<Rule>(conds);
                newconds.set(n, newcond.deepcopy());
                equivCondRules2.add(Rule.create(newconds, r2.getLeft(), r2.getRight()));
                }
                else {
                // match against everything else
                nmc_it = no_match_conds.iterator();
                while (nmc_it.hasNext()) {
                    Rule no_match_cond = (Rule)nmc_it.next();
                    Vector<Rule> newconds = new Vector<Rule>(conds);
                    newconds.set(n, no_match_cond.deepcopy());
                    equivCondRules2.add(Rule.create(newconds, r2.getLeft(), r2.getRight()));
                }
                }
            }
            equivCondsRules = equivCondRules2;
            }
        }
        changed = this.equalityCheckTransformation(equivCondsRules, newdefrules, n+1) || changed;
        }
        return changed;
    }
    }


    /* Contradiction Elimination */

    public void contradictionElimination() {
    Iterator it = this.obl.defs.iterator();
    while (it.hasNext()) {
        this.contradictionElimination((DefFunctionSymbol)it.next());
    }
    }

    public boolean contradictionElimination(DefFunctionSymbol fsym) {
    boolean changed = false;
    Set<Rule> rules = (Set<Rule>)this.obl.defsrules.get(fsym);
    Set<Rule> newrules = new HashSet<Rule>();
    Iterator r_it = rules.iterator();
    while (r_it.hasNext()) {
        Rule r = (Rule)r_it.next();
        Hashtable whatconds = new Hashtable();
        Vector<Rule> newconds = new Vector<Rule>();
        boolean iscontradictory = false;
        Iterator c_it = r.getConds().iterator();
        while (!iscontradictory && c_it.hasNext()) {
        Rule cond = (Rule)c_it.next();
        AlgebraTerm thisrhs = cond.getRight();
        if (!thisrhs.getVars().isEmpty()) {
            // We must keep assignments to variables.
            newconds.add(cond);
        }
        else {
            AlgebraTerm otherrhs = (AlgebraTerm)whatconds.get(cond.getLeft());
            // If we have not seen such a lhs, we have to keep this condition
            if (otherrhs == null) {
            whatconds.put(cond.getLeft(), thisrhs);
            newconds.add(cond);
            }
            else {
            if (otherrhs.equals(thisrhs)) {
                // If we have seen this lhs with this rhs we can ignore this condition.
                changed = true;
            }
            else {
                if (thisrhs.isMatchable(otherrhs) || otherrhs.isMatchable(thisrhs)) {
                // If one matches the other (or vice versa) we have to keep this condition.
                newconds.add(cond);
                }
                else {
                // None matches the other. Therefore, this rule is contradictory.
                iscontradictory = true;
                }
            }
            }
        }
        }
        if (!iscontradictory) {
        newrules.add(Rule.create(newconds, r.getLeft(), r.getRight()));
        }
        else {
        changed = true;
        }
    }
    if (changed) {
        this.obl.defsrules.put(fsym, newrules);
        this.obl.updateSymbol(fsym, newrules);
        return true;
    }
    return false;
    }

}
