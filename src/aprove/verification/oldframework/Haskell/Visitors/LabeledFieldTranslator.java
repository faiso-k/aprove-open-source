package aprove.verification.oldframework.Haskell.Visitors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/**
 * This visitor translates
 *   - constructions with labeled fields into standard constructions
 *   - updates with labeled fields into case constructs that preserve unmentioned values
 *
 * after application, no labeled fields are used anymore
 *
 * @author matraf
 *
 */
@SuppressWarnings("serial")
public class LabeledFieldTranslator extends HaskellVisitor {

    private boolean isPattern = false;
    private Prelude prelude;
    private Module curModule;
    private final Stack<EntityFrame> entityFramesStack = new Stack<EntityFrame>();

    public LabeledFieldTranslator() {
    }

    public LabeledFieldTranslator(final Prelude prelude) {
        this.prelude = prelude;
    }

    /**
     * marking the start of a rule pattern
     * and tracking the definitions of variables
     */
    @Override
    public void fcaseHaskellRule(final HaskellRule ho) {
        this.isPattern = true;
        this.entityFramesStack.push(ho.getEntityFrame());
    }

    /**
     * marking the end of a rule pattern
     */
    @Override
    public void icaseHaskellRule(final HaskellRule ho) {
        this.isPattern = false;
    }

    /**
     * tracking the definitions of variables
     */
    @Override
    public HaskellObject caseHaskellRule(final HaskellRule ho) {
        this.entityFramesStack.pop();
        return ho;
    }

    /**
     * tracking the definitions of variables
     */
    @Override
    public void fcaseLetExp(final LetExp ho) {
        this.entityFramesStack.push(ho.getEntityFrame());
    }

    /**
     * tracking the definitions of variables
     */
    @Override
    public HaskellObject caseLetExp(final LetExp ho) {
        this.entityFramesStack.pop();
        return ho;
    }

    /**
     * keeping track of the current module
     * and the definitions of variables
     */
    @Override
    public void fcaseModule(final Module mod) {
        this.curModule = mod;
        this.entityFramesStack.push(mod);
    }

    /**
     * keeping track of the current module
     * and the definitions of variables
     */
    @Override
    public HaskellObject caseModule(final Module mod) {
        this.curModule = null;
        this.entityFramesStack.pop();
        return mod;
    }

    /**
     * returns the current entity frame, which stores local variables
     */
    private EntityFrame getCurrentEntityFrame() {
        if (!this.entityFramesStack.isEmpty()) {
            return this.entityFramesStack.peek();
        }
        return this.prelude.getModules().getMainModule();
    }

    /**
     * returns the currently active module
     * this is the module in this.curModule, or Main if this.curModule is null
     */
    private Module getCurrentModule() {
        if (this.curModule == null) {
            return this.prelude.getModules().getMainModule();
        } else {
            return this.curModule;
        }
    }

    /**
     * return the constructors the field is defined for
     */
    private Set<Cons> getFieldsType(final VarEntity field) {
        final Set<Cons> conss = new HashSet<Cons>();
        for (final HaskellRule rule : ((Function) field.getValue()).getRules()) {
            final HaskellObject obj = HaskellTools.getLeftMost(rule.getPatterns().get(0));
            if (!(obj instanceof Cons)) {
                return null;
            } else {
                final Cons cons = (Cons) obj;
                final ConsEntity consEntity = (ConsEntity) cons.getSymbol().getEntity();
                if (!this.containsEquivalentAtom(consEntity.getSelectors(), new Var(new HaskellNamedSym(field)))) {
                    return null;
                } else {
                    conss.add(cons);
                }
            }
        }
        return conss;
    }

    /**
     * returns whether a set of atoms contains a specified atom
     */
    private boolean containsEquivalentAtom(final Collection<? extends Atom> haystack, final Atom needle) {
        for (final Atom cons : haystack) {
            if (needle.equivalentTo(cons)) {
                return true;
            }
        }
        return false;
    }

    /**
     * when encountering a constructor with field equations, rewrite it to a standard constructor
     */
    @Override
    public HaskellObject caseLabCons(final LabCons ho) {
        final Cons newCons = new Cons(Copy.deep(ho.getCons().getSymbol()));
        final List<HaskellObject> hos = new LinkedList<HaskellObject>();
        hos.add(newCons);
        final Set<Var> seenFieldVars = new HashSet<Var>(ho.getFieldEquations().size());
        final ConsEntity consEnt = (ConsEntity) ho.getCons().getSymbol().getEntity();

        // duplicating the list of field equations, so that we can remove from it
        final List<FieldEqu> fieldEqus = ho.getFieldEquations();

        // iterating over all fields of this constructor, looking for a match in the equations
        final Iterator<Boolean> strictness = consEnt.getStrictness().iterator();
        for (final Var field : consEnt.getSelectors()) {
            final boolean isStrict = strictness.next();
            boolean foundField = false;

            final Iterator<FieldEqu> fieldEqu_it = fieldEqus.iterator();
            while (fieldEqu_it.hasNext()) {
                final FieldEqu equ = fieldEqu_it.next();

                // if there is a match: remove the equation and test whether there has been a field equation with this name before
                if (((Var) equ.getVariable()).getSymbol().getName(false).equals(field.getSymbol().getName(false))) {
                    fieldEqu_it.remove();
                    if (seenFieldVars.add(field)) {
                        foundField = true;
                        hos.add(equ.getExpression());

                        final Var var = (Var) equ.getVariable();
                        final Module curMod = this.getCurrentModule();
                        final Set<HaskellEntity> varEnts = curMod.getEntities(var.getSymbol(), HaskellEntity.Sort.VAR);

                        // should never happen
                        if (aprove.Globals.useAssertions) {
                            assert (varEnts.size() == 1) : "could not determine field for "
                                + var.getSymbol().getName(false);
                        }

                        // getting the leftmost item in the pattern of the first (and only) rule for the selector
                        // this should be the constructor this selector is defined for
                        final VarEntity varEnt = (VarEntity) varEnts.iterator().next();
                        final Set<Cons> conss = this.getFieldsType(varEnt);
                        // there should be a constructor, and it should be the constructor that is currently constructed
                        if ((conss == null) || (!this.containsEquivalentAtom(conss, ho.getCons()))) {
                            HaskellError.output(equ, "unknown field");
                        }

                    } else {
                        HaskellError.output(equ, "Repeated field name");
                    }
                }
            }
            if (!foundField) {
                // if we are in a pattern and a field was not specified,
                // any value will match => add a joker pattern
                if (this.isPattern) {
                    hos.add(new JokerPat());
                } else {
                    // if this field was marked as strict, then it must be defined => Error
                    if (isStrict) {
                        HaskellError.output(ho, "strict field \"" + field.getSymbol().getName(false)
                            + "\" was not defined");
                    }
                    // if we are not in a pattern, then we are
                    // constructing an object => set field to undefined
                    final HaskellNamedSym undefSym = new HaskellNamedSym("", "undefined");
                    undefSym.setEntity(this.prelude.getEntity(undefSym, HaskellEntity.Sort.VAR));
                    final Var undef = new Var(undefSym);
                    hos.add(undef);
                }
            }
        }

        // if there are still Field equations left, those variables are no fields
        if (!fieldEqus.isEmpty()) {
            String errorString = "The following fields do not exist for this constructor: ";
            String sep = "";
            for (final FieldEqu equ : fieldEqus) {
                errorString += sep + ((Var) equ.getVariable()).getSymbol();
                sep = ", ";
            }
            HaskellError.output(ho, errorString);
        }

        final HaskellObject res = HaskellTools.buildApplies(hos);
        return res;
    }

    /**
     * translates an update<br>
     * <code>exp { v_1 = exp_1, ..., v_n = exp_n }</code><br>
     * into<br>
     * <code>
     * case exp of <br>
     *   C_1 s_11 ... s_1n_1 = C_1 t_11 ... t_1n_1<br>
     *   ...<br>
     *   C_m s_m1 ... s_mn_m = C_m t_m1 ... t_mn_m<br>
     * </code><br>
     * <br>
     * where<br>
     *   <code>s_ij</code> = <code>_</code>    if the j-th field of <code>C_i</code> is in {<code>v_1</code>, ..., <code>v_n</code>}<br>
     *   <code>s_ij</code> = <code>w_ij</code> otherwise (where <code>w_ij</code> is a fresh variable)<br>
     * and where<br>
     *   <code>t_ij</code> = <code>exp_k</code> if the j-th field of <code>C_i</code> is <code>v_k</code><br>
     *   <code>t_ij</code> = <code>w_ij</code>  otherwise<br>
     * <br>
     * for all 1 <= i <= m, 1 <= j <= n_i
     */
    @Override
    public HaskellObject caseLabUpdate(final LabUpdate ho) {
        final List<AltExp> altExps = new LinkedList<AltExp>();

        final Module curMod = this.getCurrentModule();

        // caching the field assignments (using Strings, since Vars do not have equals)
        final Map<String, HaskellExp> var2exp = new HashMap<String, HaskellExp>();

        // determining the constructors that contain all specified fields
        Set<Cons> conssContainingFields = null;
        assert (!ho.getFieldEquations().isEmpty());
        for (final FieldEqu equ : ho.getFieldEquations()) {
            final Var var = (Var) equ.getVariable();

            if (var2exp.get(var.getSymbol().getName(false)) == null) {
                var2exp.put(var.getSymbol().getName(false), equ.getExpression());
            } else {
                HaskellError.output(var, "duplicate field");
            }

            // getting the entity of the field
            final Set<HaskellEntity> varEnts = curMod.getEntities(var.getSymbol(), HaskellEntity.Sort.VAR);
            // should never happen
            if (aprove.Globals.useAssertions) {
                assert (varEnts.size() == 1) : "could not determine field for " + var.getSymbol().getName(false);
            }
            final VarEntity varEnt = (VarEntity) varEnts.iterator().next();

            // getting the constructors this field is defined for
            final Set<Cons> conss = this.getFieldsType(varEnt);
            if (conss == null) {
                HaskellError.output(var, "unknown field name");
            }
            if (conssContainingFields == null) {
                conssContainingFields = conss;
            } else {
                conssContainingFields.retainAll(conss);
            }
        }

        if ((conssContainingFields == null) || (conssContainingFields.isEmpty())) {
            HaskellError.output(ho, "no constructor found with all these fields");
        }

        // building the alternative constructors that have all the the fields specified
        for (final Cons cons : conssContainingFields) {
            final ConsEntity consEnt = (ConsEntity) cons.getSymbol().getEntity();
            // building the pattern of the case alternative
            final List<HaskellObject> hosPat = new ArrayList<HaskellObject>(consEnt.getArity() + 1);
            final List<HaskellObject> hosExp = new ArrayList<HaskellObject>(consEnt.getArity() + 1);
            final Cons newCons = new Cons(Copy.deep(cons.getSymbol()));
            hosPat.add(newCons);
            hosExp.add(newCons);

            final EntityFrame ef = new EntityFrame.EntityFrameSkeleton(this.getCurrentEntityFrame(), new EntityMap());

            // these are traversed in the correct order
            for (final Var field : consEnt.getSelectors()) {

                if (var2exp.get(field.getSymbol().getName(false)) != null) {
                    // we have an equation for this field
                    // thus the pattern is a joker and the expression is taken from the equation
                    hosPat.add(new JokerPat());
                    hosExp.add(Copy.deep(var2exp.get(field.getSymbol().getName(false))));
                } else {
                    // there is no equation for this field
                    // create a new variable and add it to the pattern and the expression
                    final String newName = this.prelude.buildUniqueName();
                    final VarEntity vent = new VarEntity(newName, curMod, null, null, true);
                    ef.addEntity(vent);
                    hosPat.add(new Var(new HaskellNamedSym(vent)));
                    hosExp.add(new Var(new HaskellNamedSym(vent)));
                }

            }
            final AltExp aexp =
                new AltExp((HaskellPat) HaskellTools.buildApplies(hosPat),
                    (HaskellExp) HaskellTools.buildApplies(hosExp), ef);
            altExps.add(aexp);
        }

        final CaseExp cexp = new CaseExp(ho.getExpression(), altExps);
        return cexp;
    }
}
