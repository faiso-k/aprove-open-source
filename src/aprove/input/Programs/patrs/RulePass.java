package aprove.input.Programs.patrs;

import java.util.*;

import aprove.input.Generated.patrs.node.*;
import aprove.input.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Treewalker which generates R.
 *
 * @author Stephan Falke
 * @version $Id$
 */

class RulePass extends Pass {

    private Stack<TRSTerm> terms = new Stack<TRSTerm>();
    private Set<PARule> rules = new LinkedHashSet<PARule>();
    private Map<String, List<String>> sorts;
    private Set<PAConstraint> cond = new LinkedHashSet<PAConstraint>();
    private TRSFunctionApplication l;
    private TRSTerm r;
    private Set<String> okfuns;

    public RulePass(Map<String, List<String>> sorts) {
        this.sorts = sorts;

        this.okfuns = new LinkedHashSet<String>();
        this.okfuns.add("0");
        this.okfuns.add("1");
        this.okfuns.add("-");
        this.okfuns.add("+");
    }

    @Override
    public void outASimpleRule(ASimpleRule node) {
        if (this.errors.getMaxLevel() >= ParseError.ERROR) {
            return;
        }
        PARule rule = PARule.create(this.l, this.r, ImmutableCreator.create(new LinkedHashSet<PAConstraint>(this.cond)));
        this.cond.clear();
        if (this.check_rule(rule, ((ASimple) node.getSimple()).getArrow())) {
            this.rules.add(rule);
        }
    }

    @Override
    public void outASimple(ASimple node) {
        this.r = this.terms.pop();
        this.l = (TRSFunctionApplication) this.terms.pop();
    }

    private boolean check_rule(PARule rule, Token t) {
        Map<String, String> varsorts = new LinkedHashMap<String, String>();

        this.get_sorts(rule.getLeft(), varsorts);
        this.get_sorts(rule.getRight(), varsorts);
        this.get_sorts(rule.getConstraint(), varsorts);

        if (this.check_vars(rule, t) && this.check_sorts(rule.getLeft(), varsorts, t) && this.check_sorts(rule.getConstraint(), varsorts, t) && this.check_sorts(rule.getRight(), varsorts, t)) {
            if (this.get_sort(rule.getLeft(), varsorts) != this.get_sort(rule.getRight(), varsorts)) {
                this.addParseError(t, ParseError.ERROR, "sorts of lhs and rhs disagree");
                return false;
            } else {
                return true;
            }
        } else {
            return false;
        }
    }

    private boolean check_vars(PARule rule, Token tok) {
        Set<TRSVariable> lvars = rule.getLeft().getVariables();
        if (!lvars.containsAll(rule.getRight().getVariables())) {
            this.addParseError(tok, ParseError.ERROR, "rule contains extra variables on right side");
            return false;
        }
        if (!lvars.containsAll(aprove.verification.dpframework.BasicStructures.CollectionUtils.getVariables(rule.getConstraint()))) {
            this.addParseError(tok, ParseError.ERROR, "rule contains extra variables in constraint");
            return false;
        }
        return true;
    }

    private boolean check_sorts(TRSTerm t, Map<String, String> varsorts, Token tok) {
        if (t instanceof TRSVariable) {
            String stt = this.get_sort(t, varsorts);
            if (stt == null) {
                this.addParseError(tok, ParseError.ERROR, "sort of variable '" + ((TRSVariable) t).getName() + "' cannot be determined");
                return false;
            }
            return true;
        }
        TRSFunctionApplication ft = (TRSFunctionApplication) t;
        String f = ft.getRootSymbol().getName();
        List<String> sorts = this.sorts.get(f);
        for (int i = 0; i < sorts.size() - 1; i++) {
            TRSTerm tt = ft.getArgument(i);
            if (tt instanceof TRSVariable) {
                String stt = this.get_sort(tt, varsorts);
                if (stt == null) {
                    this.addParseError(tok, ParseError.ERROR, "sort of variable '" + ((TRSVariable) tt).getName() + "' cannot be determined");
                    return false;
                } else if (stt != sorts.get(i)) {
                    this.addParseError(tok, ParseError.ERROR, "variable '" + ((TRSVariable) tt).getName() + "' is used with inconsistent sorts");
                    return false;
                }
            } else {
                if (this.get_sort(tt, varsorts) != sorts.get(i)) {
                    this.addParseError(tok, ParseError.ERROR, "function symbol '" + ((TRSFunctionApplication) tt).getRootSymbol().getName() + "' has the wrong sort");
                    return false;
                }
                if (!this.check_sorts(tt, varsorts, tok)) {
                    return false;
                }
            }
        }
        return true;
    }

    private boolean check_sorts(Set<PAConstraint> c, Map<String, String> varsorts, Token t) {
        for (PAConstraint cc : c) {
            Set<TRSVariable> v = cc.getVariables();
            for (TRSVariable vv : v) {
                if (varsorts.get(vv.getName()) != "int") {
                    this.addParseError(t, ParseError.ERROR, "variable '" + vv.getName() + "' is used with inconsistent sorts");
                    return false;
                }
            }
        }
        return true;
    }

    private void get_sorts(TRSTerm t, Map<String, String> varsorts) {
        if (t instanceof TRSVariable) {
            return;
        }
        TRSFunctionApplication ft = (TRSFunctionApplication) t;
        String f = ft.getRootSymbol().getName();
        List<String> sorts = this.sorts.get(f);
        for (int i = 0; i < sorts.size() - 1; i++) {
            TRSTerm tt = ft.getArgument(i);
            if (tt instanceof TRSVariable) {
                String stt = this.get_sort(tt, varsorts);
                if (stt == null) {
                    varsorts.put(((TRSVariable) tt).getName(), sorts.get(i));
                }
            } else {
                this.get_sorts(tt, varsorts);
            }
        }
    }

    private void get_sorts(Set<PAConstraint> c, Map<String, String> varsorts) {
        for (PAConstraint cc : c) {
            Set<TRSVariable> v = cc.getVariables();
            for (TRSVariable vv : v) {
                if (varsorts.get(vv.getName()) == null) {
                    varsorts.put(vv.getName(), "int");
                }
            }
        }
    }

    private String get_sort(TRSTerm t, Map<String, String> varsorts) {
        if (t instanceof TRSVariable) {
            return varsorts.get(((TRSVariable) t).getName());
        } else {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            String f = ft.getRootSymbol().getName();
            List<String> sorts = this.sorts.get(f);
            return sorts.get(sorts.size() - 1);
        }
    }

    @Override
    public void outAEqatomPaatom(AEqatomPaatom node) {
        TRSTerm t = this.terms.pop();
        TRSTerm s = this.terms.pop();
        PAConstraint c = PAConstraint.create(s, t, PAConstraint.EQ);
        if (this.check_cond(c, node.getEq())) {
            this.cond.add(c);
        }
    }

    @Override
    public void outAGtreqatomPaatom(AGtreqatomPaatom node) {
        TRSTerm t = this.terms.pop();
        TRSTerm s = this.terms.pop();
        PAConstraint c = PAConstraint.create(s, t, PAConstraint.GTREQ);
        if (this.check_cond(c, node.getGtreq())) {
            this.cond.add(c);
        }
    }

    @Override
    public void outAGtratomPaatom(AGtratomPaatom node) {
        TRSTerm t = this.terms.pop();
        TRSTerm s = this.terms.pop();
        PAConstraint c = PAConstraint.create(s, t, PAConstraint.GTR);
        if (this.check_cond(c, node.getGtr())) {
            this.cond.add(c);
        }
    }

    private boolean check_cond(PAConstraint c, Token t) {
        TRSTerm l = c.getLeft();
        TRSTerm r = c.getRight();

        Set<String> funs = this.getFunNames(l);
        funs.addAll(this.getFunNames(r));

        if (this.okfuns.containsAll(funs)) {
            return true;
        } else {
            if (!funs.removeAll(this.okfuns)) {
                throw new RuntimeException("internal error in RulePass.check_cond");
            }
            String bad = new Vector<String>(funs).get(0);
            this.addParseError(t, ParseError.ERROR, "constraint cannot contain '" + bad + "'");
            return false;
        }
    }

    private Set<String> getFunNames(TRSTerm t) {
        Set<String> res = new LinkedHashSet<String>();
        for (FunctionSymbol f : t.getFunctionSymbols()) {
            res.add(f.getName());
        }
        return res;
    }

    @Override
    public void inAFunctAppTerm(AFunctAppTerm node) {
        String name = this.chop(node.getId());
        if (!this.sorts.keySet().contains(name)) {
            Token t = null;
            if (node.getId() instanceof ARegularId) {
                t = ((ARegularId) node.getId()).getRegularid();
            } else {
                t = ((ASpecialId) node.getId()).getSpecialid();
            }
            this.addParseError(t, ParseError.ERROR, "id not declared");
            return;
        }
        int arity = this.sorts.get(name).size() - 1;
        FunctionSymbol f = FunctionSymbol.create(name, arity);
        ATermlist tl = (ATermlist)node.getTermlist();
        int size = (tl == null) ? 0 : (tl.getTermcomma().size() + 1);
        if (arity != size) {
            Token t = null;
            if (node.getId() instanceof ARegularId) {
                t = ((ARegularId) node.getId()).getRegularid();
            } else {
                t = ((ASpecialId) node.getId()).getSpecialid();
            }
            this.addParseError(t, ParseError.ERROR, "expected " + arity + " parameters, but found " + size);
            // BEGIN "ugly hack"
            TRSTerm u = TRSTerm.createVariable("undefined");
            for (int i = 0; i < arity - size; i++) {
                this.terms.add(u);
            }
            // END "ugly hack"
        }
    }

    @Override
    public void outAFunctAppTerm(AFunctAppTerm node) {
        String name = this.chop(node.getId());
        if (!this.sorts.keySet().contains(name)) {
            return;
        }
        int arity = this.sorts.get(name).size() - 1;
        FunctionSymbol f = FunctionSymbol.create(name, arity);
        TRSTerm[] t = new TRSTerm[arity];
        for (int i = 0; i < arity; i++) {
            t[arity - 1 - i] = this.terms.pop();
        }
        this.terms.add(TRSTerm.createFunctionApplication(f, t));
    }

    @Override
    public void inAConstVarTerm(AConstVarTerm node) {
        String name = this.chop(node.getId());
        if (!this.sorts.keySet().contains(name)) {
            this.terms.add(TRSTerm.createVariable(name));
        } else {
            int arity = this.sorts.get(name).size() - 1;
            FunctionSymbol f = FunctionSymbol.create(name, arity);
            if (arity != 0) {
                Token t = null;
                if (node.getId() instanceof ARegularId) {
                    t = ((ARegularId) node.getId()).getRegularid();
                } else {
                    t = ((ASpecialId) node.getId()).getSpecialid();
                }
                this.addParseError(
                    t,
                    ParseError.ERROR,
                    "missing parameter list for function or constructor '" + name + "'"
                );
            }
            this.terms.add(TRSTerm.createFunctionApplication(f, TRSTerm.EMPTY_ARGS));
        }
    }

    public Set<PARule> getR() {
        return this.rules;
    }

}
