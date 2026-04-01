package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

public class Implication extends Constraint.ConstraintSkeleton implements HasTRSTerms, HasVariables {
    public Object id;
    public final Object data;
    public ImmutableSet<TRSVariable> quantor;
    public ConstraintSet conditions;
    public Constraint conclusion;

    public final ImmutableSet<TRSVariable> allVars;
    private final Set<GPolyVar> allPolyVars;

    @SuppressWarnings("unchecked")
    protected Implication(
        Object id,
        Object data,
        Set<TRSVariable> dquantor,
        ConstraintSet conditions,
        Constraint conclusion,
        boolean dq
    ) {
        super();
        this.id = id;
        this.data = data;
        this.conditions = conditions;
        this.conclusion = conclusion;
        Set<TRSVariable> nAllVars = new LinkedHashSet<TRSVariable>();
        nAllVars.addAll((Set<TRSVariable>)conclusion.getVariables());
        nAllVars.addAll(this.conditions.getVariables());
        this.allVars = ImmutableCreator.create(nAllVars);
        Set<GPolyVar> nAllPolyVars = new LinkedHashSet<GPolyVar>(this.conditions.getPolyVariables());
        nAllPolyVars.addAll(conclusion.getPolyVariables());
        this.allPolyVars = ImmutableCreator.create(nAllPolyVars);
        Set<TRSVariable> nQuantor;
        if (dq) {
            nQuantor = dquantor;
        } else {
            nQuantor = new LinkedHashSet<TRSVariable>(dquantor);
            nQuantor.retainAll(nAllVars);
        }
        this.quantor = ImmutableCreator.create(nQuantor);
    }

    @Override
    public boolean isImplication() {
        return true;
    }

    @Override
    public Set<TRSVariable> getVariables() {
        return this.allVars;
    }

    @Override
    public Set<GPolyVar> getPolyVariables() {
        return this.allPolyVars;
    }

    public static
        Implication
        create(Set<TRSVariable> quantor, ConstraintSet conditions, Constraint conclusion, Object data)
    {
        return new Implication(null, data, quantor, conditions, conclusion, false);
    }

    public static Implication create(
        Object id,
        Set<TRSVariable> quantor,
        ConstraintSet conditions,
        Constraint conclusion,
        Object data)
    {
        return new Implication(id, data, quantor, conditions, conclusion, false);
    }

    public TRSVisitable applySubstitution(
        TRSSubstitution subs,
        boolean ignoreTopQuantor,
        boolean quantorChange,
        boolean idpMode)
    {
        if (!ignoreTopQuantor) {
            Set<TRSVariable> dom = new LinkedHashSet<TRSVariable>(subs.getDomain());
            dom.retainAll(this.quantor);
            assert (dom.isEmpty());
        }
        ImmutableSet<TRSVariable> nQuantor;
        if (quantorChange) {
            nQuantor = this.applySubsitutionToQuantor(subs);
        } else {
            nQuantor = this.quantor;

        }
        return new Implication(this.id, this.data, nQuantor, (ConstraintSet) this.conditions.applySubstitution(
            subs,
            idpMode), (Constraint) this.conclusion.applySubstitution(subs, idpMode), true);
    }

    public ImmutableSet<TRSVariable> applySubsitutionToQuantor(TRSSubstitution subs) {
        Set<TRSVariable> nQuantor = new LinkedHashSet<TRSVariable>(this.quantor);
        nQuantor.removeAll(subs.getDomain());
        nQuantor.addAll(subs.getVariablesInCodomain());
        return ImmutableCreator.create(nQuantor);
    }

    @Override
    public TRSVisitable visit(DPConstraintVisitor dpcv) {
        dpcv.fcaseImplication(this);
        Implication imp = this;
        boolean change = false;
        Set<TRSVariable> nQuantor = this.quantor;
        if (dpcv.guardQuantor(this)) {
            nQuantor = dpcv.caseQuantor(this.quantor);
            change = change || nQuantor != this.quantor;
        }
        ConstraintSet inConditions = this.conditions;
        if (dpcv.guardConditions(this)) {
            inConditions = dpcv.applyTo(this.conditions);
            change = change || (inConditions != this.conditions);
        }
        Constraint nConclusion = this.conclusion;
        if (dpcv.guardConclusion(this)) {
            nConclusion = dpcv.applyTo(this.conclusion);
            change = change || (nConclusion != this.conclusion);
        }
        if (change) {
            imp = Implication.create(this.id, nQuantor, inConditions, nConclusion, this.data);
        }
        return dpcv.caseImplication(imp);
    }

    /**
    public boolean collectUnifyProblemForImplication(Vector<Variable> yes,Vector<Variable> no,List<ConstraintUnifyProblem> cups, Constraint con, boolean multiSet) {
        if (!con.isImplication()) {
            cups.clear();
            return false;
        }
        Implication implication = (Implication) con;
        yes.addAll(this.getQuantor());
        ConstraintUnifyProblem.increaseDomain(cups,this.getQuantor());
        return implication.getConditions().collectUnifyProblemForImplication(yes , no, cups, this.getConditions(), false)
        && this.getConclusion().collectUnifyProblemForImplication(yes, no, cups, implication.getConclusion(), false);
    }

    public boolean collectUnifyProblemForEquivalenz(List<ConstraintUnifyProblem> cups, Constraint con) {
        if (!con.isImplication()) {
            cups.clear();
            return false;
        }
        Implication implication = (Implication) con;
        return this.getQuantor().isEmpty() && implication.getQuantor().isEmpty() && implication.getConditions().collectUnifyProblemForEquivalenz(cups, this.getConditions())
        && this.getConclusion().collectUnifyProblemForEquivalenz(cups, implication.getConclusion());
    }
    **/

    public ImmutableSet<TRSVariable> getAllVars() {
        return this.allVars;
    }

    public Constraint getConclusion() {
        return this.conclusion;
    }

    public ConstraintSet getConditions() {
        return this.conditions;
    }

    public ImmutableSet<TRSVariable> getQuantor() {
        return this.quantor;
    }

    @Override
    public String toString() {
        return "("
            + this.quantor.toString()
            + "."
            + this.getConditions().toString()
            + "\n  =>"
            + this.getConclusion().toString()
            + ")";
    }

    public Object getId() {
        return this.id;
    }

    @Override
    public String export(Export_Util o) {
        String qstr = "";
        String condstr = "";
        if (!this.quantor.isEmpty()) {
            String first = "";
            String varstr = "";
            for (TRSVariable v : this.quantor) {
                varstr = varstr + first + v.export(o);
                first = ",";
            }
            qstr = o.allQuantor() + varstr + ":";
        }
        if (!this.getConditions().isEmpty()) {
            condstr = this.getConditions().export(o) + " " + o.implication() + " ";
        }
        return "(" + qstr + condstr + this.getConclusion().export(o) + ")";
    }

    @Override
    public boolean collectMatchMap(Constraint constraint, Map<TRSVariable, TRSTerm> map) {
        return false;
    }

    public Object getData() {
        return this.data;
    }
}
