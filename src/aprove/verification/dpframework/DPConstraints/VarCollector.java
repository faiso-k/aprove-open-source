package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.idp.*;

public class VarCollector extends DPConstraintVisitor {
    Set<TRSVariable> vars;

    public VarCollector(Set<TRSVariable> vars) {
        super();
        this.vars = vars;
    }

    @Override
    public void fcaseTermAtom(TermAtom atom) {
        atom.getLeft().collectVariables(this.vars);
        atom.getRight().collectVariables(this.vars);
    }

    @Override
    public void fcaseUsableAtom(UsableAtom atom) {
        atom.getT().collectVariables(this.vars);
    }

}
