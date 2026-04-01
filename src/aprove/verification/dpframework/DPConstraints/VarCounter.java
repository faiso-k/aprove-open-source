package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.idp.*;

public class VarCounter extends DPConstraintVisitor {
    Map<TRSVariable, Integer> map;

    public VarCounter(Map<TRSVariable, Integer> map) {
        super();
        this.map = map;
    }

    @Override
    public void fcaseTermAtom(TermAtom atom) {
        atom.getLeft().computeVariableCount(this.map);
        atom.getRight().computeVariableCount(this.map);
    }

    @Override
    public void fcaseUsableAtom(UsableAtom atom) {
        atom.getT().computeVariableCount(this.map);
    }

}
