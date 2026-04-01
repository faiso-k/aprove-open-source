package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.idp.*;

public class TermCollector extends DPConstraintVisitor {
    Set<TRSTerm> terms;

    public TermCollector(Set<TRSTerm> terms) {
        super();
        this.terms = terms;
    }

    @Override
    public void fcaseTermAtom(TermAtom atom) {
        this.terms.add(atom.getLeft());
        this.terms.add(atom.getRight());
    }

    @Override
    public void fcaseUsableAtom(UsableAtom atom) {
        this.terms.add(atom.getT());
    }

}
