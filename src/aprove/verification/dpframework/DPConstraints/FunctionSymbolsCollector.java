package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.DPConstraints.idp.*;
import aprove.verification.oldframework.BasicStructures.*;

public class FunctionSymbolsCollector extends DPConstraintVisitor {
    Set<FunctionSymbol> fs;

    public FunctionSymbolsCollector(Set<FunctionSymbol> fs) {
        super();
        this.fs = fs;
    }

    @Override
    public void fcaseTermAtom(TermAtom atom) {
        atom.getLeft().collectFunctionSymbols(this.fs);
        atom.getRight().collectFunctionSymbols(this.fs);
    }

    @Override
    public void fcaseUsableAtom(UsableAtom atom) {
        atom.getT().collectFunctionSymbols(this.fs);
    }

}
