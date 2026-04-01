package aprove.verification.complexity.LowerBounds.BasicStructures;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.complexity.LowerBounds.Util.Renaming.*;
import aprove.verification.dpframework.BasicStructures.*;
import immutables.*;


abstract class Relation<S extends TRSTerm, T extends TRSTerm, R extends Relation<S, T, R>> implements Exportable {

    S lhs;
    T rhs;

    public Relation(S lhs, T rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
    }

    public S getLeft() {
        return this.lhs;
    }

    public T getRight() {
        return this.rhs;
    }

    @SuppressWarnings({ "unchecked", "unused" })
    public R applySubstitution(TRSSubstitution sigma, TrsTypes types) {
        return this.cloneWith((S)this.lhs.applySubstitution(sigma), (T)this.rhs.applySubstitution(sigma));
    }

    abstract R cloneWith(S newLhs, T newRhs);

    public Set<TRSVariable> getVariables() {
        Set<TRSVariable> res = new LinkedHashSet<>();
        res.addAll(this.lhs.getVariables());
        res.addAll(this.rhs.getVariables());
        return res;
    }

    @Override
    public String export(Export_Util eu) {
        String res = "";
        res += eu.export(this.lhs);
        res += eu.escape(" ") + this.getSymbol(eu) + eu.escape(" ");
        res += eu.export(this.rhs);
        return res;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    abstract String getSymbol(Export_Util eu);

    public TRSSubstitution getVarRenaming(RenamingCentral renamingCentral) {
        RenamingSession session = renamingCentral.getSession();
        Map<TRSVariable, TRSTerm> renaming = new LinkedHashMap<>();
        for (TRSVariable var : this.getVariables()) {
            renaming.put(var, session.renameVariable(var));
        }
        TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(renaming));
        return sigma;
    }

    public R renameVariables(RenamingCentral renamingCentral) {
        return this.renameVariables(renamingCentral, null);
    }

    public R renameVariables(RenamingCentral renamingCentral, TrsTypes types) {
        TRSSubstitution sigma = this.getVarRenaming(renamingCentral);
        return this.applySubstitution(sigma, types);
    }

    @SuppressWarnings("unchecked")
    public R normalizeVariables() {
        Map<TRSVariable, TRSVariable> renaming = new LinkedHashMap<>();
        ImmutablePair<? extends TRSTerm, Integer> p = this.getLeft().renumberVariables(renaming, "x", 0);
        S newLhs = (S) p.x;
        int count = p.y;
        p = this.getRight().renumberVariables(renaming, "x", count);
        T newRhs = (T) p.x;
        return this.cloneWith(newLhs, newRhs);
    }
}
