package aprove.verification.idpframework.Core.Itpf;

import java.util.*;

import aprove.verification.idpframework.Core.Utility.Marking.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class ItpfAndWrapper implements Immutable {

    private final ImmutableCollection<? extends QuantifiedDisjunction<ItpfConjClause>> formulas;
    private final ItpfFactory factory;

    private volatile Itpf formula;
    private volatile ImmutableList<ItpfQuantor> quantors;

    public ItpfAndWrapper(final Itpf formaula, final ItpfFactory factory) {
        this.formulas = ImmutableCreator.create(Collections.singleton(formaula));
        this.factory = factory;
        this.formula = formaula;
        this.quantors = formaula.getQuantification();
    }

    public ItpfAndWrapper(final ImmutableCollection<? extends QuantifiedDisjunction<ItpfConjClause>> formulas, final ItpfFactory factory) {
        this.formulas = formulas;
        this.factory = factory;
    }

    public ItpfAndWrapper addFormulas(final ImmutableCollection<? extends Itpf> formulas) {
        final LinkedHashSet<QuantifiedDisjunction<ItpfConjClause>> totalFormulas = new LinkedHashSet<QuantifiedDisjunction<ItpfConjClause>>(this.formulas);
        totalFormulas.addAll(formulas);
        return new ItpfAndWrapper(ImmutableCreator.create(totalFormulas), this.factory);
    }

    public ItpfAndWrapper addFormula(final QuantifiedDisjunction<ItpfConjClause> formula) {
        final LinkedHashSet<QuantifiedDisjunction<ItpfConjClause>> totalFormulas = new LinkedHashSet<QuantifiedDisjunction<ItpfConjClause>>(this.formulas);
        totalFormulas.add(formula);
        return new ItpfAndWrapper(ImmutableCreator.create(totalFormulas), this.factory);
    }

    public Itpf getFormula() {
        if (this.formula == null) {
            synchronized(this) {
                if (this.formula == null) {
                    return this.formula = this.factory.createAnd(this.formulas);
                }
            }
        }

        return this.formula;
    }

    public ImmutableCollection<? extends QuantifiedDisjunction<ItpfConjClause>> getSingleFormulas() {
        return this.formulas;
    }

    public ImmutableList<ItpfQuantor> getTotalQuantification() {
        if (this.quantors == null) {
            synchronized(this) {
                if (this.quantors == null) {
                    if (this.formula == null) {
                        ImmutableList<ItpfQuantor> nonEmptyQunators = null;
                        for (final QuantifiedDisjunction<ItpfConjClause> f : this.formulas) {
                            if (!f.getQuantification().isEmpty()) {
                                if (nonEmptyQunators != null) {
                                    return this.quantors = this.getFormula().getQuantification();
                                } else {
                                    nonEmptyQunators = f.getQuantification();
                                }
                            }
                        }
                        if (nonEmptyQunators == null) {
                            return this.quantors = ImmutableCreator.create(Collections.<ItpfQuantor>emptyList());
                        } else {
                            return this.quantors = nonEmptyQunators;
                        }
                    } else {
                        return this.quantors = this.formula.getQuantification();
                    }
                }
            }
        }

        return this.quantors;
    }
}
