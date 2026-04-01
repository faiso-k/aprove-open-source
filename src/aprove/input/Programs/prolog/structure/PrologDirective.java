package aprove.input.Programs.prolog.structure;

import java.util.*;

import aprove.input.Programs.prolog.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

/**
 * A PrologDirective modells a directive in Prolog and consists of a
 * PrologTerm called body, which should contain predicate calls for a
 * PrologProgram.<br><br>
 *
 * Created: Nov 29, 2006<br>
 * Last modified: Aug 19, 2015
 *
 * @author cryingshadow
 * @version $Id$
 */
public class PrologDirective implements Exportable, Immutable, JSONExport {

    /**
     * The body of the directive.
     */
    private final PrologTerm body;

    /**
     * Constructs a new PrologDirective with the specified PrologTerm as
     * body.
     * @param term The directive's body.
     */
    public PrologDirective(PrologTerm term) {
        if (term == null) {
            throw new NullPointerException("A directive must not be null!");
        }
        this.body = term;
    }

    /**
     * @return A set of all symbol names.
     */
    public Set<String> createSetOfAllSymbolNames() {
        NameWalker walker = new NameWalker();
        this.getBody().walk(walker);
        return walker.getResult();
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof PrologDirective) {
            return this.getBody().equals(((PrologDirective) o).getBody());
        }
        return false;
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder res = new StringBuilder();
        res.append(o.export(":-"));
        res.append(o.appSpace());
        Set<FunctionSymbol> preds = new LinkedHashSet<FunctionSymbol>();
        preds.add(this.body.createFunctionSymbol());
        res.append(this.body.export(o, preds));
        return res.toString();
    }

    /**
     * Export method considering the specified set of defined function symbols.
     * @param o The export utility object.
     * @param preds The defined function symbols.
     * @return The exported String.
     */
    public String export(Export_Util o, Set<FunctionSymbol> preds) {
        StringBuilder res = new StringBuilder();
        res.append(o.export(":-"));
        res.append(o.appSpace());
        res.append(this.body.export(o, preds));
        return res.toString();
    }

    /**
     * Returns the directive's body.
     * @return The directive's body.
     */
    public PrologTerm getBody() {
        return this.body;
    }

    @Override
    public int hashCode() {
        return 23 * this.getBody().hashCode();
    }

    @Override
    public Object toJSON() {
        return this.body.toJSON();
    }

    /**
     * Tries to transform this directive to a list of queries. This is
     * possible if this directive is no correct directive in Prolog, but
     * a moding information for predicates used in programs for
     * termination analysis for example. If this directive is a correct
     * directive in Prolog and no moding information, the returned list
     * of queries will be empty.
     * @return A list of queries constructed from moding information in
     *         this directive.
     */
    public List<PrologQuery> toQueries() {
        final List<PrologQuery> res = new ArrayList<PrologQuery>();
        if (this.getBody().isConjunction()) {
            this.getBody().walkConjunction(new TermWalker() {

                @Override
                public boolean goDeeper(PrologTerm term) {
                    return true;
                }

                @Override
                public boolean isApplicable(PrologTerm term) {
                    return true;
                }

                @Override
                public void performAction(PrologTerm term) {
                    PrologQuery q = Translator.toQuery(term, PrologPurpose.TERMINATION);
                    if (q != null) {
                        res.add(q);
                    }
                }

            });
        } else {
            PrologQuery q = Translator.toQuery(this.getBody(), PrologPurpose.TERMINATION);
            if (q != null) {
                res.add(q);
            }
        }
        return res;
    }

    @Override
    public String toString() {
        return ":- " + this.getBody().toString();
    }

}
