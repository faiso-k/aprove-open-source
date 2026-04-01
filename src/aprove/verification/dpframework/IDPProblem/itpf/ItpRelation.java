/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.itpf;

import aprove.prooftree.Export.Utility.*;
import immutables.*;

public enum ItpRelation implements Immutable, Exportable {

    TO(false, true), TO_TRANS(true, true), TO_PLUS(false, true), EQ(true, false), ABSTRACT_GT(false, false), ABSTRACT_GE(true, false),
    TO_SYM_TRANS(true, true);   // we don't really need or support that, for future use

    private final boolean isReflexive;
    private final boolean isRewriteRel;

    ItpRelation(boolean reflexive, boolean isRewriteRel) {
        this.isReflexive = reflexive;
        this.isRewriteRel = isRewriteRel;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String export(Export_Util o) {
        switch(this) {
        case TO :
            return o.idpItpfTo();
        case TO_TRANS :
            return o.idpItpfToTrans();
        case TO_PLUS :
            return o.idpItpfToPlus();
        case EQ :
            return o.idpItpfEq();
        case ABSTRACT_GE :
            return o.idpCCGE();
        case ABSTRACT_GT :
            return o.idpCCGT();
        default:
            throw new UnsupportedOperationException();
        }
    }

    public boolean isReflexive() {
        return this.isReflexive;
    }

    public boolean isRewriteRel() {
        return this.isRewriteRel;
    }
}
