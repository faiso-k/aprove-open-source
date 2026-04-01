package aprove.verification.dpframework.BasicStructures.Unification;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * @author Matthias Sondermann
 * @version $Id$
 */
public class SemiUnificationDag extends TermPairDag<SemiUnificationNode> {

    public SemiUnificationDag(TRSTerm term1, TRSTerm term2) {
        super(term1, term2, SharingMode.VARIABLE);
    }

    @Override
    protected SemiUnificationNode createNewNode(TRSTerm term) {
        return new SemiUnificationNode(term);
    }
}
