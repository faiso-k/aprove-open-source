package aprove.verification.idpframework.Core.PredefinedFunctions.Domains;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public interface Domain extends Immutable, IDPExportable, XmlExportable {


    public String getSuffix();

    public boolean isUserDefinedDomain();

    public boolean isBooleanDomain();

    public boolean isIntegerDomain();

    public boolean isSemiRingDomain();

    /**
     * @param dom The other domain.
     * @return True iff other domain is specialization.
     */
    public boolean isSpecialization(Domain dom);

    /**
     * @param otherDom The other domain.
     * @return Least common domain.
     */
    public Domain getGeneralization(Domain otherDom);

}