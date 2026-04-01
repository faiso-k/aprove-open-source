package aprove.prooftree.Export.ProofPurposeDescriptors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.prooftree.Proofs.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Created on 19.07.2005 by marmer
 * @author marmer, cryingshadow
 * @version $Id$
 */
public abstract class ProofPurposeDescriptor implements VerbosityExportable {

    /**
     * @param stat The truth value.
     * @param purpose The analysis purpose.
     * @param object The analysis object.
     * @param o The export utility.
     * @return A default export message for a ProofPurposeDescriptor.
     */
    public static String export(TruthValue stat, String purpose, String object, Export_Util o) {
        final StringBuilder sb = new StringBuilder();
        sb.append(o.bold(purpose));
        sb.append(" of ");
        sb.append(object);
        sb.append(" could ");
        if (stat instanceof YNM) {
            final YNM status = (YNM)stat;
            final Color color = status.toColor();
            switch (status) {
                case YES:
                    sb.append("successfully be ");
                    sb.append(o.fontcolor("proven", color));
                    break;
                case NO:
                    sb.append("successfully be ");
                    sb.append(o.fontcolor("disproven", color));
                    break;
                default:
                    sb.append("not be shown");
                    break;
            }
        } else {
            final ComplexityYNM status = (ComplexityYNM)stat;
            final Color color = status.toColor();
            sb.append(" be shown to be ");
            sb.append(o.fontcolor(o.escape(stat.toString()), color));
        }
        sb.append(o.escape(":"));
        sb.append(o.linebreak());
        sb.append(o.linebreak());
        return sb.toString();
    }

    private TruthValue status;

    public ProofPurposeDescriptor() {

    }

    public Proof deepcopy() {
        return null;
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {
        return this.export(o);
    }

    public abstract String getPurpose();

    public TruthValue getStatus() {
        return this.status;
    }

    public void setStatus(TruthValue status) {
        this.status = status;
    }

}
