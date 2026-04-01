/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.processorHistory;

import aprove.verification.dpframework.IDPProblem.Processors.*;

public class IdpProcessorHistory {

    public static IdpProcessorHistory initialHistory(IDPProcessor proc) {
        if (proc != null) {
            return new IdpProcessorHistory(null, proc);
        } else {
            return null;
        }
    }

    public static IdpProcessorHistory newEntry(IdpProcessorHistory procHistory,
            IDPProcessor proc) {
        return new IdpProcessorHistory (procHistory, proc);
    }

    private final IdpProcessorHistory parent;
    private final IDPProcessor proc;

    public IdpProcessorHistory (IdpProcessorHistory parent, IDPProcessor proc) {
        this.parent = parent;
        this.proc = proc;
    }

    public IdpProcessorHistory getParent() {
        return this.parent;
    }

    public IDPProcessor getProc() {
        return this.proc;
    }

}
