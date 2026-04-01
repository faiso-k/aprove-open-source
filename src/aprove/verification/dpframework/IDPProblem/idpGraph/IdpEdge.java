/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.idpGraph;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.*;
import aprove.verification.dpframework.IDPProblem.Processors.processorHistory.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class IdpEdge implements Immutable, Exportable, IDPExportable {

    public static IdpEdge create(Node from, Node to, Itpf itpf, IDPProcessor proc) {
        return new IdpEdge(from, to, itpf, IdpProcessorHistory.initialHistory(proc));
    }

    private final Node from;
    private final Node to;
    private final Itpf itpf;
    private final IdpProcessorHistory procHistory;
    private Integer hash;

    private IdpEdge(Node from, Node to, Itpf itpf, IdpProcessorHistory procHistory) {
        this.from = from;
        this.to = to;
        this.itpf = itpf;
        this.procHistory = procHistory;
    }

    public Node getFrom() {
        return this.from;
    }

    public Node getTo() {
        return this.to;
    }

    public Itpf getItpf() {
        return this.itpf;
    }

    public IdpProcessorHistory getProcHistory() {
        return this.procHistory;
    }

    @Override
    public boolean equals (Object o) {
        if (o == this) {
            return true;
        } else if (o instanceof IdpEdge) {
            IdpEdge io = (IdpEdge) o;
            return io.from.equals(this.from) && io.to.equals(this.to) && io.itpf.equals(this.itpf);
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        if (this.hash == null) {
            synchronized(this) {
                if (this.hash == null) {
                    this.hash = Integer.valueOf(this.from.hashCode() + this.to.hashCode() + this.itpf.hashCode());
                }
            }
        }
        return this.hash;
    }

    public String exportShort(Export_Util o) {
        StringBuilder sb = new StringBuilder();
        sb.append(this.from.exportId(o));
        sb.append(" ");
        sb.append(o.rightarrow());
        sb.append(" ");
        sb.append(this.to.exportId(o));
        return sb.toString();
    }

    @Override
    public String export(Export_Util o) {
        return this.export(o, null, VerbosityLevel.MIDDLE);
    }

    @Override
    public String export(Export_Util o, IDPPredefinedMap predefinedMap, VerbosityLevel verbosityLevel) {
        StringBuilder sb = new StringBuilder();
        sb.append(this.from.export(o, predefinedMap, verbosityLevel));
        sb.append(o.rightarrow());
        sb.append(this.to.export(o, predefinedMap, verbosityLevel));
        sb.append(o.pipeSign());
        sb.append(this.itpf.export(o, predefinedMap, verbosityLevel));
        return sb.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public IdpEdge change(Node from, Node to, Itpf itpf, IDPProcessor proc) {
        return new IdpEdge(from != null ? from : this.from,
                        to != null ? to : this.to,
                        itpf != null ? itpf : this.itpf,
                        IdpProcessorHistory.newEntry(this.procHistory, proc));
    }



}
