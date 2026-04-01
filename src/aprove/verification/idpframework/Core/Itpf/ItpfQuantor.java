package aprove.verification.idpframework.Core.Itpf;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class ItpfQuantor implements Exportable, IDPExportable, Immutable, XmlExportable {

    static final ItpfQuantor create(final boolean allQuantor,
        final IVariable<?> variable,
        final ItpfFactory factory) {
        return new ItpfQuantor(allQuantor, variable);
    }

    private final IVariable<?> variable;
    private final boolean universalQuantor;

    ItpfQuantor(final boolean universalQuantor, final IVariable<?> variable) {
        this.universalQuantor = universalQuantor;
        this.variable = variable;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (this.universalQuantor ? 1231 : 1237);
        result = prime * result + this.variable.hashCode();
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final ItpfQuantor other = (ItpfQuantor) obj;
        if (this.universalQuantor != other.universalQuantor) {
            return false;
        }
        if (!this.variable.equals(other.variable)) {
            return false;
        }
        return true;
    }

    @Override
    public final String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public final String export(final Export_Util o) {
        return this.export(o, IDPExportable.DEFAULT_LEVEL);
    }

    @Override
    public final String export(final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        final StringBuilder sb = new StringBuilder();
        this.export(sb, o, verbosityLevel);
        return sb.toString();
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o, final VerbosityLevel verbosityLevel) {
        if (this.universalQuantor) {
            sb.append(o.allQuantor());
        } else {
            sb.append(o.existQuantor());
        }
        sb.append(" ");
        sb.append(this.variable);
        if (!DomainFactory.UNKNOWN.equals(this.variable.getDomain())) {
            sb.append(":");
            sb.append(this.variable.getDomain());
        }
    }

    public IVariable<?> getVariable() {
        return this.variable;
    }

    public boolean isUniversalQuantor() {
        return this.universalQuantor;
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        return Collections.singletonMap("universalQuantor", Boolean.toString(this.universalQuantor));
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        final XmlContentsMap result = new XmlContentsMap();
        result.add(this.variable);

        return result ;
    }

}
