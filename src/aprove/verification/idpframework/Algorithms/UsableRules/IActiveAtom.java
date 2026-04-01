package aprove.verification.idpframework.Algorithms.UsableRules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

/**
 *
 * @author MP
 */
public class IActiveAtom extends IDPExportable.IDPExportableSkeleton implements XmlExportable {

    public static IActiveAtom create(final IFunctionSymbol<?> fs, final int pos) {
        return new IActiveAtom(fs, pos);
    }

    public final IFunctionSymbol<?> fs;
    public final int pos;

    private final int hashCode;

    private IActiveAtom(final IFunctionSymbol<?> fs, final int pos) {
        this.fs = fs;
        this.pos = pos;
        int hashCode = 78921321 * fs.hashCode();
        hashCode += 891341273 * pos;
        this.hashCode = hashCode;
    }

    @Override
    public boolean equals(final Object other) {
        if (other instanceof IActiveAtom) {
            final IActiveAtom atom = (IActiveAtom) other;
            return this.hashCode == atom.hashCode && this.pos == atom.pos && this.fs.equals(atom.fs);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        sb.append(this.fs.export(eu, false));
        sb.append("/");
        sb.append(this.pos);
    }

    @Override
    public Map<String, String> getXmlAttribs(XmlExporter xe) {
        Map<String, String> m = new HashMap<String, String>();
        m.put("pos", Integer.toString(this.pos));
        return m;
    }

    @Override
    public XmlContentsMap getXmlContents(XmlExporter xe) {
        XmlContentsMap contents = new XmlContentsMap();
        contents.add(this.fs);
        return contents;
    }

}
