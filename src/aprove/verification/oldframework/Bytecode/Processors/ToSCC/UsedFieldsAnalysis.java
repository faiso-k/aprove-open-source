package aprove.verification.oldframework.Bytecode.Processors.ToSCC;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.OpCodes.FieldAccess.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Analysis of used instance fields in a given SCC.
 *
 * @author Marc Brockschmidt
 */
public class UsedFieldsAnalysis extends SCCAnalysis {
    /**
     * This maps holds, per classname, a list of instance fields read (!)
     * somewhere in the annotated SCC.
     */
    private final CollectionMap<ClassName, String> readInstanceFields;

    /**
     * This maps holds, per classname, a counter of the number of read instance
     * fields of a non-primitive type.
     */
    private final Map<ClassName, Integer> readInstanceReferenceFields;

    /**
     * This maps holds, per classname, a list of static fields read (!)
     * somewhere in the annotated SCC.
     */
    private final CollectionMap<ClassName, String> readStaticFields;

    /**
     * @param scc the SCC to be annotated
     */
    public UsedFieldsAnalysis(final JBCGraph scc) {
        /*
         * We use a linked hash set as collection because we really, really want
         * a stable order on the field entries:
         */
        this.readInstanceFields = new CollectionMap<>();
        this.readStaticFields = new CollectionMap<>();
        this.readInstanceReferenceFields = new DefaultValueMap<>(0);

        //Now check all edges of the SCC for read accesses:
        for (final Node n : scc.getNodes()) {
            for (final Edge e : n.getOutEdges()) {
                for (final VariableInformation i : e.getLabel()) {
                    if (i instanceof InstanceAccessInformation) {
                        final InstanceAccessInformation ia = (InstanceAccessInformation) i;
                        if (ia.getAccessType().equals(FieldAccessRW.READ)) {
                            if (this.readInstanceFields.add(ia.getClassName(), ia.getFieldName())) {
                                if (ia.getReadOrWrittenRef().pointsToReferenceType()) {
                                    this.readInstanceReferenceFields.put(ia.getClassName(),
                                        this.readInstanceReferenceFields.get(ia.getClassName()) + 1);
                                }
                            }
                        }
                    } else if (i instanceof StaticFieldAccessInformation) {
                        final StaticFieldAccessInformation sfa = (StaticFieldAccessInformation) i;
                        if (sfa.getAccessType().equals(FieldAccessRW.READ)) {
                            this.readStaticFields.add(sfa.getClassName(), sfa.getFieldName());
                        }
                    }
                }
            }
        }
    }

    /**
     * @param cName Some classname.
     * @return A collection of field names of <code>cName</code> read in this
     *  SCC.
     */
    public Collection<String> getUsedFieldNames(final ClassName cName) {
        return this.readInstanceFields.getNotNull(cName);
    }

    /**
     * @param cName Some classname.
     * @return A collection of static field names of <code>cName</code> read in
     *  this SCC.
     */
    public Collection<String> getUsedStaticFieldNames(final ClassName cName) {
        return this.readStaticFields.getNotNull(cName);
    }

    /**
     * @param cName Some classname.
     * @return the number of fields of <code>cName</code> with reference values
     *  read in this SCC.
     */
    public Integer getNumberOfUsedReferenceFields(final ClassName cName) {
        return this.readInstanceReferenceFields.get(cName);
    }

    /**
     * @param o export util
     * @return textual representation of the analysis
     */
    @Override
    public String export(final Export_Util o) {
        final StringBuilder sb = new StringBuilder();

        sb.append("Used field analysis yielded the following read fields:").append(o.linebreak());
        final List<String> classWiseInfo = new LinkedList<>();
        for (final Entry<ClassName, Collection<String>> e : this.readInstanceFields.entrySet()) {
            final String classInfo = e.getKey().toString() + ": " + e.getValue();
            classWiseInfo.add(classInfo);
        }
        sb.append(o.set(classWiseInfo, Export_Util.ITEMIZE));

        return sb.toString();
    }
}
