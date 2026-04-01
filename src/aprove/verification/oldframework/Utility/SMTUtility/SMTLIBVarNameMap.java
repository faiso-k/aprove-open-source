package aprove.verification.oldframework.Utility.SMTUtility;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * Mapping between SMTLIB Variables and their YICES names.
 *
 * @author Andreas Kelle-Emden
 * @$Id$
 */
public class SMTLIBVarNameMap implements Map<SMTLIBAssignableSemantics, String> {

    private final Map<String, SMTLIBAssignableSemantics> nameToVarMap;
    private final Map<SMTLIBAssignableSemantics, String> varToNameMap;
    private final Set<String> stringSet;

    public SMTLIBVarNameMap() {
        this.nameToVarMap = new LinkedHashMap<String, SMTLIBAssignableSemantics>();
        this.varToNameMap = new LinkedHashMap<SMTLIBAssignableSemantics, String>();
        this.stringSet = new LinkedHashSet<String>();
    }

    public Map<String, SMTLIBAssignableSemantics> getNameToVarMap() {
        return this.nameToVarMap;
    }

    public Map<SMTLIBAssignableSemantics, String> getVarToNameMap() {
        return this.varToNameMap;
    }

    @Override
    public void clear() {
        this.nameToVarMap.clear();
        this.varToNameMap.clear();
    }

    @Override
    public boolean containsKey(final Object key) {
        return this.varToNameMap.containsKey(key);
    }

    @Override
    public boolean containsValue(final Object value) {
        return this.varToNameMap.containsValue(value);
    }

    @Override
    public Set<Map.Entry<SMTLIBAssignableSemantics, String>> entrySet() {
        return this.varToNameMap.entrySet();
    }

    @Override
    public String get(final Object key) {
        return this.varToNameMap.get(key);
    }

    public SMTLIBAssignableSemantics getVar(final Object key) {
        return this.nameToVarMap.get(key);
    }

    @Override
    public boolean isEmpty() {
        return this.varToNameMap.isEmpty();
    }

    @Override
    public Set<SMTLIBAssignableSemantics> keySet() {
        return this.varToNameMap.keySet();
    }

    @Override
    public String put(final SMTLIBAssignableSemantics key, final String value) {
        final String firstRes = this.varToNameMap.get(key);
        if (firstRes != null) {
            return firstRes;
        }
        boolean createNew = false;
        String varName = key.getName();
        varName = varName.replace("_", "__");

        final StringBuilder newName = new StringBuilder();

        for (int i = 0; i < varName.length(); i++) {
            final char c = varName.charAt(i);
            //Allow only [a-z0-9_A-Z]
            if ((97 <= c && c <= 122) || (48 <= c && c <= 57) || c == 95 || (65 <= c && c <= 90)) {
                newName.append(c);
            } else {
                newName.append('_').append(Integer.toString(c));
                createNew = true;
            }
        }
        if (varName.contains("@")) {
            varName = varName.replace("@", "_at");
            createNew = true;
        }
        if (varName.contains("[")) {
            varName = varName.replace("[", "_lrbracket");
            createNew = true;
        }

        if (varName.contains("]")) {
            varName = varName.replace("]", "_rrbracket");
            createNew = true;
        }


        if (createNew) {
            varName = newName.toString();
            boolean ok = false;
            while (!ok) {
                if (!this.stringSet.contains(varName)) {
                    ok = true;
                } else {
                    varName += "_";
                }
            }
        }

        this.nameToVarMap.put(varName, key);
        this.varToNameMap.put(key, varName);
        this.stringSet.add(varName);
        return varName;
    }

    @Override
    public void putAll(final Map m) {
        throw new UnsupportedOperationException("Not allowed on YICES name maps");
    }

    @Override
    public String remove(final Object key) {
        return this.varToNameMap.remove(key);
    }

    @Override
    public int size() {
        return this.varToNameMap.size();
    }

    @Override
    public Collection<String> values() {
        return this.varToNameMap.values();
    }

}
