package aprove.input.Programs.prolog.structure;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * PrologSubstitution.<br><br>
 *
 * Created: Sep 16, 2008<br>
 * Last modified: Sep 16, 2008
 *
 * @author cryingshadow
 * @version $Id$
 */
public class PrologSubstitution extends LinkedHashMap<PrologVariable, PrologTerm> implements PrettyStringable {

    /**
     * Generated automatically.
     */
    private static final long serialVersionUID = -1744604545672075384L;

    /**
     * Standard constructor for empty substitution.
     */
    public PrologSubstitution() {
        super();
    }

    /**
     * Standard constructor from the specified map.
     * @param map The map representing the substitution.
     */
    public PrologSubstitution(final Map<? extends PrologVariable, ? extends PrologTerm> map) {
        super(map);
    }

    /**
     * Returns \sigma1\sigma2 if \sigma1\sigma2 = \sigma2\sigma1 and
     * \sigma1\sigma2 is a variable renaming and \sigma1\sigma2|_N =
     * \sigma1\sigma2. Returns null otherwise.
     * @param sigma1 The first substitution to check.
     * @param sigma2 The second substitution to check.
     * @return The combined substitution if this is a nonabstract
     *         variable renaming and null otherwise.
     */
    public static PrologSubstitution isNonAbstractRenaming(
        final PrologSubstitution sigma1,
        final PrologSubstitution sigma2)
    {
        if (sigma1 != null && sigma2 != null) {
            final PrologSubstitution res = new PrologSubstitution();
            for (final Map.Entry<PrologVariable, PrologTerm> entry : sigma1.entrySet()) {
                if (entry.getKey().isAbstractVariable() || !entry.getValue().isNonAbstractVariable()) {
                    return null;
                } else if (sigma2.containsKey(entry.getKey())) {
                    if (!entry.getValue().equals(sigma2.get(entry.getKey()))) {
                        return null;
                    }
                }
                res.put(entry.getKey(), entry.getValue());
            }
            for (final Map.Entry<PrologVariable, PrologTerm> entry : sigma2.entrySet()) {
                if (entry.getKey().isAbstractVariable() || !entry.getValue().isNonAbstractVariable()) {
                    return null;
                } else if (sigma1.containsKey(entry.getKey())) {
                    if (!entry.getValue().equals(sigma1.get(entry.getKey()))) {
                        return null;
                    }
                }
                res.put(entry.getKey(), entry.getValue());
            }
            return res;
        } else {
            return null;
        }
    }

    /**
     * Combines two matchers if they are consistent variable renamings.
     * @param sigma1 Matcher 1.
     * @param sigma2 Matcher 2.
     * @return The variable renaming specified by the two matchers or null if they do not specify a consistent variable
     *         renaming.
     */
    public static
        PrologSubstitution
        isVariableRenaming(final PrologSubstitution sigma1, final PrologSubstitution sigma2)
    {
        if (sigma1 != null && sigma2 != null) {
            final PrologSubstitution res = new PrologSubstitution();
            if (PrologSubstitution.checkEntries(sigma1, sigma2, res)
                && PrologSubstitution.checkEntries(sigma2, sigma1, res))
            {
                return res;
            }
        }
        return null;
    }

    /**
     * Helper method to combine two matchers which should be variable renamings and to check consistency of them.
     * @param sigma1 Matcher 1.
     * @param sigma2 Matcher 2.
     * @param res The combination of the two matchers.
     * @return True if the matchers were consistent variable renamings.
     */
    private static boolean checkEntries(
        final PrologSubstitution sigma1,
        final PrologSubstitution sigma2,
        final PrologSubstitution res)
    {
        for (final Map.Entry<PrologVariable, PrologTerm> entry : sigma1.entrySet()) {
            final PrologVariable key = entry.getKey();
            final PrologTerm value = entry.getValue();
            if (key.isAbstractVariable() || !value.isNonAbstractVariable()) {
                if (key.isNonAbstractVariable() || !value.isAbstractVariable()) {
                    return false;
                } else if (sigma2.containsKey(key)) {
                    if (!value.equals(sigma2.get(key))) {
                        return false;
                    }
                }
            } else if (sigma2.containsKey(key)) {
                if (!value.equals(sigma2.get(key))) {
                    return false;
                }
            }
            res.put(entry.getKey(), entry.getValue());
        }
        return true;
    }

    /**
     * Appends a substitution to the current one (composition).
     * @param substitution The substitution to append.
     * @return A deep copy of the current subsitution where the specified substitution is appended.
     */
    public PrologSubstitution append(final PrologSubstitution substitution) {
        final PrologSubstitution res = this.deepCopy();
        for (final Map.Entry<PrologVariable, PrologTerm> entry : res.entrySet()) {
            entry.setValue(entry.getValue().applySubstitution(substitution));
        }
        for (final Map.Entry<PrologVariable, PrologTerm> entry : substitution.entrySet()) {
            if (!res.containsKey(entry.getKey())) {
                res.put(entry.getKey(), entry.getValue());
            }
        }
        return res;
    }

    /**
     * Creates a deep copy.
     * @return A deep copy.
     */
    public PrologSubstitution deepCopy() {
        final PrologSubstitution res = new PrologSubstitution();
        for (final Map.Entry<PrologVariable, PrologTerm> entry : this.entrySet()) {
            res.put(entry.getKey(), entry.getValue());
        }
        return res;
    }

    /**
     * Returns a set of abstract variables in the range of this substitution.
     * @return A set of abstract variables in the range of this substitution.
     */
    public Set<PrologAbstractVariable> getAbstractVarsInRange() {
        final Set<PrologAbstractVariable> res = new LinkedHashSet<PrologAbstractVariable>();
        for (final PrologTerm t : this.values()) {
            res.addAll(t.createSetOfAllAbstractVariables());
        }
        return res;
    }

    /**
     * Returns a set of non-abstract variables in the range of this substitution.
     * @return A set of non-abstract variables in the range of this substitution.
     */
    public Set<PrologNonAbstractVariable> getNonAbstractVarsInRange() {
        final Set<PrologNonAbstractVariable> res = new LinkedHashSet<PrologNonAbstractVariable>();
        for (final PrologTerm t : this.values()) {
            res.addAll(t.createSetOfAllNonAbstractVariables());
        }
        return res;
    }

    /**
     * Returns a set of all variables in the range of this substitution.
     * @return A set of all variables in the range of this substitution.
     */
    public Set<PrologVariable> getVarsInRange() {
        final Set<PrologVariable> res = new LinkedHashSet<PrologVariable>();
        for (final PrologTerm t : this.values()) {
            res.addAll(t.createSetOfAllVariables());
        }
        return res;
    }

    @Override
    public String prettyToString() {
        final StringBuilder res = new StringBuilder();
        boolean first = true;
        for (final Map.Entry<PrologVariable, PrologTerm> entry : this.entrySet()) {
            if (first) {
                first = false;
            } else {
                res.append(",\\n");
            }
            res.append(entry.getKey().prettyToString());
            res.append(" -> ");
            res.append(entry.getValue().prettyToString());
        }
        return res.toString();
    }

    /**
     * Returns the restricted substitution w.r.t. the specified set of variables.
     * @param set The set to which the substitution is to be restricted.
     * @return A new restricted substitution w.r.t. the specified set of variables.
     */
    public PrologSubstitution restrict(final Set<? extends PrologVariable> set) {
        final PrologSubstitution res = new PrologSubstitution();
        for (final Map.Entry<PrologVariable, PrologTerm> entry : this.entrySet()) {
            if (set.contains(entry.getKey())) {
                res.put(entry.getKey(), entry.getValue());
            }
        }
        return res;
    }

    /**
     * Works like restrict, but for the complement of the specified set of variables.
     * @param set The set to whose complement the substitution is to be restricted.
     * @return A new restricted substitution w.r.t. the complement of the specified set of variables.
     */
    public PrologSubstitution restrictExclusion(final Set<? extends PrologVariable> set) {
        final PrologSubstitution res = new PrologSubstitution();
        for (final Map.Entry<PrologVariable, PrologTerm> entry : this.entrySet()) {
            if (!set.contains(entry.getKey())) {
                res.put(entry.getKey(), entry.getValue());
            }
        }
        return res;
    }

    /**
     * Returns the restricted substitution w.r.t. abstract variables.
     * @return A new restricted substitution w.r.t. abstract variables.
     */
    public PrologSubstitution restrictToAbstractVariables() {
        final PrologSubstitution res = new PrologSubstitution();
        for (final Map.Entry<PrologVariable, PrologTerm> entry : this.entrySet()) {
            if (entry.getKey().isAbstractVariable()) {
                res.put(entry.getKey(), entry.getValue());
            }
        }
        return res;
    }

    /**
     * Returns the restricted substitution w.r.t. non-abstract variables.
     * @return A new restricted substitution w.r.t. non-abstract variables.
     */
    public PrologSubstitution restrictToNonAbstractVariables() {
        final PrologSubstitution res = new PrologSubstitution();
        for (final Map.Entry<PrologVariable, PrologTerm> entry : this.entrySet()) {
            if (entry.getKey().isNonAbstractVariable()) {
                res.put(entry.getKey(), entry.getValue());
            }
        }
        return res;
    }

    /**
     * @param kb A knowledge base indicating ground variables which are overlined in the output.
     * @return A representation of this substitution suitable for LaTeX documents.
     */
    public String toLaTeX(final KnowledgeBase kb) {
        final StringBuilder res = new StringBuilder();
        res.append("\\{");
        boolean first = true;
        for (final Map.Entry<PrologVariable, PrologTerm> entry : this.entrySet()) {
            if (first) {
                first = false;
            } else {
                res.append(",");
            }
            res.append(entry.getKey().toLaTeX(kb));
            res.append("/");
            res.append(entry.getValue().toLaTeX(kb));
        }
        res.append("\\}");
        return res.toString();
    }

    /* (non-Javadoc)
     * @see java.util.AbstractMap#toString()
     */
    @Override
    public String toString() {
        final StringBuilder res = new StringBuilder();
        boolean first = true;
        for (final Map.Entry<PrologVariable, PrologTerm> entry : this.entrySet()) {
            if (first) {
                first = false;
            } else {
                res.append(",\n");
            }
            res.append(entry.getKey());
            res.append(" -> ");
            res.append(entry.getValue());
        }
        return res.toString();
    }

}
