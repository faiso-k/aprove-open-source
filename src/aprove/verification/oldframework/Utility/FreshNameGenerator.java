package aprove.verification.oldframework.Utility;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.NameGenerators.*;
/** Generator for fresh names. This is a broad generalization of FreshVarGenerator
 *  suitable for both dependency pair creation and variable renaming.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
@SuppressWarnings("serial")
public class FreshNameGenerator implements FreshNameChecker,
        java.io.Serializable{

    public static final NameGenerator ACL2 =
        new ACL2NameGenerator();

    public static final NameGenerator APPEND_NUMBERS =
        new AppendNameGenerator(0, 1);

    public static final NameGenerator DEPENDENCY_PAIRS =
        new UppercasingNameGenerator(new AppendNameGenerator(2, 1));

    public static final NameGenerator CiME_FRIENDLYNAMES =
        new FriendlyNamesNameGenerator(FriendlyNamesNameGenerator.Mode.CiME);

    public static final NameGenerator FRIENDLYNAMES =
        new FriendlyNamesNameGenerator(FriendlyNamesNameGenerator.Mode.FRIENDLY);

    public static final NameGenerator PROLOG_FUNCS =
        FreshNameGenerator.APPEND_NUMBERS;

    public static final NameGenerator PROLOG_VARS =
        FreshNameGenerator.APPEND_NUMBERS;

    public static final NameGenerator SEMLAB_VARS =
        new SemlabVarsNameGenerator();

    public static final NameGenerator TERMPTATION_FUNCS =
        new TermptationFuncsNameGenerator();

    public static final NameGenerator TERMPTATION_VARS =
        new TermptationVarsNameGenerator();

    public static final NameGenerator TTT_FRIENDLYNAMES =
        new FriendlyNamesNameGenerator(FriendlyNamesNameGenerator.Mode.TTT);

    public static final NameGenerator TTT_FUNCS =
        new TttNameGenerator();

    public static final NameGenerator TYPE_CONS =
        FreshNameGenerator.APPEND_NUMBERS;

    public static final NameGenerator TYPE_INFERENCE =
        FreshNameGenerator.APPEND_NUMBERS;

    public static final NameGenerator TYPE_INTERN =
        FreshNameGenerator.APPEND_NUMBERS;

    public static final NameGenerator TYPE_VARS =
        new TypeVarsNameGenerator();

    public static final NameGenerator VARIABLES =
        new AppendNameGenerator(2, 1);

    /** How should new names be selected?*/
    protected NameGenerator mode;
    /** The mapping from names to fresh names.*/
    protected Map<String, String> memory;
    /** The set of names that are already used.*/
    protected Set<String> used;
    /** The set of names that are initially used, that means when first generated.*/
    protected final Set<String> initiallyUsed;

    public Set<String> getUsedNames() {
        return this.used;
    }

    private String rename(final String oldName, final String newName, final boolean useMemory) {
        this.used.add(newName);
        if (useMemory) {
            this.memory.put(oldName, newName);
        }
        return newName;
    }

    @Override
    public boolean isUnused(final String name) {
        return !this.used.contains(name);
    }

    /** Get a new name for the given name.
     * @param old The old name.
     * @param useMemory True will cause subsequent calls to getFreshName with
     *        the same name to generate the same new names.
     * @return A new name.
     */
    public String getFreshName(final String old, final boolean useMemory) {
        if (useMemory) {
            final String memorized = this.memory.get(old);
            if (memorized != null) {
                return memorized;
            }
        }

        final String next = this.mode.getNewName(old, this);
        return this.rename(old, next, useMemory);
    }

    /**
     * Get a fresh name using a non-standard NameGenerator
     */
    public String getFreshName(final String old, final boolean useMemory, final NameGenerator ng) {
        if (useMemory) {
            final String memorized = this.memory.get(old);
            if (memorized != null) {
                return memorized;
            }
        }

        final String next = ng.getNewName(old, this);
        return this.rename(old, next, useMemory);
    }

    /** Default constructor.
     * @param used The set of names that are to be avoided.
     * @param mode The kind of new names to generate.
     */
    public FreshNameGenerator(final Collection<String> used, final NameGenerator mode) {
        this.memory = new HashMap<String,String>();
        this.used = new LinkedHashSet<String>(used);
        this.mode = mode;

        if(mode == FreshNameGenerator.SEMLAB_VARS) {
            this.initiallyUsed = new LinkedHashSet<String>(used);
        } else {
            this.initiallyUsed = new HashSet<String>(0);
        }
    }

    /** Default constructor.
     * @param mode The kind of new names to generate.
     */
    public FreshNameGenerator(final NameGenerator mode) {
        this(new LinkedHashSet<String>(), mode);
    }

    public FreshNameGenerator(final Iterable<? extends HasName> hasNames, final NameGenerator mode) {
        this(aprove.verification.dpframework.BasicStructures.CollectionUtils.getNames(hasNames), mode);
    }
    public FreshNameGenerator shallowcopy() {
    final FreshNameGenerator res = new FreshNameGenerator(this.used, this.mode);
    res.memory = new HashMap<String,String>(this.memory);
    return res;
    }

    /** Free this name. I.e., this name can be used later on.
     */
    public void freeName(final String name) {
        this.memory.remove(name);
        this.used.remove(name);
    }

    /**
     * Lock this name, i.e., mark it as already used
     * @param name
     * @return true iff name was not already locked / used
     */
    public boolean lockName(final String name) {
        return this.used.add(name);
    }

    /**
     * Lock these names, i.e., mark them as already used
     * @param name
     * @return true iff at least one name was not already locked / used
     */
    public boolean lockNames(final Collection<String> names) {
        return this.used.addAll(names);
    }

    /**
     * Lock these names, i.e., mark them as already used
     * @param name
     * @return true iff at least one name was not already locked / used
     */
    public void lockHasNames(final Collection<? extends HasName> hasNames) {
        for (final HasName hasName : hasNames) {
            this.used.add(hasName.getName());
        }
    }

    /** Only to be used in SEMLAB_VARS mode!
     */
    public void setUsedToOrigin() {
        if(Globals.useAssertions) {
            assert(this.mode == FreshNameGenerator.SEMLAB_VARS);
        }
        this.used = new LinkedHashSet<String>(this.initiallyUsed);
    }


}
