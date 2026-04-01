package aprove.verification.dpframework.Utility;

import java.util.*;

import aprove.verification.oldframework.Utility.*;

public class FreshNameEnsurer implements FreshNameChecker {

    protected final NameProvider keepProvider;
    protected final NameProvider avoidProvider;
    protected final Map<String,String> memorizedMapping;
    protected final Set<String> usedNames;
    protected final NameGenerator nameGen;

    private FreshNameEnsurer(NameProvider keep, NameProvider avoid, NameGenerator gen) {
        this.keepProvider = keep;
        this.avoidProvider = avoid;
        this.memorizedMapping = new HashMap<String,String>();
        this.usedNames = new HashSet<String>();
        this.nameGen = gen;
    }

    /**
     * @param keep
     *            This names may not be replaced. This can be used to keep names
     *            intact, which need an explicit conversion (see
     *            {@link NameConflictResolver} for an usage example)
     * @param avoid
     *            Names which must be replaced. If a name is also present in
     *            <code>keep</code>, its presence in <code>avoid</code> is
     *            ignored.
     * @param gen
     *            NameGenerator used to generate fresh names.
     */
    public static FreshNameEnsurer create(NameProvider keep, NameProvider avoid, NameGenerator gen) {
        return new FreshNameEnsurer(keep, avoid, gen);
    }

    public static FreshNameEnsurer create(NameProvider avoid, NameGenerator gen) {
        NameProvider keep = EmptyNameProvider.create();
        return new FreshNameEnsurer(keep, avoid, gen);
    }

    public static FreshNameEnsurer create(Collection<String> used, NameGenerator gen) {
        NameProvider keep = EmptyNameProvider.create();
        NameProvider avoid = CollectionNameProvider.create(used);
        return new FreshNameEnsurer(keep, avoid, gen);
    }

    public String getFreshName(String old) {
        String memorized = this.memorizedMapping.get(old);
        if (memorized != null) {
            return memorized;
        }

        if (this.keepProvider.contains(old)) {
            return old;
        }

        if (this.avoidProvider.contains(old)
                || this.usedNames.contains(old)) {
            String fresh = this.nameGen.getNewName(old, this);
            this.memorizedMapping.put(old, fresh);
            this.usedNames.add(fresh);
            return fresh;
        }

        this.memorizedMapping.put(old, old);
        this.usedNames.add(old);
        return old;
    }

    @Override
    public boolean isUnused(String name) {
        return !(this.keepProvider.contains(name)
                || this.avoidProvider.contains(name)
                || this.usedNames.contains(name));
    }

}
