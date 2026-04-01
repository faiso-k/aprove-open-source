package aprove.verification.oldframework.Bytecode;

/**
 * Here we store which annotations to add for new static fields. When accessing a class with static fields we might also
 * consider the case that the class was initialized before the access. If so, the static fields can have (arbitrary?)
 * values. In this class we define which annotations we assume for these values.
 * @author cotto
 */
public class StaticFieldInitInfo {

    /**
     * Each static field may share with any other reference.
     */
    private boolean sharingBetweenAny;

    /**
     * Each static field may be cyclic.
     */
    private boolean cyclic;

    /**
     * Each static field may be non-tree.
     */
    private boolean nonTree;

    /**
     * Each static field may share with any other static field.
     */
    private boolean sharesWithSFs;

    /**
     * @return false only if we want to assume that the static field is acyclic
     */
    public boolean annotateAsCyclic() {
        return this.cyclic;
    }

    /**
     * @return false only if we want to assume that the static field is tree-shaped
     */
    public boolean annotateAsNonTree() {
        return this.nonTree;
    }

    /**
     * @return false only if we want to assume that the static field does not share with any other static field
     */
    public boolean sharesWithStaticFields() {
        return this.sharesWithSFs;
    }

    /**
     * @return false only if we want to assume that the static field does not share with any other reference
     */
    public boolean sharesWithEverything() {
        return this.sharingBetweenAny;
    }

    /**
     * Each static field may share with any other reference.
     */
    public void setSharingBetweenAny() {
        this.sharingBetweenAny = true;
    }

    /**
     * Each static field may be cyclic.
     */
    public void setCyclic() {
        this.cyclic = true;
        this.nonTree = true;
    }

    /**
     * Each static field may share with any other static field.
     */
    public void setSharingBetweenSFs() {
        this.sharesWithSFs = true;
    }

    /**
     * Each static field may be non-tree.
     */
    public void setNonTree() {
        this.nonTree = true;
    }
}
