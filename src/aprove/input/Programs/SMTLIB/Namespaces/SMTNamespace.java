package aprove.input.Programs.SMTLIB.Namespaces;

import java.util.*;

import aprove.*;
import aprove.input.Programs.SMTLIB.Exceptions.*;
import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.input.Programs.SMTLIB.Terms.*;

/**
 * Represents a namespace for declared and defined identifiers with its sort or
 * respectively the definition. Namespaces can have parent namespaces to
 * represent hierarchic structure of namespaces.
 */
public class SMTNamespace {

    private final Map<String, AbstractSort> declarations =
        new LinkedHashMap<String, AbstractSort>();
    private final Map<String, SMTTermWrapper> definitions =
        new LinkedHashMap<String, SMTTermWrapper>();
    private SMTNamespace parentNamespace;

    public SMTNamespace() {
    }

    public SMTNamespace(final SMTNamespace parent) {
        this.parentNamespace = parent;
    }

    public Set<String> getIdentifiers() {
        return this.getIdentifiers(false);
    }

    public Set<String> getIdentifiers(final boolean onlyTopLevel) {
        final Set<String> ret = new LinkedHashSet<String>(this.declarations.keySet());
        if (onlyTopLevel == false && this.parentNamespace != null) {
            ret.addAll(this.parentNamespace.getIdentifiers(onlyTopLevel));
        }
        return ret;
    }

    /**
     * Declare a new identifier in this namespace.
     * @param identifier The new identifier
     * @param sort The sort of the identifier
     * @throws MultipleOccurenceException
     */
    public void declare(final String identifier, final AbstractSort sort)
            throws MultipleOccurenceException {
        if (Globals.useAssertions) {
            assert identifier != null;
            assert !identifier.equals("");
            assert sort != null;
        }

        if (this.declarations.containsKey(identifier)) {
            throw new MultipleOccurenceException("identifier");
        }

        this.declarations.put(identifier, sort);
    }

    /**
     * Define an identifier in this namespace. If the identifier is not yet
     * declared, it will be declared.
     * @param identifier The identifier
     * @param term The term which defines the identifier
     * @throws SortMismatchException
     * @throws MultipleOccurenceException
     */
    public void define(final String identifier, final SMTTermWrapper term)
            throws SortMismatchException, MultipleOccurenceException {
        if (Globals.useAssertions) {
            assert identifier != null;
            assert !identifier.equals("");
            assert term != null;
        }

        if (!this.declarations.containsKey(identifier)) {
            this.declare(identifier, term.getSort());
        } else {
            if (!term.getSort().equalsWith(this.declarations.get(identifier))) {
                throw new SortMismatchException(identifier);
            }
        }
        this.definitions.put(identifier, term);
    }

    public boolean isDeclared(final String identifier) {
        boolean declared = this.declarations.containsKey(identifier);
        if (!declared && this.parentNamespace != null) {
            declared = this.parentNamespace.isDeclared(identifier);
        }
        return declared;
    }

    public boolean isDefined(final String identifier) {
        boolean defined = this.definitions.containsKey(identifier);
        if (!defined && this.parentNamespace != null) {
            defined = this.parentNamespace.isDefined(identifier);
        }
        return defined;
    }

    /**
     * Returns the sort of an identifier (if declared). This method searches
     * also in the parent namespaces, if the identifier is not declared in this
     * namespace.
     * @param identifier The identifier
     * @return Sort of the identifier
     * @throws UndeclaredException
     */
    public AbstractSort getSort(final String identifier)
            throws UndeclaredException {
        AbstractSort sort = null;

        if (this.declarations.containsKey(identifier)) {
            sort = this.declarations.get(identifier);
        } else if (this.parentNamespace != null) {
            sort = this.parentNamespace.getSort(identifier);
        }

        if (sort == null) {
            throw new UndeclaredException(identifier);
        }

        return sort;
    }

    /**
     * Returns the defining term of an identifier (if defined). This method
     * searches also in the parent namespaces, if the identifier is not defined
     * in this namespace.
     * @param identifier The identifier
     * @return The term which defines the identifier
     * @throws UndefinedException
     */
    public SMTTermWrapper getDefinition(final String identifier)
            throws UndefinedException {
        SMTTermWrapper term = null;

        if (this.definitions.containsKey(identifier)) {
            term = this.definitions.get(identifier);
        } else if (this.parentNamespace != null) {
            term = this.parentNamespace.getDefinition(identifier);
        }

        if (term == null) {
            throw new UndefinedException(identifier);
        }

        return term;
    }
}
