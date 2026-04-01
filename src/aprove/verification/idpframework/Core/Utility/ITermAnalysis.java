package aprove.verification.idpframework.Core.Utility;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public interface ITermAnalysis<T extends ITerm<?>> {

    /**
     * @return the map of pre-defined function symbols
     */
    public IDPPredefinedMap getPredefinedMap();

    /**
     * Extracts all function symbols that occur in the user-defined rules.
     * @return
     */
    public ImmutableSet<IFunctionSymbol<?>> getFunctionSymbols();

    /**
     * Extracts all function symbols that occur at the root positions of LHS of
     * user-defined rules.
     * @return
     */
    public ImmutableSet<IFunctionSymbol<?>> getRootSymbols();

    /**
     * Extracts all variables that occur in the user-defined rules.
     * @return
     */
    public ImmutableSet<IVariable<?>> getVariables();

    /**
     * @return true iff fs is a constructor
     */
    public Boolean isConstructor(final IFunctionSymbol<?> fs);

    /**
     * get T as a mapping from defined symbols to corresponding user-defined
     * rules
     */
    public ImmutableMap<IFunctionSymbol<?>, ImmutableSet<T>> getTermMap();

    /**
     * Extracts all terms used in the ruled.
     * @return all terms used in the ruled.
     */
    public ImmutableSet<? extends T> getTerms();

    /**
     * Extract all domains used in a collection of user-defined rules.
     */
    public ImmutableSet<Domain> getDomains();

    public ImmutableSet<IFunctionSymbol<?>> getPredefinedFunctions();

    /**
     * Checks if unrestricted integers occur in the rules.
     */
    public boolean hasUnrestrictedInt();

    /**
     * Checks if restricted integers occur in the rules.
     */
    public boolean hasRestrictedInt();

    /**
     * Checks if bitwise operations occur in the rules.
     */
    public boolean hasBitwiseOps();

    /**
     * Checks if defined predefined symbols (sic!) occur in the rules.
     */
    public boolean hasPredefinedDefSymbols();

}