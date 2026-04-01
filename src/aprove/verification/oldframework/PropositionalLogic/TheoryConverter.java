package aprove.verification.oldframework.PropositionalLogic;

/**
 * can convert properties of the source theory into
 * formulas of the destination-theory
 *
 * Useful together with the TheoryConverterVisitor for Formulas
 *
 * @author thiemann
 *
 * @param <T_SRC>
 * @param <T_DEST>
 */
public interface TheoryConverter<T_SRC, T_DEST> {

    public Formula<T_DEST> convert(T_SRC theoryProposition);

}
