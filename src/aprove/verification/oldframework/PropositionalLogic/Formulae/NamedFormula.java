package aprove.verification.oldframework.PropositionalLogic.Formulae;

/**
 * Implemented by formulae providing a label
 * @author patrick
 *
 */
public interface NamedFormula {

    public String getDescription();

    public String getType();

    public void setDescription(String description);

}
