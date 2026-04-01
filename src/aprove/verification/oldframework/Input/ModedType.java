/**
 * By this class we manage all the input languages which we can handle
 * and what we can do with them, e.g termination analysis,
 * proving of theorems...
 * By this class an invalid combination is prevented.
 *
 * Termination analysis is available for any kind of input language except STRS.
 * Proving of theorems is only possible for FP and STRS.
 *
 * The factory methods create the valid combinations of language and mode.
 *
 * @author dickmeis
 */

package aprove.verification.oldframework.Input;

public class ModedType {

    private Language language;
    private HandlingMode mode;

    private ModedType(Language language, HandlingMode mode) {
        this.language = language;
        this.mode = mode;
    }

    /**
     * Create a ModedInput if we are able to handle the combination of
     * language and mode. Otherwise return null.
     *
     * @param language
     * @param mode
     *
     * @return a ModedInput consisting of language and mode
     *     if the combination is valid otherwise null
     */
    static public ModedType createModedInput(Language language, HandlingMode mode) {
        if (language.supports(mode)){
            return new ModedType(language, mode);
        }
        return null;
    }

    /**
     * Create a ModedInput with default handling mode (as returned by
     * language.getDefault).
     */
    static public ModedType createModedInput(Language language) {
        return ModedType.createModedInput(language, language.getDefaultMode());
    }

    public Language getLanguage(){
        return this.language;
    }

    public HandlingMode getHandlingMode(){
        return this.mode;
    }

    /**
     * Sets handling mode if supported by the language.
     * @return true iff handling mode is supported
     */
    public boolean setMode(HandlingMode mode){
        if (this.language.supports(mode)){
            this.mode = mode;
            return true;
        }
        return false;
    }

}

