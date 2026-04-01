package aprove.verification.oldframework.Input;

public class TypedInput {

    private final ModedType modedType;
    private final Object input;
    private final Input originInput;

    public TypedInput(final ModedType modedType, final Object input, final Input originInput){
        this.modedType = modedType;
        this.input = input;
        this.originInput = originInput;
    }

    /**
     * This is a shortcut for getModedType().getLanguage()
     * @return the language
     */
    public Language getLanguage(){
        return this.modedType.getLanguage();
    }

    /**
     * This is a shortcut for getModedType().getHandlingMode()
     * @return the HandlingMode
     */
    public HandlingMode getHandlingMode(){
        return this.modedType.getHandlingMode();
    }

    public ModedType getModedType(){
        return this.modedType;
    }

    public Object getInput(){
        return this.input;
    }

    public Input getOriginInput(){
        return this.originInput;
    }

    @Override
    public String toString() {
        if (this.modedType != null && this.modedType.getLanguage() != null) {
            return "Moded Type Language: "
                    + this.modedType.getLanguage().toString();
        } else {
            return super.toString();
        }
    }
}
