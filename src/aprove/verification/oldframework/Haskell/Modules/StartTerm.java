package aprove.verification.oldframework.Haskell.Modules;

import aprove.verification.oldframework.Utility.GenericStructures.*;

public class StartTerm extends Pair<String, StartTerm.Type> {

    private static final String H_TERMINATION_KEYWORD = "htermination";
    private static final String LAZY_TERMINATION_KEYWORD = "lazy-termination";

    public static enum Type {
        H_TERMINATION {
            @Override
            public String getKeyword() {
                return StartTerm.H_TERMINATION_KEYWORD;
            }
        },
        LAZY_TERMINATION {
            @Override
            public String getKeyword() {
                return StartTerm.LAZY_TERMINATION_KEYWORD;
            }
        };


        public abstract String getKeyword();

        /**
         * returns the type that is represented by the given string,
         * or null if no such type exists
         * @param typeString the type string to parse
         * @return the type the string corresponds to, or null
         */
        public static Type getTypeOf(String typeString) {
            for(Type type : Type.values()) {
                if (typeString.equals(type.getKeyword())) {
                    return type;
                }
            }
            return null;
        }
    }


    public StartTerm(String term, Type type) {
        super(term, type);
    }

    public String getTerm() {
        return this.x;
    }

    public Type getType() {
        return this.y;
    }

    /**
     * @return a String representation of this start term, which can be parsed again
     * @see HaskellTools.parseStartTerm()
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("<");
        sb.append(this.getType().getKeyword());
        sb.append("> ");
        sb.append(this.getTerm());
        return sb.toString();
    }
}
