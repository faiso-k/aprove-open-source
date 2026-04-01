package aprove.verification.dpframework.MCSProblem.sat_tools;

/*
 * Some static functions
 */

public class CommonOperations {

    public static String[] trimStringArray(String[] input)
    {
        String[] res = new String[input.length];
        for (int i=0; i<input.length; i++) {
            res[i] = input[i].trim();
        }
        return res;
    }

    public static boolean isLiteralNegative(String literal)
    {
        return literal.startsWith("-");
    }

    // -x => x
    public static String literalToVar(String literal)
    {
        if (CommonOperations.isLiteralNegative(literal)) {
            return literal.substring(1);
        } else {
            return literal;
        }
    }

    // -x=>x; x=>-x
    public static String negateLiteral(String literal)
    {
        if (CommonOperations.isLiteralNegative(literal)) {
            return CommonOperations.literalToVar(literal);
        } else {
            return "-"+literal;
        }
    }

    // unary: array of 0 and 1
    // if not unary return -1
    public static int unaryToDecimal(int[] unary)
    {
        boolean foundZero = false;
        int res=0;
        for (int i=0; i<unary.length; i++) {
            if (unary[i]==0) {
                foundZero = true;
            } else if (unary[i]==1) {
                if (foundZero) {
                    return -1; //11...100...01...
                } else {
                    res++;
                }
            } else {
                return -1;
            }
        }
        return res;
    }


    // bool: array of 0 and 1
    // if one of the bits is not 0 or 1 return -1
    public static int binaryToDecimal(int[] bool)
    {
        int res=0;
        int currCoef = 1;
        for (int i=bool.length-1; i>=0; i--) {
            if (bool[i]!=0 && bool[i]!=1) {
                return -1;
            }
            res = res + currCoef*bool[i];
            currCoef*=2;
        }
        return res;
    }

    // return number of bits needed to represent num numbers
    public static int numOfBits(int num)
    {
        double log2 = Math.log(num+1) / Math.log(2);
        return (int)Math.ceil(log2);
    }
}
