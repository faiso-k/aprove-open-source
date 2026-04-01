package aprove.verification.oldframework.Rewriting.SemanticLabelling;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.MaxMinPolynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

public class InterpretationPoolCreator {

    private static boolean smallSet = true;

    private static MaxMinPolynomial zero = MaxMinPolynomial.ZERO;
    private static MaxMinPolynomial one = MaxMinPolynomial.ONE;
    private static MaxMinPolynomial three =
        MaxMinPolynomial.create(VarPolynomial.create(3));
    private static MaxMinPolynomial seven =
        MaxMinPolynomial.create(VarPolynomial.create(7));
    private static MaxMinPolynomial x_0 =
        MaxMinPolynomial.create(VarPolynomial.createVariable("x_0"));
    private static MaxMinPolynomial x_1 =
        MaxMinPolynomial.create(VarPolynomial.createVariable("x_1"));
    private static MaxMinPolynomial x_0plus1 =
        MaxMinPolynomial.create(VarPolynomial.createVariable("x_0").plus(VarPolynomial.create(1)));
    private static MaxMinPolynomial x_0plus3 =
        MaxMinPolynomial.create(VarPolynomial.createVariable("x_0").plus(VarPolynomial.create(3)));
    private static MaxMinPolynomial x_1plus1 =
        MaxMinPolynomial.create(VarPolynomial.createVariable("x_1").plus(VarPolynomial.create(1)));
    private static MaxMinPolynomial x_1plus3 =
        MaxMinPolynomial.create(VarPolynomial.createVariable("x_1").plus(VarPolynomial.create(3)));
    private static MaxMinPolynomial x_0plusx_1 =
        MaxMinPolynomial.create(VarPolynomial.createVariable("x_0").plus(VarPolynomial.createVariable("x_1")));
    private static MaxMinPolynomial x_0times2 =
        MaxMinPolynomial.create(VarPolynomial.createVariable("x_0").times(SimplePolynomial.create(2)));
    private static MaxMinPolynomial x_0times3 =
        MaxMinPolynomial.create(VarPolynomial.createVariable("x_0").times(SimplePolynomial.create(3)));
    private static MaxMinPolynomial x_0times7 =
        MaxMinPolynomial.create(VarPolynomial.createVariable("x_0").times(SimplePolynomial.create(7)));
    private static MaxMinPolynomial x_1times2 =
        MaxMinPolynomial.create(VarPolynomial.createVariable("x_1").times(SimplePolynomial.create(2)));
    private static MaxMinPolynomial x_1times3 =
        MaxMinPolynomial.create(VarPolynomial.createVariable("x_1").times(SimplePolynomial.create(3)));
    private static MaxMinPolynomial x_1times7 =
        MaxMinPolynomial.create(VarPolynomial.createVariable("x_1").times(SimplePolynomial.create(7)));
    private static MaxMinPolynomial x_0timesx_1 =
        MaxMinPolynomial.create(VarPolynomial.createVariable("x_0").times(VarPolynomial.createVariable("x_1")));
    private static MaxMinPolynomial minimum =
        MaxMinPolynomial.createMinPoly(InterpretationPoolCreator.createMinInterp());
    private static MaxMinPolynomial maximum =
        MaxMinPolynomial.create(InterpretationPoolCreator.createMaxInterp());
    private static MaxMinPolynomial monos =
        (MaxMinPolynomial.create(VarPolynomial.createVariable("x_0")).monos(MaxMinPolynomial.create(VarPolynomial.createVariable("x_1"))));


    /**
     * default values are -1 as carrier, representing the natural numbers
     * @return
     */
    public static ArrayList<Set<MaxMinPolynomial>> createIntPool () {
        return InterpretationPoolCreator.createIntPool(-1, 2);
    }

    /**
     * @param cSS the CarrierSize
     * @return
     */
    public static ArrayList<Set<MaxMinPolynomial>> createIntPool (int cSS) {
        return InterpretationPoolCreator.createIntPool(cSS, 2);
    }

    /**
     *
     * @param cSS the CarrierSize
     * @param maxArity the maximal arity of the function symbols of the TRS
     * @return
     */
    private static ArrayList<Set<MaxMinPolynomial>> createIntPool (int cSS, int maxArity) {
        switch (cSS) {
        case -1 : {

            ArrayList<Set<MaxMinPolynomial>> returnValue = new ArrayList<Set<MaxMinPolynomial>>(3);
            returnValue.add(0, InterpretationPoolCreator.createIntSet(-1, 0));
            returnValue.add(1, InterpretationPoolCreator.createIntSet(-1, 1));
            returnValue.add(2, InterpretationPoolCreator.createIntSet(-1, 2));
            return returnValue;
        }
        case 2 : {
            ArrayList<Set<MaxMinPolynomial>> returnValue = new ArrayList<Set<MaxMinPolynomial>>(3);
            returnValue.add(0, InterpretationPoolCreator.createIntSet(2, 0));
            returnValue.add(1, InterpretationPoolCreator.createIntSet(2, 1));
            returnValue.add(2, InterpretationPoolCreator.createIntSet(2, 2));
            return returnValue;

        }
        case 3 : {

            ArrayList<Set<MaxMinPolynomial>> returnValue = new ArrayList<Set<MaxMinPolynomial>>(3);
            returnValue.add(0, InterpretationPoolCreator.createIntSet(3, 0));
            returnValue.add(1, InterpretationPoolCreator.createIntSet(3, 1));
            returnValue.add(2, InterpretationPoolCreator.createIntSet(3, 2));
            return returnValue;
        }

        default : {
            ArrayList<Set<MaxMinPolynomial>> returnValue = new ArrayList<Set<MaxMinPolynomial>>(3);
            returnValue.add(0, InterpretationPoolCreator.createIntSet(7, 0));
            returnValue.add(1, InterpretationPoolCreator.createIntSet(7, 1));
            returnValue.add(2, InterpretationPoolCreator.createIntSet(7, 2));
            return returnValue;

        }
        }

    }

    /**
     *  default -1 as carrier size, representing the natural numbers
     * @param arity the arity of the function symbol
     * to which an interpretation set is desired
     * @return a set of interpretations
     */
    public static Set<MaxMinPolynomial> createIntSet(int arity) {
        Set<MaxMinPolynomial> resultSet = new HashSet<MaxMinPolynomial>();
        if(arity == 0) {
            resultSet.add(InterpretationPoolCreator.zero);
            resultSet.add(InterpretationPoolCreator.one);
            resultSet.add(InterpretationPoolCreator.three);
            resultSet.add(InterpretationPoolCreator.seven);
        }
        else {
            if(arity == 1) {
                resultSet.add(InterpretationPoolCreator.zero);
                resultSet.add(InterpretationPoolCreator.one);
                resultSet.add(InterpretationPoolCreator.three);
                resultSet.add(InterpretationPoolCreator.seven);
                resultSet.add(InterpretationPoolCreator.x_0);
                resultSet.add(InterpretationPoolCreator.x_0plus1);
                resultSet.add(InterpretationPoolCreator.x_0plus3);
                resultSet.add(InterpretationPoolCreator.x_0times2);
                resultSet.add(InterpretationPoolCreator.x_0times3);
                resultSet.add(InterpretationPoolCreator.x_0times7);
            }
            else {
                resultSet.add(InterpretationPoolCreator.zero);
                resultSet.add(InterpretationPoolCreator.one);
                resultSet.add(InterpretationPoolCreator.three);
                resultSet.add(InterpretationPoolCreator.seven);
                resultSet.add(InterpretationPoolCreator.x_0);
                resultSet.add(InterpretationPoolCreator.x_0plus1);
                resultSet.add(InterpretationPoolCreator.x_0plus3);
                resultSet.add(InterpretationPoolCreator.x_0times2);
                resultSet.add(InterpretationPoolCreator.x_0times3);
                resultSet.add(InterpretationPoolCreator.x_0times7);
                resultSet.add(InterpretationPoolCreator.x_1);
                resultSet.add(InterpretationPoolCreator.x_1plus1);
                resultSet.add(InterpretationPoolCreator.x_1plus3);
                resultSet.add(InterpretationPoolCreator.x_1times2);
                resultSet.add(InterpretationPoolCreator.x_1times3);
                resultSet.add(InterpretationPoolCreator.x_1times7);
                resultSet.add(InterpretationPoolCreator.x_0plusx_1);
                resultSet.add(InterpretationPoolCreator.x_0timesx_1);
                resultSet.add(InterpretationPoolCreator.minimum);
                resultSet.add(InterpretationPoolCreator.maximum);
            }
        }
        return resultSet;
    }

    /**
     *
     * @param cSS the size of the carrier
     * @param arity the arity of the function symbol
     * to which an interpretation set is desired
     * @return a set of interpretations
     */
    public static Set<MaxMinPolynomial> createIntSet(int cSS, int arity) {
        Set<MaxMinPolynomial> resultSet = new HashSet<MaxMinPolynomial>();
        if(InterpretationPoolCreator.smallSet) {
            if(arity == 0) {
                resultSet.add(InterpretationPoolCreator.zero);
                resultSet.add(InterpretationPoolCreator.one);
            }
            else {
                if(arity == 1) {
                    resultSet.add(InterpretationPoolCreator.zero);
                    resultSet.add(InterpretationPoolCreator.one);
                    resultSet.add(InterpretationPoolCreator.x_0);
                    resultSet.add(InterpretationPoolCreator.x_0plus1);
                }
                else {
                    resultSet.add(InterpretationPoolCreator.zero);
                    resultSet.add(InterpretationPoolCreator.one);
                    resultSet.add(InterpretationPoolCreator.x_0);
                    resultSet.add(InterpretationPoolCreator.x_1);
                    resultSet.add(InterpretationPoolCreator.x_0plusx_1);
                    resultSet.add(InterpretationPoolCreator.minimum);
                    resultSet.add(InterpretationPoolCreator.maximum);
                }
            }
        }
        else {

        if(cSS == -1) {
            if(arity == 0) {
                resultSet.add(InterpretationPoolCreator.zero);
                resultSet.add(InterpretationPoolCreator.one);
                resultSet.add(InterpretationPoolCreator.three);
            }
            else {
                if(arity == 1) {
                    resultSet.add(InterpretationPoolCreator.zero);
                    resultSet.add(InterpretationPoolCreator.one);
                    resultSet.add(InterpretationPoolCreator.three);
                    resultSet.add(InterpretationPoolCreator.seven);
                    resultSet.add(InterpretationPoolCreator.x_0);
                    resultSet.add(InterpretationPoolCreator.x_0plus1);
                    resultSet.add(InterpretationPoolCreator.x_0plus3);
                    resultSet.add(InterpretationPoolCreator.x_0times3);
                    resultSet.add(InterpretationPoolCreator.x_0times7);
                }
                else {
                    resultSet.add(InterpretationPoolCreator.zero);
                    resultSet.add(InterpretationPoolCreator.one);
                    resultSet.add(InterpretationPoolCreator.three);
                    resultSet.add(InterpretationPoolCreator.x_0);
                    resultSet.add(InterpretationPoolCreator.x_0plus1);
                    resultSet.add(InterpretationPoolCreator.x_0plus3);
                    resultSet.add(InterpretationPoolCreator.x_0times2);
                    resultSet.add(InterpretationPoolCreator.x_0times3);
                    resultSet.add(InterpretationPoolCreator.x_1);
                    resultSet.add(InterpretationPoolCreator.x_1plus1);
                    resultSet.add(InterpretationPoolCreator.x_1plus3);
                    resultSet.add(InterpretationPoolCreator.x_1times2);
                    resultSet.add(InterpretationPoolCreator.x_1times3);
                    resultSet.add(InterpretationPoolCreator.x_0plusx_1);
                    resultSet.add(InterpretationPoolCreator.x_0timesx_1);
                    resultSet.add(InterpretationPoolCreator.minimum);
                    resultSet.add(InterpretationPoolCreator.maximum);
                }
            }
        }
        else {
            if(cSS == 2) {
                if(arity == 0) {
                    resultSet.add(InterpretationPoolCreator.zero);
                    resultSet.add(InterpretationPoolCreator.one);
                }
                else {
                    if(arity == 1) {
                        resultSet.add(InterpretationPoolCreator.zero);
                        resultSet.add(InterpretationPoolCreator.one);
                        resultSet.add(InterpretationPoolCreator.x_0);
                        resultSet.add(InterpretationPoolCreator.x_0plus1);
                    }
                    else {
                        resultSet.add(InterpretationPoolCreator.zero);
                        resultSet.add(InterpretationPoolCreator.one);
                        resultSet.add(InterpretationPoolCreator.x_0);
                        resultSet.add(InterpretationPoolCreator.x_0plus1);
                        resultSet.add(InterpretationPoolCreator.x_1);
                        resultSet.add(InterpretationPoolCreator.x_1plus1);
                        resultSet.add(InterpretationPoolCreator.minimum);
                        resultSet.add(InterpretationPoolCreator.maximum);
                    }
                }
            }
            else {
                if(cSS < 8) {
                    if(arity == 0) {
                        resultSet.add(InterpretationPoolCreator.zero);
                        resultSet.add(InterpretationPoolCreator.one);
                    }
                    else {
                        if(arity == 1) {
                            resultSet.add(InterpretationPoolCreator.zero);
                            resultSet.add(InterpretationPoolCreator.one);
                            resultSet.add(InterpretationPoolCreator.x_0);
                            resultSet.add(InterpretationPoolCreator.x_0plus1);
                        }
                        else {
                            resultSet.add(InterpretationPoolCreator.zero);
                            resultSet.add(InterpretationPoolCreator.one);
                            resultSet.add(InterpretationPoolCreator.x_0);
                            resultSet.add(InterpretationPoolCreator.x_0plus1);
                            resultSet.add(InterpretationPoolCreator.x_1);
                            resultSet.add(InterpretationPoolCreator.x_1plus1);
                            resultSet.add(InterpretationPoolCreator.x_0plusx_1);
                            resultSet.add(InterpretationPoolCreator.x_0timesx_1);
                            resultSet.add(InterpretationPoolCreator.x_0times2);
                            resultSet.add(InterpretationPoolCreator.x_1times2);
                            resultSet.add(InterpretationPoolCreator.minimum);
                            resultSet.add(InterpretationPoolCreator.maximum);
                        }
                    }
                }
                else {
                    if(arity == 0) {
                        resultSet.add(InterpretationPoolCreator.zero);
                        resultSet.add(InterpretationPoolCreator.one);
                        resultSet.add(InterpretationPoolCreator.three);
                        resultSet.add(InterpretationPoolCreator.seven);
                    }
                    else {
                        if(arity == 1) {
                            resultSet.add(InterpretationPoolCreator.zero);
                            resultSet.add(InterpretationPoolCreator.one);
                            resultSet.add(InterpretationPoolCreator.three);
                            resultSet.add(InterpretationPoolCreator.seven);
                            resultSet.add(InterpretationPoolCreator.x_0);
                            resultSet.add(InterpretationPoolCreator.x_0plus1);
                            resultSet.add(InterpretationPoolCreator.x_0plus3);
                            resultSet.add(InterpretationPoolCreator.x_0times2);
                            resultSet.add(InterpretationPoolCreator.x_0times3);
                        }
                        else {
                            resultSet.add(InterpretationPoolCreator.zero);
                            resultSet.add(InterpretationPoolCreator.one);
                            resultSet.add(InterpretationPoolCreator.three);
                            resultSet.add(InterpretationPoolCreator.seven);
                            resultSet.add(InterpretationPoolCreator.x_0);
                            resultSet.add(InterpretationPoolCreator.x_0plus1);
                            resultSet.add(InterpretationPoolCreator.x_0plus3);
                            resultSet.add(InterpretationPoolCreator.x_0times2);
                            resultSet.add(InterpretationPoolCreator.x_0times3);
                            resultSet.add(InterpretationPoolCreator.x_1);
                            resultSet.add(InterpretationPoolCreator.x_1plus1);
                            resultSet.add(InterpretationPoolCreator.x_1plus3);
                            resultSet.add(InterpretationPoolCreator.x_1times2);
                            resultSet.add(InterpretationPoolCreator.x_1times3);
                            resultSet.add(InterpretationPoolCreator.x_0plusx_1);
                            resultSet.add(InterpretationPoolCreator.x_0timesx_1);
                            resultSet.add(InterpretationPoolCreator.minimum);
                            resultSet.add(InterpretationPoolCreator.maximum);
                        }
                    }
                }
            }
        }
        }//Closing bracket of else of smallset hack
        return resultSet;
    }



    private static Set<VarPolynomial> createMinInterp() {
        Set<VarPolynomial> returnSet = new HashSet<VarPolynomial>(2);
        returnSet.add(VarPolynomial.createVariable("x_0"));
        returnSet.add(VarPolynomial.createVariable("x_1"));
        return returnSet;
    }

    private static Set<Set<VarPolynomial>> createMaxInterp() {
        Set<VarPolynomial> dummySet0 = new HashSet<VarPolynomial>(1);
        Set<VarPolynomial> dummySet1 = new HashSet<VarPolynomial>(1);
        Set<Set<VarPolynomial>> returnSet = new HashSet<Set<VarPolynomial>>(2);
        dummySet0.add(VarPolynomial.createVariable("x_0"));
        dummySet1.add(VarPolynomial.createVariable("x_1"));
        returnSet.add(dummySet0);
        returnSet.add(dummySet1);
        return returnSet;
    }

}
