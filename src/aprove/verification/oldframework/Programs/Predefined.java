package aprove.verification.oldframework.Programs;

import aprove.verification.oldframework.Syntax.*;

/**
 * This class stores predefined things of a program. For example the sort
 * boolean, their constructors and functions. This is done to determine
 * the semantics of certain objects.
 * @author Christian Haselbach
 * @version $Id$
 */

public class Predefined {

    protected Sort bool = null;
    protected DefFunctionSymbol fAnd = null;
    protected DefFunctionSymbol fOr = null;
    protected DefFunctionSymbol fNot = null;
    protected ConstructorSymbol cTrue = null;
    protected ConstructorSymbol cFalse = null;

    protected Predefined() {
    }

    protected Predefined(Sort bool, ConstructorSymbol cTrue, ConstructorSymbol cFalse) {
    this.bool = bool;
    this.cTrue = cTrue;
    this.cFalse = cFalse;
    }

    protected Predefined(Sort bool, ConstructorSymbol cTrue, ConstructorSymbol cFalse, DefFunctionSymbol fAnd, DefFunctionSymbol fOr, DefFunctionSymbol fNot) {
    this.bool = bool;
    this.cTrue = cTrue;
    this.cFalse = cFalse;
    this.fAnd = fAnd;
    this.fOr = fOr;
    this.fNot = fNot;
    }

    public static Predefined create() {
    return new Predefined();
    }

    public static Predefined create(Sort bool, ConstructorSymbol cTrue, ConstructorSymbol cFalse) {
    return new Predefined(bool, cTrue, cFalse);
    }

    public static Predefined create(Sort bool, ConstructorSymbol cTrue, ConstructorSymbol cFalse, DefFunctionSymbol fAnd, DefFunctionSymbol fOr, DefFunctionSymbol fNot) {
    return new Predefined(bool, cTrue, cFalse, fAnd, fOr, fNot);
    }

    public Sort getBool() {
    return this.bool;
    }

    public void setBool(Sort s) {
    this.bool = s;
    }

    public ConstructorSymbol getTrue() {
    return this.cTrue;
    }

    public void setTrue(ConstructorSymbol fsym) {
    this.cTrue = fsym;
    }

    public ConstructorSymbol getFalse() {
    return this.cFalse;
    }

    public void setFalse(ConstructorSymbol fsym) {
    this.cFalse = fsym;
    }

    public DefFunctionSymbol getAnd() {
    return this.fAnd;
    }

    public void setAnd(DefFunctionSymbol fsym) {
    this.fAnd = fsym;
    }

    public DefFunctionSymbol getOr() {
    return this.fOr;
    }

    public void setOr(DefFunctionSymbol fsym) {
    this.fOr = fsym;
    }

    public DefFunctionSymbol getNot() {
    return this.fNot;
    }

    public void setNot(DefFunctionSymbol fsym) {
    this.fNot = fsym;
    }

}

