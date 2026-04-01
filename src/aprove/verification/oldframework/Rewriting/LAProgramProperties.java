package aprove.verification.oldframework.Rewriting;

import java.util.*;

import aprove.verification.oldframework.Syntax.*;

/**
 * All important and useful sorts and symbols are collected here.
 * Assign the values while parsing and never change them.
 *
 * @author dickmeis
 * @version $Id$
 */

public class LAProgramProperties {

    public Sort sortBool;
    public Sort sortNat;

    public ConstructorSymbol csTrue;
    public ConstructorSymbol csFalse;

    public ConstructorSymbol csZero;
    public ConstructorSymbol csSucc;

    public DefFunctionSymbol fsPlus;

    public DefFunctionSymbol fsEqual;
    public DefFunctionSymbol fsLesseq;
    public DefFunctionSymbol fsLess;
    public DefFunctionSymbol fsInequal;
    public DefFunctionSymbol fsGreater;
    public DefFunctionSymbol fsGreatereq;

    public DefFunctionSymbol fsNot;

    public Set<DefFunctionSymbol> laBasedFunctionSymbols = new HashSet<DefFunctionSymbol>();
    public Set<DefFunctionSymbol> semilaBasedFunctionSymbols = new HashSet<DefFunctionSymbol>();

}
