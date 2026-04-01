/*created on 26.09.2004
 * In this class all the inforamtion of the given input are collected.
 * Since FullPass works on a tree structure it is written recursively
 * in a depth first manner.
 */

/**
 * @author dickmeis
 * @version $Id$
 */

package aprove.input.Programs.strs;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.input.Generated.strs.analysis.*;
import aprove.input.Generated.strs.node.*;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class FullPass extends DepthFirstAdapter {

    private static final boolean DEBUB_STACK = Globals.DEBUG_DICKMEIS && false;

    protected static Logger logger = Logger
            .getLogger("aprove.input.Programs.strs.FullPass");

    // contains the defined function symbols found in the the prepass
    // used to distinguish between constructors and function symbols
    private Stack<String> definedFunctSymb;

    // the symbols contain in their class the information about sorts and
    // arguments
    private HashMap<String, DefFunctionSymbol> defFunc;

    private HashMap<String, ConstructorSymbol> constructors;

    // sorts that have been declared
    private Stack<String> declaredSorts;

    // sorts with defined constructors
    // the constructors are collected within the Sort class
    private HashMap<String, Sort> sorts;

    // sorts of the arguments in a function/constructor declaration
    private List<Sort> funcArgSorts;

    // the expected sorts of a term
    // note: when entering a rule declaration or a condition
    // we don't know the sort yet
    // thus we check later that the sorts for lhs and rhs are identical
    private Stack<Sort> expectedTermSorts;

    // constructed terms
    // with this stack we construct the rules
    private MarkedStack<AlgebraTerm> termStack;

    // the constructed program:
    // symbols, rules, ...
    private Program program;

    // found errors
    private ParseErrors parseErrors;

    private Stack<String> reservedNames;

    private Sort boolSort;
    private Sort natSort;

    private AlgebraTerm tTrue;
    private AlgebraTerm tFalse;
    private DefFunctionSymbol fAnd;

    public FullPass(Stack<String> definedFunctSymb) {

        this.definedFunctSymb = definedFunctSymb;

        this.declaredSorts = new Stack<String>();
        this.funcArgSorts = new LinkedList<Sort>();

        this.sorts = new HashMap<String, Sort>();

        this.program = Program.create();
        this.program.laProgramProperties = new LAProgramProperties();

        this.termStack = new MarkedStack<AlgebraTerm>();

        this.parseErrors = new ParseErrors();

        this.constructors = new HashMap<String, ConstructorSymbol>();
        this.defFunc = new HashMap<String, DefFunctionSymbol>();

        this.expectedTermSorts = new Stack<Sort>();

        this.reservedNames = new Stack<String>();

        // create predefined sorts and their rules
        try {
            String functionName;
            Vector<Sort> argSorts;
            DefFunctionSymbol dfs;
            AlgebraTerm args[] = new AlgebraTerm[2];
            AlgebraTerm args1[] = new AlgebraTerm[1];
            AlgebraTerm lhs;
            AlgebraTerm rhs;
            Rule r;

            /*
             * create Sort Bool
             */

            String boolName = "Bool";

            this.boolSort = Sort.create(boolName);

            ConstructorSymbol csTrue = ConstructorSymbol.create("true", 0, this.boolSort);
            this.constructors.put("true", csTrue);
            this.program.addConstructorSymbol(csTrue);
            this.program.laProgramProperties.csTrue = csTrue;

            ConstructorSymbol csFalse = ConstructorSymbol.create("false", 0, this.boolSort);
            this.constructors.put("false", csFalse);
            this.program.addConstructorSymbol(csFalse);
            this.program.laProgramProperties.csFalse = csFalse;

            this.boolSort.addConstructorSymbol(csTrue);
            this.boolSort.addConstructorSymbol(csFalse);

            this.program.addSort(this.boolSort);
            this.program.laProgramProperties.sortBool = this.boolSort;
            this.declaredSorts.add(boolName);
            this.sorts.put(boolName, this.boolSort);

            /*
             * equal_Bool
             */
            functionName = "equal_" + boolName;

            if(this.definedFunctSymb.contains(functionName)){
                ParseError pe = new ParseError();
                pe.setMessage("Name clash: " + functionName + " is a resevered function name.");
                this.parseErrors.add(pe);
            }
            this.reservedNames.add(functionName);

            argSorts = new Vector<Sort>();
            argSorts.add(this.boolSort);
            argSorts.add(this.boolSort);

            dfs = DefFunctionSymbol.create(functionName, argSorts, this.boolSort);
            this.boolSort.setEqualOp(dfs);
            dfs.setTermination(true); // by construction
            this.program.addPredefFunctionSymbol(dfs);
            dfs.setSignatureClass(Symbol.BOOLSIG);
            this.definedFunctSymb.add(functionName);
            this.defFunc.put(functionName, dfs);

            this.tTrue = ConstructorApp.create(csTrue);
            this.tFalse = ConstructorApp.create(csFalse);

            args[0] = this.tTrue;
            args[1] = this.tFalse;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tFalse);
            this.program.addRule(dfs, r);

            args[0] = this.tFalse;
            args[1] = this.tTrue;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tFalse);
            this.program.addRule(dfs, r);

            args[0] = this.tTrue;
            args[1] = this.tTrue;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tTrue);
            this.program.addRule(dfs, r);

            args[0] = this.tFalse;
            args[1] = this.tFalse;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tTrue);
            this.program.addRule(dfs, r);


            /*
             * and
             */
            functionName = "and";

            if(this.definedFunctSymb.contains(functionName)){
                ParseError pe = new ParseError();
                pe.setMessage("Name clash: " + functionName + " is a resevered function name.");
                this.parseErrors.add(pe);
            }
            this.reservedNames.add(functionName);

            argSorts = new Vector<Sort>();
            argSorts.add(this.boolSort);
            argSorts.add(this.boolSort);

            this.fAnd = DefFunctionSymbol.create(functionName, argSorts, this.boolSort);
            this.program.addPredefFunctionSymbol(this.fAnd);
            this.definedFunctSymb.add(functionName);
            this.defFunc.put(functionName, this.fAnd);

            VariableSymbol vsX_B = VariableSymbol.create("X", this.boolSort);
            AlgebraVariable vX_b = AlgebraVariable.create(vsX_B);

            args[0] = this.tTrue;
            args[1] = vX_b;
            lhs = DefFunctionApp.create(this.fAnd, args);
            r = Rule.create(lhs, vX_b);
            this.program.addRule(this.fAnd, r);

            args[0] = vX_b;
            args[1] = this.tTrue;
            lhs = DefFunctionApp.create(this.fAnd, args);
            r = Rule.create(lhs, vX_b);
            this.program.addRule(this.fAnd, r);

            args[0] = this.tFalse;
            args[1] = vX_b;
            lhs = DefFunctionApp.create(this.fAnd, args);
            r = Rule.create(lhs, this.tFalse);
            this.program.addRule(this.fAnd, r);

            args[0] = vX_b;
            args[1] = this.tFalse;
            lhs = DefFunctionApp.create(this.fAnd, args);
            r = Rule.create(lhs, this.tFalse);
            this.program.addRule(this.fAnd, r);

            /*
             * not
             */
            functionName = "not";

            if(this.definedFunctSymb.contains(functionName)){
                ParseError pe = new ParseError();
                pe.setMessage("Name clash: " + functionName + " is a resevered function name.");
                this.parseErrors.add(pe);
            }
            this.reservedNames.add(functionName);

            argSorts = new Vector<Sort>();
            argSorts.add(this.boolSort);

            dfs = DefFunctionSymbol.create(functionName, argSorts, this.boolSort);

            this.definedFunctSymb.add(functionName);
            this.program.addPredefFunctionSymbol(dfs);
            this.defFunc.put(functionName, dfs);
            this.program.laProgramProperties.fsNot = dfs;

            args1[0] = this.tTrue;
            lhs = DefFunctionApp.create(dfs, args1);
            r = Rule.create(lhs, this.tFalse);
            this.program.addRule(dfs, r);

            args1[0] = this.tFalse;
            lhs = DefFunctionApp.create(dfs, args1);
            r = Rule.create(lhs, this.tTrue);
            this.program.addRule(dfs, r);


            /*
             * create Sort Nat
             */
            String natName = "Nat";

            this.natSort = Sort.create(natName);

            ConstructorSymbol csZero = ConstructorSymbol.create("0", 0, this.natSort);
            this.constructors.put("0", csZero);
            this.program.addConstructorSymbol(csZero);
            this.program.laProgramProperties.csZero = csZero;

            List<Sort> argSort = new ArrayList<Sort>(1);
            argSort.add(this.natSort);
            ConstructorSymbol csSucc = ConstructorSymbol.create("s", 1, this.natSort);
            this.constructors.put("s", csSucc);
            this.program.addConstructorSymbol(csSucc);
            this.program.laProgramProperties.csSucc = csSucc;

            this.natSort.addConstructorSymbol(csZero);
            this.natSort.addConstructorSymbol(csSucc);

            this.program.addSort(this.natSort);
            this.program.laProgramProperties.sortNat = this.natSort;
            this.declaredSorts.add(natName);
            this.sorts.put(natName, this.natSort);

            /*
             * equal
             */
            functionName = "equal";

            if(this.definedFunctSymb.contains(functionName)){
                ParseError pe = new ParseError();
                pe.setMessage("Name clash: " + functionName + " is a resevered function name.");
                this.parseErrors.add(pe);
            }
            this.reservedNames.add(functionName);

            argSorts = new Vector<Sort>();
            argSorts.add(this.natSort);
            argSorts.add(this.natSort);

            dfs = DefFunctionSymbol.create(functionName, argSorts, this.boolSort);
            this.definedFunctSymb.add(functionName);
            this.defFunc.put(functionName, dfs);
            this.natSort.setEqualOp(dfs);
            dfs.setTermination(true); // by construction

            this.program.addPredefFunctionSymbol(dfs);
            this.program.laProgramProperties.fsEqual = dfs;
            dfs.setSignatureClass(Symbol.BOOLSIG);

            AlgebraTerm tZero = ConstructorApp.create(csZero);

            VariableSymbol vsX = VariableSymbol.create("X", this.natSort);
            AlgebraVariable vX = AlgebraVariable.create(vsX);
            AlgebraTerm[] v = {vX};
            AlgebraTerm tSuccX = ConstructorApp.create(csSucc, v);

            VariableSymbol vsY = VariableSymbol.create("Y", this.natSort);
            AlgebraVariable vY = AlgebraVariable.create(vsY);
            v[0]=vY;
            AlgebraTerm tSuccY = ConstructorApp.create(csSucc, v);

            args[0] = tZero;
            args[1] = tZero;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tTrue);
            this.program.addRule(dfs, r);

            args[0] = tSuccX;
            args[1] = tZero;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tFalse);
            this.program.addRule(dfs, r);

            args[0] = tZero;
            args[1] = tSuccY;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tFalse);
            this.program.addRule(dfs, r);

            args[0] = tSuccX;
            args[1] = tSuccY;
            lhs = DefFunctionApp.create(dfs, args);
            args[0] = vX;
            args[1] = vY;
            rhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, rhs);
            this.program.addRule(dfs, r);


            /*
             * inequal
             */
            functionName = "inequal";

            if(this.definedFunctSymb.contains(functionName)){
                ParseError pe = new ParseError();
                pe.setMessage("Name clash: " + functionName + " is a resevered function name.");
                this.parseErrors.add(pe);
            }
            this.reservedNames.add(functionName);

            argSorts = new Vector<Sort>();
            argSorts.add(this.natSort);
            argSorts.add(this.natSort);

            dfs = DefFunctionSymbol.create(functionName, argSorts, this.boolSort);
            dfs.setSignatureClass(Symbol.BOOLSIG);
            dfs.setTermination(true); // by construction
            this.definedFunctSymb.add(functionName);
            this.defFunc.put(functionName, dfs);
            this.program.addPredefFunctionSymbol(dfs);
            this.program.laProgramProperties.fsInequal = dfs;

            args[0] = tZero;
            args[1] = tZero;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tFalse);
            this.program.addRule(dfs, r);

            args[0] = tSuccX;
            args[1] = tZero;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tTrue);
            this.program.addRule(dfs, r);

            args[0] = tZero;
            args[1] = tSuccY;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tTrue);
            this.program.addRule(dfs, r);

            args[0] = tSuccX;
            args[1] = tSuccY;
            lhs = DefFunctionApp.create(dfs, args);
            args[0] = vX;
            args[1] = vY;
            rhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, rhs);
            this.program.addRule(dfs, r);

            // plus
            functionName = "plus";

            if(this.definedFunctSymb.contains(functionName)){
                ParseError pe = new ParseError();
                pe.setMessage("Name clash: " + functionName + " is a resevered function name.");
                this.parseErrors.add(pe);
            }
            this.reservedNames.add(functionName);

            argSorts = new Vector<Sort>();
            argSorts.add(this.natSort);
            argSorts.add(this.natSort);

            dfs = DefFunctionSymbol.create(functionName, argSorts, this.natSort);
            dfs.setTermination(true); // by construction
            this.definedFunctSymb.add(functionName);
            this.defFunc.put(functionName, dfs);
            this.program.addPredefFunctionSymbol(dfs);
            this.program.laProgramProperties.fsPlus = dfs;

            args[0] = tZero;
            args[1] = vY;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, vY);
            this.program.addRule(dfs, r);

            args[0] = tSuccX;
            args[1] = vY;
            lhs = DefFunctionApp.create(dfs, args);
            args[0] = vX;
            args[1] = vY;
            rhs = DefFunctionApp.create(dfs, args);
            args1[0] = rhs;
            rhs = ConstructorApp.create(csSucc, args1);
            r = Rule.create(lhs, rhs);
            this.program.addRule(dfs, r);

            /*
             * lesseq
             */
            functionName = "lesseq";

            if(this.definedFunctSymb.contains(functionName)){
                ParseError pe = new ParseError();
                pe.setMessage("Name clash: " + functionName + " is a resevered function name.");
                this.parseErrors.add(pe);
            }
            this.reservedNames.add(functionName);

            argSorts = new Vector<Sort>();
            argSorts.add(this.natSort);
            argSorts.add(this.natSort);

            dfs = DefFunctionSymbol.create(functionName, argSorts, this.boolSort);
            dfs.setTermination(true); // by construction
            this.definedFunctSymb.add(functionName);
            this.defFunc.put(functionName, dfs);
            this.program.addPredefFunctionSymbol(dfs);
            this.program.laProgramProperties.fsLesseq = dfs;

            args[0] = tZero;
            args[1] = vY;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tTrue);
            this.program.addRule(dfs, r);

            args[0] = tSuccX;
            args[1] = tZero;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tFalse);
            this.program.addRule(dfs, r);

            args[0] = tSuccX;
            args[1] = tSuccY;
            lhs = DefFunctionApp.create(dfs, args);
            args[0] = vX;
            args[1] = vY;
            rhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, rhs);
            this.program.addRule(dfs, r);

            /*
             * less
             */
            functionName = "less";

            if(this.definedFunctSymb.contains(functionName)){
                ParseError pe = new ParseError();
                pe.setMessage("Name clash: " + functionName + " is a resevered function name.");
                this.parseErrors.add(pe);
            }
            this.reservedNames.add(functionName);

            argSorts = new Vector<Sort>();
            argSorts.add(this.natSort);
            argSorts.add(this.natSort);

            dfs = DefFunctionSymbol.create(functionName, argSorts, this.boolSort);
            dfs.setTermination(true); // by construction
            this.definedFunctSymb.add(functionName);
            this.defFunc.put(functionName, dfs);
            this.program.addPredefFunctionSymbol(dfs);
            this.program.laProgramProperties.fsLess = dfs;

            args[0] = vX;
            args[1] = tZero;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tFalse);
            this.program.addRule(dfs, r);

            args[0] = tZero;
            args[1] = tSuccY;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tTrue);
            this.program.addRule(dfs, r);

            args[0] = tSuccX;
            args[1] = tSuccY;
            lhs = DefFunctionApp.create(dfs, args);
            args[0] = vX;
            args[1] = vY;
            rhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, rhs);
            this.program.addRule(dfs, r);

            /*
             *  greater
             */
            functionName = "greater";

            if(this.definedFunctSymb.contains(functionName)){
                ParseError pe = new ParseError();
                pe.setMessage("Name clash: " + functionName + " is a resevered function name.");
                this.parseErrors.add(pe);
            }
            this.reservedNames.add(functionName);

            argSorts = new Vector<Sort>();
            argSorts.add(this.natSort);
            argSorts.add(this.natSort);

            dfs = DefFunctionSymbol.create(functionName, argSorts, this.boolSort);
            dfs.setTermination(true); // by construction
            this.definedFunctSymb.add(functionName);
            this.defFunc.put(functionName, dfs);
            this.program.addPredefFunctionSymbol(dfs);
            this.program.laProgramProperties.fsGreater = dfs;

            args[0] = tZero;
            args[1] = vY;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tFalse);
            this.program.addRule(dfs, r);

            args[0] = tSuccX;
            args[1] = tZero;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tTrue);
            this.program.addRule(dfs, r);

            args[0] = tSuccX;
            args[1] = tSuccY;
            lhs = DefFunctionApp.create(dfs, args);
            args[0] = vX;
            args[1] = vY;
            rhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, rhs);
            this.program.addRule(dfs, r);

            /*
             * greatereq
             */
            functionName = "greatereq";

            if(this.definedFunctSymb.contains(functionName)){
                ParseError pe = new ParseError();
                pe.setMessage("Name clash: " + functionName + " is a resevered function name.");
                this.parseErrors.add(pe);
            }
            this.reservedNames.add(functionName);

            argSorts = new Vector<Sort>();
            argSorts.add(this.natSort);
            argSorts.add(this.natSort);

            dfs = DefFunctionSymbol.create(functionName, argSorts, this.boolSort);
            dfs.setTermination(true); // by construction
            this.definedFunctSymb.add(functionName);
            this.defFunc.put(functionName, dfs);
            this.program.addPredefFunctionSymbol(dfs);
            this.program.laProgramProperties.fsGreatereq = dfs;

            args[0] = vX;
            args[1] = tZero;
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tTrue);
            this.program.addRule(dfs, r);

            args[0] = tZero;
            args1[0] = vY;
            args[1] = ConstructorApp.create(csSucc, args1);
            lhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, this.tFalse);
            this.program.addRule(dfs, r);

            args[0] = tSuccX;
            args[1] = tSuccY;
            lhs = DefFunctionApp.create(dfs, args);
            args[0] = vX;
            args[1] = vY;
            rhs = DefFunctionApp.create(dfs, args);
            r = Rule.create(lhs, rhs);
            this.program.addRule(dfs, r);

        }
        catch (ProgramException programException) {
            programException.getMessage();
            ParseError pe = new ParseError();
            pe.setMessage(programException.getMessage());
            this.parseErrors.add(pe);
        }

    }

    public ParseErrors getErrors() {
        return this.parseErrors;
    }

    @Override
    public void outASortdecl(ASortdecl node) {
        TSortIdent tSortIdent = node.getSortIdent();
        String sSort = tSortIdent.getText();
        this.declaredSorts.push(sSort);
    }

    @Override
    public void outAFuncdecl(AFuncdecl node) {
        TPrefixIdent tPrefixIdent = node.getPrefixIdent();
        String name = tPrefixIdent.getText();

        TSortIdent tSortIdent = node.getSortIdent();
        String sSort = tSortIdent.getText();

        if(this.reservedNames.contains(name)){
            ParseError pe = new ParseError();
            pe.setMessage("Name clash: " + name + " is a resevered function name.");
            this.parseErrors.add(pe);
        }

        // check if a used sort in a function declaration
        // has been declared
        if (!this.declaredSorts.contains(sSort)) {
            ParseError pe = new ParseError();
            pe.setMessage("Sort " + sSort + " has not been declared");
            this.parseErrors.add(pe);
        }

        try {
            if (this.definedFunctSymb.contains(name)) {
                // it is a defined function symbol

                Sort sort = this.sorts.get(sSort);

                DefFunctionSymbol dfs = DefFunctionSymbol.create(name,
                        this.funcArgSorts, sort);

                this.defFunc.put(name, dfs);
                this.program.addDefFunctionSymbol(dfs);

            }
            else {
                // it is a constructor symbol

                Sort sort = this.sorts.get(sSort);
                DefFunctionSymbol feq;

                if (sort == null) {
                    sort = Sort.create(sSort);

                    // create the equality test function symbol
                    String feqName = "equal_"+sSort;
                    Vector<Sort> argSorts = new Vector<Sort>();
                    argSorts.add(sort);
                    argSorts.add(sort);
                    feq = DefFunctionSymbol.create(feqName, argSorts, this.boolSort);
                    sort.setEqualOp(feq);
                    feq.setTermination(true); // by construction

                    try {
                        this.program.addPredefFunctionSymbol(feq);
                        feq.setSignatureClass(Symbol.BOOLSIG);
                    }
                    catch (ProgramException e) {
                        ParseError pe = new ParseError();
                        pe.setMessage("cannot create equality test '" + feqName + "' for sort '" + sSort);
                        this.parseErrors.add(pe);
                    }

                    this.sorts.put(sSort, sort);
                    this.program.addSort(sort);

                }
                else{
                    feq = sort.getEqualOp();
                }

                ConstructorSymbol cs = ConstructorSymbol.create(name,
                        this.funcArgSorts, sort);


                // create the equality rules

                VariableSymbol vsX = VariableSymbol.create("X");
                AlgebraVariable varX = AlgebraVariable.create(vsX);
                VariableSymbol vsY = VariableSymbol.create("Y");
                AlgebraVariable varY = AlgebraVariable.create(vsY);
                Set<AlgebraVariable> vars =  new HashSet<AlgebraVariable>();
                vars.add(varX);
                vars.add(varY);
                FreshVarGenerator fvg = new FreshVarGenerator(vars);

                int arity = this.funcArgSorts.size();

                AlgebraTerm[] argsX = new AlgebraTerm[arity];
                AlgebraTerm[] argsY = new AlgebraTerm[arity];

                for(int i=0; i<arity;i++){
                    Sort argS = this.funcArgSorts.get(i);

                    AlgebraVariable vx = fvg.getFreshVariable(varX, false);
                    vx.getVariableSymbol().setSort(argS);
                    argsX[i]=vx;

                    AlgebraVariable vy = fvg.getFreshVariable(varY, false);
                    vy.getVariableSymbol().setSort(argS);
                    argsY[i]=vy;
                }
                AlgebraTerm tConsX = ConstructorApp.create(cs, argsX);
                AlgebraTerm tConsY = ConstructorApp.create(cs, argsY);

                AlgebraTerm[] args = new AlgebraTerm[2];
                args[0] = tConsX;
                args[1] = tConsY;
                AlgebraTerm lhs = DefFunctionApp.create(feq, args);
                Rule r;
                AlgebraTerm rhs;
                if(arity==0){
                    rhs = this.tTrue;
                }
                else{
                    args = new AlgebraTerm[2];
                    args[0] = argsX[0];
                    args[1] = argsY[0];

                    rhs = DefFunctionApp.create(feq, args);

                    for(int i=1; i<arity;i++){
                        args = new AlgebraTerm[2];
                        args[0] = argsX[i];
                        args[1] = argsY[i];

                        AlgebraTerm t = DefFunctionApp.create(feq, args);

                        AlgebraTerm argsAnd[] = new AlgebraTerm[2];
                        argsAnd[0] = rhs;
                        argsAnd[1] = t;

                        rhs = DefFunctionApp.create(this.fAnd, argsAnd);
                    }

                }

                r = Rule.create(lhs, rhs);
                this.program.addRule(feq, r);

                // create the inequality rules

                for (ConstructorSymbol other_cs : sort.getConstructorSymbols()) {

                    Set<AlgebraVariable> other_vars =  new HashSet<AlgebraVariable>();
                    vars.add(varY);
                    FreshVarGenerator other_fvg = new FreshVarGenerator(other_vars);

                    int other_arity = other_cs.getArity();

                    AlgebraTerm[] other_argsY = new AlgebraTerm[other_arity];

                    for(int i=0; i<other_arity;i++){
                        Sort argS = other_cs.getArgSort(i);

                        AlgebraVariable vy = other_fvg.getFreshVariable(varY, false);
                        vy.getVariableSymbol().setSort(argS);
                        other_argsY[i]=vy;
                    }
                    AlgebraTerm tConsY_other = ConstructorApp.create(other_cs, other_argsY);

                    args = new AlgebraTerm[2];
                    args[0] = tConsX;
                    args[1] = tConsY_other;

                    lhs = DefFunctionApp.create(feq, args);
                    r = Rule.create(lhs, this.tFalse);
                    this.program.addRule(feq, r);

                    args = new AlgebraTerm[2];
                    args[0] = tConsY_other;
                    args[1] = tConsX;

                    lhs = DefFunctionApp.create(feq, args);
                    r = Rule.create(lhs, this.tFalse);
                    this.program.addRule(feq, r);
                }


                this.constructors.put(name, cs);
                sort.addConstructorSymbol(cs);
                this.program.addConstructorSymbol(cs);

            }
        }
        catch (ProgramException programException) {
            programException.getMessage();
            ParseError pe = new ParseError();
            pe.setMessage(programException.getMessage());
            this.parseErrors.add(pe);
        }

        this.funcArgSorts = new LinkedList<Sort>();

    }

    @Override
    public void outASorts(ASorts node) {
        TSortIdent tSortIdent = node.getSortIdent();
        String sSort = tSortIdent.getText();

        // check if a used sort in a function declaration
        // has been declared
        if (!this.declaredSorts.contains(sSort)) {
            ParseError pe = new ParseError();
            pe.setMessage("Sort " + sSort + " has not been declared.");
            this.parseErrors.add(pe);
        }

        Sort argsort = this.sorts.get(sSort);

        if (argsort == null) {
            ParseError pe = new ParseError();
            pe.setMessage("Sort " + sSort + " has not (yet) any constructors.");
            this.parseErrors.add(pe);
        }

        this.funcArgSorts.add(argsort);
    }

    @Override
    public void outASortcomma(ASortcomma node) {
        TSortIdent tSortIdent = node.getSortIdent();
        String sSort = tSortIdent.getText();

        // check if a used sort in a function declaration
        // has been declared
        if (!this.declaredSorts.contains(sSort)) {
            ParseError pe = new ParseError();
            pe.setMessage("Sort " + sSort + " has not been declared");
            this.parseErrors.add(pe);
        }

        Sort argsort = this.sorts.get(sSort);
        this.funcArgSorts.add(argsort);
    }

    @Override
    public void inARuledecl(ARuledecl node) {
        // null because we do not know the sorts yet
        // we will check that later
        this.expectedTermSorts.push(null);
        this.expectedTermSorts.push(null);
        if (FullPass.DEBUB_STACK) {
            System.err.println("push");
            System.err.println("push");
        }
    }

    @Override
    public void outARuledecl(ARuledecl node) {
        AlgebraTerm right;
        AlgebraTerm left;

        right = this.termStack.pop();
        left = this.termStack.pop();

        Sort rSort = right.getSort();
        Sort lSort = left.getSort();

        if (rSort == null) {
            // because it is a variable
            // then set the sort of the lhs
            right.getSymbol().setSort(lSort);
        }
        else if (!rSort.equals(lSort)) {
            ParseError pe = new ParseError(ParseError.ERROR);
            pe.setMessage("The sort of the rhs " + rSort
                    + " is not the Sort of the lhs " + lSort + ".");
            this.parseErrors.add(pe);
        }

        Stack<Rule> conditions = new Stack<Rule>();

        List<AlgebraTerm> condTerms;
        if (node.getConditional() != null) {
            condTerms = this.termStack.popDownToMark();

            for (int i = 0; i < condTerms.size(); i += 2) {
                AlgebraTerm s = condTerms.get(i);
                AlgebraTerm t = condTerms.get(i + 1);

                if(s == null){
                    // the error has occured before
                    continue;
                }

                if(! t.isConstructorGroundTerm()){
                    ParseError pe = new ParseError();
                    pe.setMessage("The rhs " + t + " of the condition " + s + " -> " + t
                            + " is not a constructor ground term.");
                    this.parseErrors.add(pe);
                }

                Sort tSort = t.getSort();

                if (tSort == null) {
                    // because it is a variable
                    // then set the sort of the lhs
                    t.getSymbol().setSort(lSort);
                }
                else if (s==null){
                    // an error has occured before
                }
                else if (!tSort.equals(s.getSort())) {
                    // not allowed -> exit with error
                    ParseError pe = new ParseError();
                    pe.setMessage("The condition " + s + " -> " + t
                            + " has not an identical sort.");
                    this.parseErrors.add(pe);
                }

                Rule c = Rule.create(s, t);
                conditions.push(c);
            }

        }

        Rule r = Rule.create(conditions, left, right);
        if (this.variableCheck(r)) {
            this.program.addRule(r);
        }

//        System.err.println(r);
        this.expectedTermSorts.clear();
        if (FullPass.DEBUB_STACK) {
            System.err.println("clear");
        }
    }

    @Override
    public void inAConditional(AConditional node) {
        this.termStack.pushMark();
    }

    @Override
    public void inACond(ACond node) {
        // null because we do not know the sorts yet
        // we will check that later
        this.expectedTermSorts.push(null);
        this.expectedTermSorts.push(null);
        if (FullPass.DEBUB_STACK) {
            System.err.println("push");
            System.err.println("push");
        }
    }

    @Override
    public void outAVarTerm(AVarTerm node) {
        String name = node.getVarIdent().getText();

        Sort s;
        if(this.expectedTermSorts.isEmpty()){
            s=null;
            ParseError pe = new ParseError(ParseError.ERROR);
            pe.setMessage("Sort for variable " + name + " is not clear.");
            this.parseErrors.add(pe);
        }
        else{
            s = this.expectedTermSorts.pop();
        }

        if (FullPass.DEBUB_STACK) {
            System.err.println("pop " + s);
        }

        VariableSymbol vs = VariableSymbol.create(name, s);
        AlgebraVariable var = AlgebraVariable.create(vs);

        this.termStack.push(var);
    }

    @Override
    public void outAConst0Term(AConst0Term node) {
        String name = node.getPrefixIdent().getText();

        Sort s;
        if(this.expectedTermSorts.isEmpty()){
            s=null;
            ParseError pe = new ParseError(ParseError.ERROR);
            pe.setMessage("Sort for construcor" + name + " is not clear.");
            this.parseErrors.add(pe);
        }
        else{
            s = this.expectedTermSorts.pop();
        }

        if (FullPass.DEBUB_STACK) {
            System.err.println("pop " + s);
        }

        ConstructorSymbol cs = this.constructors.get(name);
        if (cs == null) {
            ParseError pe = new ParseError(ParseError.ERROR);
            pe.setMessage("Constructor " + name + " has not been declared.");
            this.parseErrors.add(pe);
            this.termStack.push(null);
            return;
        }

        ConstructorApp ca = ConstructorApp.create(cs);
        this.termStack.push(ca);

        Sort caS = ca.getSort();
        if (s != null && !s.equals(caS)) {
            ParseError pe = new ParseError(ParseError.ERROR);
            pe.setMessage("The sort " + caS + " of the constructor" + cs
                    + " is not the expected Sort " + s + ".");
            this.parseErrors.add(pe);
        }
    }

    @Override
    public void inAConstFuncTerm(AConstFuncTerm node) {
        this.termStack.pushMark();

        String name = node.getPrefixIdent().getText();

        DefFunctionSymbol dfs = this.defFunc.get(name);
        if (dfs != null) {
            List<Sort> sorts = dfs.getArgSorts();
            for (int i = sorts.size() - 1; i >= 0; i--) {
                Sort s = sorts.get(i);
                this.expectedTermSorts.push(s);
                if (FullPass.DEBUB_STACK) {
                    System.err.println("push " + s);
                }
            }
        }
        else {
            ConstructorSymbol cs = this.constructors.get(name);
            if (cs == null){
                ParseError pe = new ParseError(ParseError.ERROR);
                pe.setMessage("The constructor symbol " + name + " has not been declared.");
                this.parseErrors.add(pe);
                this.expectedTermSorts.push(null);
                return;
            }
            List<Sort> sorts = cs.getArgSorts();
            for (int i = sorts.size() - 1; i >= 0; i--) {
                Sort s = sorts.get(i);
                this.expectedTermSorts.push(s);
                if (FullPass.DEBUB_STACK) {
                    System.err.println("push " + s);
                }
            }
        }
    }

    @Override
    public void outAConstFuncTerm(AConstFuncTerm node) {
        List<AlgebraTerm> arguments = this.termStack.popDownToMark();

        String name = node.getPrefixIdent().getText();

        Sort s = this.expectedTermSorts.pop();
        if (FullPass.DEBUB_STACK) {
            System.err.println("pop " + s);
        }

        DefFunctionSymbol dfs = this.defFunc.get(name);
        if (dfs != null) {
            DefFunctionApp dfa = DefFunctionApp.create(dfs, arguments);
            this.termStack.push(dfa);

            Sort dfaS = dfa.getSort();
            if (s != null && !s.equals(dfaS)) {
                ParseError pe = new ParseError(ParseError.ERROR);
                pe.setMessage("The sort " + dfaS
                        + " of the functions application " + dfs
                        + " is not the expected Sort " + s + ".");
                this.parseErrors.add(pe);
            }
        }
        else {
            ConstructorSymbol cs = this.constructors.get(name);
            if (cs == null){
                ParseError pe = new ParseError(ParseError.ERROR);
                pe.setMessage("The constructor symbol " + name + " has not been declared.");
                this.parseErrors.add(pe);
                this.termStack.push(null);
                return;
            }
            ConstructorApp ca = ConstructorApp.create(cs, arguments);
            this.termStack.push(ca);

            Sort caS = ca.getSort();
            if (s != null && !s.equals(caS)) {
                ParseError pe = new ParseError(ParseError.ERROR);
                pe.setMessage("The sort " + caS + " of the constructor " + cs
                        + " is not the expected Sort " + s + ".");
                this.parseErrors.add(pe);
            }
        }
    }

    private boolean variableCheck(Rule rule) {

        AlgebraTerm lhs = rule.getLeft();
        AlgebraTerm rhs = rule.getRight();

        // the lhs must not be a variable
        if (lhs instanceof AlgebraVariable) {
            ParseError pe = new ParseError(
                    ParseError.VARIABLE_CONDITION_VIOLATED);
            pe.setMessage("The lhs of the rule " + rule + " is a variable.");
            this.parseErrors.add(pe);
            return false;
        }

        Set<AlgebraVariable> lhsVars = lhs.getVars();
        Set<AlgebraVariable> rhsVars = rhs.getVars();

        // check if every variable on the rhs is contained in the lhs
        for (AlgebraVariable vRhs : rhsVars) {
            if (!lhsVars.contains(vRhs)) {
                // not allowed -> exit with error
                ParseError pe = new ParseError(
                        ParseError.VARIABLE_CONDITION_VIOLATED);
                pe.setMessage("The rhs of the rule " + rule
                        + " contains the variable " + vRhs
                        + " which does not occur on the lhs.");
                this.parseErrors.add(pe);
                return false;
            }
        }

        // check if every variable in lhs of a condition is contained in the lhs
        List<Rule> conds = rule.getConds();
        for (Rule cond : conds) {
            AlgebraTerm s = cond.getLeft();
            Set<AlgebraVariable> sVars = s.getVars();
            for (AlgebraVariable vS : sVars) {
                if (!lhsVars.contains(vS)) {
                    // not allowed -> exit with error
                    ParseError pe = new ParseError(
                            ParseError.VARIABLE_CONDITION_VIOLATED);
                    pe.setMessage("The condition " + cond + " of the rule "
                            + rule + " contains the variable " + vS
                            + " which does not occur on the lhs.");
                    this.parseErrors.add(pe);
                    return false;
                }
            }

        }

        return true;
    }

    public Program getProgram() {
        return this.program;
    }
}
