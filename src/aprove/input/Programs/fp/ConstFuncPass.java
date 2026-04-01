package aprove.input.Programs.fp;

import java.math.*;
import java.util.*;

import aprove.input.Generated.fp.node.*;
import aprove.input.Programs.Predef.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class ConstFuncPass extends Pass {

    // keeping track of what has already been defined
    private HashMap<String, Set<Pair<List<String>,String>>> funcSymSorts;

    private List<String> curArgSortsNames;
    private String curSortName;
    private TId curSelSortToken;
    private int curOpFixity;
    private Set<String> overriddenPrecedences;

    @Override
    public void caseAInfixDecl(AInfixDecl node) {
        node.getInfixdef().apply(this);
    }

    @Override
    public void inStart(Start node) {
        this.consSymCounts = new HashMap<String, Integer>();
        this.consSymSignatures = new HashMap<String, Set<Pair<String,List<String>>>>();
        this.funcSymCounts = new HashMap<String, Integer>();
        this.funcSymSorts = new HashMap<String, Set<Pair<List<String>,String>>>();
        this.operatorFixity = new HashMap<String, Pair<Integer,Integer>>();
        this.overriddenPrecedences = new HashSet<String>();
        this.addPredefs();
    }


    @Override
    public void outStart(Start node) {
        this.funcSymSignatureFixed = new HashMap<String, Pair<Set<Pair<List<String>,String>>,BigInteger>>();
        // determining what argument sorts are always the same for a function
        for(Map.Entry<String, Set<Pair<List<String>,String>>> mapEntry : this.funcSymSorts.entrySet()) {

            if (aprove.Globals.useAssertions) {
                assert mapEntry.getValue().size() > 0 : "function \""+mapEntry.getKey()+"\" is marked as overloaded, but no argument list was found.";
            }

            Set<Pair<List<String>,String>> funcSymSigs = mapEntry.getValue();
            List<String> someArgList = funcSymSigs.iterator().next().x;
            int numArgs = someArgList.size();
            BigInteger fixedArgs = BigInteger.ONE.shiftLeft(numArgs).subtract(BigInteger.ONE);
            for(Pair<List<String>,String> funcSymSig : funcSymSigs) {
                for(int i=0; i<numArgs; ++i) {
                    if(!someArgList.get(i).equals(funcSymSig.x.get(i))) {
                        fixedArgs = fixedArgs.clearBit(i);
                    }
                }
            }
            this.funcSymSignatureFixed.put(mapEntry.getKey(), new Pair<Set<Pair<List<String>,String>>,BigInteger>(funcSymSigs,fixedArgs));
        }

        // checking if every constructor marked as overloaded has at least one sort it is defined for
        if (aprove.Globals.useAssertions) {
            for(Map.Entry<String, Set<Pair<String,List<String>>>> mapEntry : this.consSymSignatures.entrySet()) {
                assert mapEntry.getValue().size() > 0 : "constructor \""+mapEntry.getKey()+"\" is marked as overloaded, but no return sort was found.";
            }
        }
    }


    private void addPredefs() {
        for (ConstructorSymbol consSym : PredefDataStructureSymbols.getPredefinedConstructorSymbols()) {
            this.consSymCounts.put(consSym.getName(), Integer.valueOf(1));
            Set<Pair<String,List<String>>> consSymRet2ArgSortNames = new HashSet<Pair<String,List<String>>>();
            List<String> consSymArgSortsNames = new Vector<String>();
            for(Sort argSort : consSym.getArgSorts()) {
                consSymArgSortsNames.add(argSort.getName());
            }
            consSymRet2ArgSortNames.add(new Pair<String,List<String>>(consSym.getSort().getName(), consSymArgSortsNames));
            this.consSymSignatures.put(consSym.getName(), consSymRet2ArgSortNames);
        }

        Map<String, Pair<List<String>,String>> predefFuncsSigs = PredefFunctionSymbols.getPredefinedFunctionsSorts();
        for(Map.Entry<String, Pair<List<String>,String>> e : predefFuncsSigs.entrySet()) {
            String funcName = e.getKey();
            this.funcSymCounts.put(funcName, Integer.valueOf(1));
            Set<Pair<List<String>,String>> argSortsNames = new HashSet<Pair<List<String>,String>>();
            argSortsNames.add(e.getValue());
            this.funcSymSorts.put(funcName, argSortsNames);
            if (PredefFunctionSymbols.getPrecedence(funcName) != null) {
                this.operatorFixity.put(funcName, PredefFunctionSymbols.getFixityAndPrecedence(funcName));
            }
        }
    }


    // test whether the passed return sort name never occured before
    private boolean isNewConsSymRetSort(String consName, String retSortName) {
        for(Pair<String, List<String>> ret2Args : this.consSymSignatures.get(consName)) {
            if (retSortName.equals(ret2Args.x)) {
                return false;
            }
        }
        return true;
    }

    private void addConsSymbol(Token t, List<String> argSortsNames, String retSortName) {
        String consSymName = this.chop(t);
        Integer i = this.consSymCounts.get(consSymName);
        Set<Pair<String,List<String>>> ret2ArgSorts;
        if (i == null) {
            this.consSymCounts.put(consSymName, 1);
            ret2ArgSorts = new HashSet<Pair<String,List<String>>>();
            this.consSymSignatures.put(consSymName, ret2ArgSorts);
        }
        else {
            this.consSymCounts.put(consSymName, i.intValue()+1);
            ret2ArgSorts = this.consSymSignatures.get(consSymName);
        }
        if (!this.isNewConsSymRetSort(consSymName, retSortName)) {
            this.addParseError(t, "A constructor ''"+consSymName+"'' for sort ''"+retSortName+"'' has already been defined.");
        }
        ret2ArgSorts.add(new Pair<String,List<String>>(retSortName, argSortsNames));
    }


    // test whether the passed argument sorts names never occured before
    private boolean isNewFuncSymbolArgsList(String functName, List<String> argSortsNames) {
        for(Pair<List<String>,String> funcSig : this.funcSymSorts.get(functName)) {
            if (funcSig.x.equals(argSortsNames)) {
                return false;
            }
        }
        return true;
    }

    private void addFuncSymbol(Token funcNameToken, Token retSortNameToken) {
        String funcSymName = this.chop(funcNameToken);
        String retSortName = this.chop(retSortNameToken);
        Integer i = this.funcSymCounts.get(funcSymName);
        Set<Pair<List<String>,String>> funcSymSigs;
        if (i ==  null) {
            this.funcSymCounts.put(funcSymName, 1);
            funcSymSigs = new HashSet<Pair<List<String>,String>>();
            this.funcSymSorts.put(funcSymName, funcSymSigs);
        }
        else {
            this.funcSymCounts.put(funcSymName, i.intValue()+1);
            funcSymSigs = this.funcSymSorts.get(funcSymName);
        }
        if (!this.isNewFuncSymbolArgsList(funcSymName, this.curArgSortsNames)) {
            this.addParseError(funcNameToken, "A function with these parameters has already been defined.");
        }
        funcSymSigs.add(new Pair<List<String>,String>(this.curArgSortsNames, retSortName));
    }


    @Override
    public void inAFunct(AFunct node) {
        this.curArgSortsNames = new Vector<String>();
    }

    @Override
    public void inAOpdef(AOpdef node) {
        this.curArgSortsNames = new Vector<String>();
    }


    @Override
    public void inAIdcomma(AIdcomma node) {
        String argSortName = this.chop(node.getId());
        this.curArgSortsNames.add(argSortName);
    }

    @Override
    public void outAIdlist(AIdlist node) {
        String argSortName = this.chop(node.getId());
        this.curArgSortsNames.add(argSortName);
    }


    @Override
    public void outAFunct(AFunct node) {
        String functName = this.chop(node.getFunctname());
        this.addFuncSymbol(node.getFunctname(), node.getReturn());
    }

    @Override
    public void outAOpdef(AOpdef node) {
        String opName = this.chop(node.getOpname());
        this.addFuncSymbol(node.getOpname(), node.getReturn());
        this.infixPrecedence(node.getOpname(), node.getOptions());
    }


    private void infixPrecedence(Token infixTok, POptions options) {
        String opName = this.chop(infixTok);
        Triple<Integer,Integer,Boolean> fixityAndPrecedenceAndDefaults = Pass2.readOptions(infixTok, options, null, this);
        Pair<Integer,Integer> prevOpFixityAndPrecedence = this.operatorFixity.get(opName);
        if ( (prevOpFixityAndPrecedence != null) && (!fixityAndPrecedenceAndDefaults.z) ) {
            if (!prevOpFixityAndPrecedence.x.equals(fixityAndPrecedenceAndDefaults.x)) {
                this.addParseError(infixTok, "An operator with this name is already defined with a different fixity.");
            }
            if (!prevOpFixityAndPrecedence.y.equals(fixityAndPrecedenceAndDefaults.y)) {
                this.addParseError(infixTok, "An operator with this name is already defined with precedence "+prevOpFixityAndPrecedence.y+".");
            }
        } else {
            if (prevOpFixityAndPrecedence == null) {
                Pair<Integer,Integer> fixityAndPrecedence = new Pair<Integer,Integer>(fixityAndPrecedenceAndDefaults.x, fixityAndPrecedenceAndDefaults.y);
                this.operatorFixity.put(opName, fixityAndPrecedence);
            }
        }
    }



    @Override
    public void inAConstr(AConstr node) {
        this.curSortName = this.chop(node.getReturn());
        this.curArgSortsNames = new Vector<String>();
    }

    @Override
    public void inAInfixconstr(AInfixconstr node) {
        this.curSortName = this.chop(node.getReturn());
        this.curArgSortsNames = new Vector<String>();
        this.infixPrecedence(node.getCons(), node.getOptions());
    }


    @Override
    public void inASelidcomma(ASelidcomma node) {
        String argSortName = this.chop(node.getSort());
        this.curArgSortsNames.add(argSortName);
        this.curSelSortToken = node.getSort();
    }

    @Override
    public void caseASelidlist(ASelidlist node) {
        for(Object selidcommaNode : node.getSelidcomma()) {
            ((PSelidcomma)selidcommaNode).apply(this);
        }
        String argSortName = this.chop(node.getSort());
        this.curArgSortsNames.add(argSortName);
        this.curSelSortToken = node.getSort();
        if (node.getSelector() != null) {
            node.getSelector().apply(this);
        }
    }


    @Override
    public void outASelector(ASelector node) {
        List<String> backupCurArgSortNames = this.curArgSortsNames;
        this.curArgSortsNames = Arrays.asList(this.curSortName);
        this.addFuncSymbol(node.getName(), this.curSelSortToken);
        this.curArgSortsNames = backupCurArgSortNames;
    }


    @Override
    public void outAConstr(AConstr node) {
        Token tcons = null;
        Node n = node.getCons();
        if (n instanceof ANoappEid) {
            tcons = ((ANoappEid)n).getNoappid();
        }
        else {
            tcons = ((AAppEid)n).getId();
        }
        String retSortName = this.chop(node.getReturn());
        this.addConsSymbol(tcons, this.curArgSortsNames, retSortName);
    }


    @Override
    public void outAInfixconstr(AInfixconstr node) {
        String retSortName = this.chop(node.getReturn());
        this.addConsSymbol(node.getCons(), this.curArgSortsNames, retSortName);
    }


    @Override
    public void inAStruct(AStruct node) {
        String sortName = this.chop(node.getStructname());
        List<String> backupCurArgSortNames = this.curArgSortsNames;
        this.curArgSortsNames = Arrays.asList(sortName, sortName);
        this.addFuncSymbol(new TId("==", node.getStructname().getLine(), node.getStructname().getPos()), new TId("bool"));
        this.curArgSortsNames = backupCurArgSortNames;
    }


    @Override
    public void caseAInfixdef(AInfixdef node) {
        node.getInfixity().apply(this);
        String opName = this.chop(node.getOpname());
        if (this.overriddenPrecedences.contains(opName)) {
            this.addParseError(node.getOpname(), "For this operator a precedence was already defined.");
        }
        else {
            Token id;
            Node eid = node.getEid();
            if (eid instanceof AAppEid) {
                id = ((AAppEid)eid).getId();
            }
            else {
                id = ((ANoappEid)eid).getNoappid();
            }
            try {
                Integer precedence = Integer.parseInt(this.chop(id));
                this.operatorFixity.put(opName, new Pair<Integer,Integer>(this.curOpFixity, precedence));
                this.overriddenPrecedences.add(opName);
            }
            catch (NumberFormatException e) {
                this.addParseError(id, "could not read this number");
            }
        }
    }

    public void caseAInfixNoInfixity(ANoInfixity node) {
        this.curOpFixity = SyntacticFunctionSymbol.INFIX;
    }

    @Override
    public void caseALInfixity(ALInfixity node) {
        this.curOpFixity = SyntacticFunctionSymbol.INFIXL;
    }

    @Override
    public void caseARInfixity(ARInfixity node) {
        this.curOpFixity = SyntacticFunctionSymbol.INFIXR;
    }
}
