package aprove.input.Programs.fp;

import java.math.*;
import java.util.*;

import aprove.input.Generated.fp.node.*;
import aprove.input.Programs.Predef.IntegerPredef.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class RenameConstFuncPass extends Pass {

    private List<String> curArgSortsNames;
    private String curRetSortName;
    private String oldFunctName;
    private String newFunctName;
    private boolean isLHS;
    private boolean isLHSOpRoot;
    private String intSortName;
    private String curSelectorSortName;

    private Stack<Set<String>> possibleSortsStack;
    private Stack<List<Set<String>>> functArgsSortsStack;
    private Map<String, Stack<String>> varSort;
    private Stack<Set<String>> letVarsStack;

    // just initialization
    @Override
    public void inStart(Start node) {
        this.possibleSortsStack = new Stack<Set<String>>();
        this.functArgsSortsStack = new Stack<List<Set<String>>>();
        this.varSort = new HashMap<String, Stack<String>>();
        this.letVarsStack = new Stack<Set<String>>();
        this.intSortName = AbstractIntegerPredefItem.getIntTypeName();
        this.isLHSOpRoot = false;
    }



    /** helper, pushes a single sort name onto the stack of possible sorts
     * for this purpose a new set is created containing only this name
     * @param sortName name of the sort to push onto the stack of expected sorts
     */
    private void pushSingleSort(String sortName) {
        Set<String> newSortNames = new HashSet<String>();
        newSortNames.add(sortName);
        this.possibleSortsStack.push(newSortNames);
    }


    /** helper, pushes the passed single sort names in reverse order
     */
    private void pushSortNamesInRevOrder(List<String> sortNames) {
        String[] sortNamesArr = sortNames.toArray(new String[0]);
        for(int i=sortNamesArr.length-1; i>=0; --i) {
            this.pushSingleSort(sortNamesArr[i]);
        }
    }

    /** helper, pushes the passes possible sort names in reverse order
     */
    private void pushPossibleSortNamesInRevOrder(List<Set<String>> possibleSortNames) {
        for(int i=possibleSortNames.size()-1; i>=0; --i) {
            this.possibleSortsStack.push(possibleSortNames.get(i));
        }
    }


    /** pushes the possible sorts of the overloaded function named functName onto the stack
     * this is done in reverse order, so that processing of the arguments must be done in the correct order
     * @param functName name of the overloaded function
     * @return number of arguments the specified function has
     */
    private int pushPossibleSorts(String functName) {
        Pair<Set<Pair<List<String>,String>>,BigInteger> funcSigsAndFixedArgs = this.funcSymSignatureFixed.get(functName);
        List<String> someArgList = funcSigsAndFixedArgs.x.iterator().next().x;
        int numArgs = someArgList.size();
        for(int i=numArgs-1; i>=0; --i) {
            if (funcSigsAndFixedArgs.y.testBit(i)) {
                this.pushSingleSort(someArgList.get(i));
            }
            else {
                this.possibleSortsStack.push(this.getPossibleArgSortsAt(functName, i));
            }
        }
        return numArgs;
    }


    /** helper, gets the argument sorts of a non-overloaded function
     * @param functName name of a non-overloaded function
     * @return list of argument sort names of the specified function
     */
    private List<String> getSingleArgSortsNames(String functName) {
        Pair<Set<Pair<List<String>,String>>,BigInteger> funcSigsAndFixedArgs = this.funcSymSignatureFixed.get(functName);
        List<String> someArgList = funcSigsAndFixedArgs.x.iterator().next().x;
        int numArgs = someArgList.size();

        if(aprove.Globals.useAssertions) {
            assert funcSigsAndFixedArgs.y.equals(BigInteger.ONE.shiftLeft(numArgs).subtract(BigInteger.ONE)) : "non-fixed argument sorts found.";
        }

        return someArgList;
    }

    /** adds the return sort's name to the current functions argument sorts names
     * if there is a context for the current term
     * @param retSortName name of the sort to add
     * @return true iff it has been added
     */
    private boolean addReturnSort(String retSortName) {
        if (this.functArgsSortsStack.size() > 0) {
            Set<String> retSortsNames = new HashSet<String>();
            retSortsNames.add(retSortName);
            this.functArgsSortsStack.peek().add(retSortsNames);
            return true;
        }
        return false;
    }


    /** adds the return sorts names to the current functions argument sorts names
     * if there is a context for the current term
     * @param retSortsNames name of the possible sorts to add
     * @return true iff it has been added
     */
    private boolean addReturnSorts(Set<String> retSortsNames) {
        if (this.functArgsSortsStack.size() > 0) {
            this.functArgsSortsStack.peek().add(retSortsNames);
            return true;
        }
        return false;
    }



    /** creates a new level of function application,
     * so that the arguments sorts can later be retrieved
     * inverse to popFunctArgSorts()
     */
    private void pushNewFunctLevel() {
        this.functArgsSortsStack.push(new Vector<Set<String>>());
    }

    /** returns the possible argument sorts for each argument
     * inverse to pushNewFunctLevel()
     */
    private List<Set<String>> popFunctArgSorts() {
        return this.functArgsSortsStack.pop();
    }

    /** returns the number of possible argument sorts lists that could be generated
     * @param arg0 list of possible argument sorts for each argument
     * @return number of possible argument sorts lists
     */
    private static int sizeOf(List<Set<String>> arg0) {
        if (arg0.size() == 0) {
            return 0;
        }
        int len=1;
        for(Set<String> set : arg0) {
            len *= set.size();
            if (len == 0) {
                break;
            }
        }
        return len;
    }


    /** adds the current sort of a variable to the map of variable names to the stack of sort names
     * @param varName name of the variable
     * @param varSortName new sort of the variable varName
     */
    private void addVarSort(String varName, String varSortName) {
        Stack<String> varSortStack = this.varSort.get(varName);
        if (varSortStack == null) {
            varSortStack = new Stack<String>();
            this.varSort.put(varName, varSortStack);
        }
        varSortStack.push(varSortName);
    }


    /** remove the topmost sort of a variable
     * @param varName name of the variable
     */
    private void removeVarSort(String varName) {
        Stack<String> varSortStack = this.varSort.get(varName);
        if (varSortStack != null) {
            varSortStack.pop();
            if (varSortStack.isEmpty()) {
                this.varSort.remove(varName);
            }
        }
    }



////////////////////////////////////////////////////////////////////////
    // determining the current functions arguments
////////////////////////////////////////////////////////////////////////

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


////////////////////////////////////////////////////////////////////////
    // modifying overloaded constructors and selectors
////////////////////////////////////////////////////////////////////////

    @Override
    public void inASelidcomma(ASelidcomma node) {
        String argSortName = this.chop(node.getSort());
        this.curSelectorSortName = argSortName;
    }

    @Override
    public void caseASelidlist(ASelidlist node) {
        for(Object selidcommaNode : node.getSelidcomma()) {
            ((PSelidcomma)selidcommaNode).apply(this);
        }
        String argSortName = this.chop(node.getSort());
        this.curSelectorSortName = argSortName;
        if (node.getSelector() != null) {
            node.getSelector().apply(this);
        }
    }


    @Override
    public void outASelector(ASelector node) {
        String oldSelName = this.chop(node.getName());
        String newSelName = this.getNewFunctName(oldSelName, Arrays.asList(this.curSelectorSortName));
        if (newSelName != null) {
            node.getName().setText(newSelName);
        }
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
        String oldConsName = this.chop(tcons);
        String retSortName = this.chop(node.getReturn());
        String newConsName = this.getNewConsName(oldConsName, retSortName);
        if (newConsName != null) {
            tcons.setText(newConsName);
        }
    }


    @Override
    public void outAInfixconstr(AInfixconstr node) {
        String oldConsName = this.chop(node.getCons());
        String retSortName = this.chop(node.getReturn());
        String newConsName = this.getNewConsName(oldConsName, retSortName);
        if (newConsName != null) {
            node.getCons().setText(newConsName);
        }
    }


////////////////////////////////////////////////////////////////////////
    // handling of constants/vars and ints to get the correct return sorts
////////////////////////////////////////////////////////////////////////


    @Override
    public void caseAUnaryTterm(AUnaryTterm node) {
        String unary = this.chop(node.getUnary());

        String opName = unary + "_unary";

        Set<String> possibleSorts = this.possibleSortsStack.pop();

        this.pushPossibleSorts(opName);
        this.pushNewFunctLevel();
        node.getTterm().apply(this);
        List<Set<String>> maybeArgSortsNames = this.popFunctArgSorts();

        List<Set<String>> possibleArgSortsNames = this.getFunctPossibleArgsSortsNames(opName, maybeArgSortsNames);

        if (possibleArgSortsNames.size() > 1) {
            this.addParseError(node.getUnary(), "could not determine argument sort of unary operator ''"+unary+"''");
        }

        List<String> argSortsNames = this.getFirstArgsSortsNames(possibleArgSortsNames);
        String retSortName = this.getFunctSymRetSortName(opName, argSortsNames);

        if (!possibleSorts.contains(retSortName)) {
            this.addParseError(node.getUnary(), "The unary function ''"+unary+"'' is only defined for ''"+retSortName+"''.");
            String someRetSortName = possibleSorts.iterator().next();
            this.addReturnSort(someRetSortName);
        }
        else {
            this.addReturnSort(retSortName);
        }
    }



    @Override
    public void caseACasting(ACasting node) {
        String sortName = this.chop(node.getSort());
        this.possibleSortsStack.pop();
        this.pushSingleSort(sortName);
    }



    @Override
    public void caseAConstVarTterm(AConstVarTterm node) {
        String name = this.chop(node.getId());

        if(node.getCasting() != null) {
            node.getCasting().apply(this);
        }

        if (this.possibleSortsStack.isEmpty()) {
            this.addParseError(node.getId(), "no type found, maybe insufficiently many arguments declared?");
            this.addReturnSort(this.intSortName);
            return;
        }
        Set<String> possibleSorts = this.possibleSortsStack.pop();

        // is this an expected integer term
        if ( (this.containsInts) && (possibleSorts.contains(this.intSortName)) && (IntegerPredefItem.isIntegerString(name)) ) {
            this.intTerm(name, possibleSorts);
        }
        // or a constructor
        else
        if (this.consSymCounts.get(name) != null) {
            this.constTerm(node, name, possibleSorts);
        }
        // or an unexpected integer or a variable
        else {
            if (this.containsInts && IntegerPredefItem.isIntegerString(name)) {
                // this is an integer, check whether it was expected
                if (!possibleSorts.contains(this.intSortName)) {
                    this.addParseError(node.getId(), "The integer "+name+" cannot be used here.");
                    this.addReturnSort(this.intSortName);
                    return;
                }
            }

            // if it is not an unexpected integer, is must be a variable
            this.varTerm(node, name, possibleSorts);
        }
    }



    private void intTerm(String name, Set<String> possibleSorts) {
        if (possibleSorts.size() == 1) {
            // the return sort is clear, set it and exit
            this.addReturnSort(this.intSortName);
        }
        else {
            // is there a constructor or variable with this name?
            if ( (this.isOverloadedConstructor(name)) || (this.varSort.get(name) != null) ) {
                this.addReturnSorts(possibleSorts);
            }
            else {
                // if not, this must be an integer
                this.addReturnSort(this.intSortName);
            }
        }
    }


    private void constTerm(AConstVarTterm node, String name, Set<String> possibleSorts) {
        String retSortName = possibleSorts.iterator().next();
        if (this.isOverloadedConstructor(name)) {
                possibleSorts.retainAll(this.getConsPossibleRetSortsNames(name));
        }
        if (possibleSorts.size() > 1) {
            this.addReturnSorts(possibleSorts);
            return;
        }
        else
        if (possibleSorts.isEmpty()) {
            this.addParseError(node.getId(), "sort of constructor ''"+name+"'' could not be determined.");
        }
        else {
            retSortName = possibleSorts.iterator().next();
        }
        String newName = this.getNewConsName(name, retSortName);
        if (newName != null) {
            node.getId().setText(newName);
        }
        this.addReturnSort(retSortName);
        return;
    }


    private void varTerm(AConstVarTterm node, String name, Set<String> possibleSorts) {

        // this is a variable
        String retSortName = possibleSorts.iterator().next();
        if (this.isLHS) {
            this.addVarSort(name, retSortName);
        }
        else {
            Stack<String> thisVarSortStack = this.varSort.get(name);
            if (thisVarSortStack != null) {
                retSortName = this.varSort.get(name).peek();
            } else {
                this.addParseError(node.getId(), "unknown variable ''"+name+"''.");
            }
        }
        this.addReturnSort(retSortName);
    }


////////////////////////////////////////////////////////////////////////
    // handling of lets to get the correct return sorts
////////////////////////////////////////////////////////////////////////

    @Override
    public void caseALetlist(ALetlist node) {
        String varName = this.chop(node.getId());

        // pushing twice the unknown sort => if the return type is dependent on the possible types, it will be found to be non-determinable
        Set<String> unknownPossibleSorts = new HashSet<String>(Arrays.asList(Pass.FP_UNKNOWN_SORT.getName(), Pass.FP_UNKNOWN_SORT.getName()));
        this.possibleSortsStack.push(unknownPossibleSorts);

        // adding a new level of function application, so the return sort in there is the return sort of the rhs
        this.pushNewFunctLevel();

        // processing the rhs
        node.getTerm().apply(this);

        // determining the sort
        List<Set<String>> maybeArgSortsNames = this.popFunctArgSorts();
        if (maybeArgSortsNames.size() > 1) {
            this.addParseError(node.getId(), "could not determine the sort of let-variable ''"+varName+"''.");
        }
        List<String> functArgSorts = this.getFirstArgsSortsNames(maybeArgSortsNames);
        String rhsSortName = functArgSorts.get(0);

        // setting the sort of this variable
        this.addVarSort(varName, rhsSortName);

        // registering this variable as let variable
        this.letVarsStack.peek().add(varName);

        // processing further assignments
        if (node.getNextletlist() != null) {
            node.getNextletlist().apply(this);
        }
    }


    @Override
    public void caseALetSterm(ALetSterm node) {
        this.letVarsStack.push(new HashSet<String>());

        node.getLetlist().apply(this);
        node.getTerm().apply(this);

        // removing the sorts of the let variables
        Set<String> letVars = this.letVarsStack.pop();
        for(String letVar : letVars) {
            this.removeVarSort(letVar);
        }
    }


////////////////////////////////////////////////////////////////////////
    // handling of if to pass the correct sorts
////////////////////////////////////////////////////////////////////////


    @Override
    public void caseAIfLongSterm(AIfLongSterm node) {
        this.ifTerm(node.getIf(), node.getCondTerm(), node.getThenTerm(), node.getElseTerm());
    }


    @Override
    public void caseAIfShortSterm(AIfShortSterm node) {
        this.ifTerm(node.getIf(), node.getCondTerm(), node.getThenTerm(), node.getElseTerm());
    }

    private void ifTerm(Token ifToken, PTerm condTerm, PTerm thenTerm, PTerm elseTerm) {

        // making the stack look like this (top is at right): possibleSorts, possibleSorts, "bool"
        Set<String> possibleSorts = this.possibleSortsStack.pop();

        Set<String> thenSorts = possibleSorts;
        Set<String> elseSorts = possibleSorts;
        boolean changed = true;

        while (changed) {
            changed = false;

            this.possibleSortsStack.push(elseSorts);
            this.possibleSortsStack.push(thenSorts);
            this.pushSingleSort("bool");

            this.pushNewFunctLevel();
            condTerm.apply(this);
            thenTerm.apply(this);
            elseTerm.apply(this);
            List<Set<String>> possibleIfSorts = this.popFunctArgSorts();

            Set<String> newThenSorts = possibleIfSorts.get(1);
            Set<String> newElseSorts = possibleIfSorts.get(2);

            changed = !newThenSorts.equals(thenSorts) || !newElseSorts.equals(elseSorts);
            thenSorts = newThenSorts;
            elseSorts = newElseSorts;
        }

        if ( (thenSorts.isEmpty()) || (thenSorts.size() > 1) ) {
            this.addParseError(ifToken, "sort for ''then'' part could not be determined.");
        }
        if ( (elseSorts.isEmpty()) || (elseSorts.size() > 1) ) {
            this.addParseError(ifToken, "sort for ''else'' part could not be determined.");
        }

        this.addReturnSort(thenSorts.iterator().next());
    }

////////////////////////////////////////////////////////////////////////
    // modifying function definitions and root positions on left hand sides
////////////////////////////////////////////////////////////////////////



    @Override
    public void caseAFunct(AFunct node) {
        this.curArgSortsNames = new Vector<String>();
        this.curRetSortName = this.chop(node.getReturn());
        if (node.getIdlist() != null) {
            node.getIdlist().apply(this);
        }
        this.oldFunctName = this.chop(node.getFunctname());
        this.newFunctName = this.getNewFunctName(this.oldFunctName, this.curArgSortsNames);
        if (this.newFunctName != null) {
            node.getFunctname().setText(this.newFunctName);
        }
        for(Object ruleNode : node.getRule()) {
            ((PRule)ruleNode).apply(this);
        }
    }


    @Override
    public void caseARule(ARule node) {
        this.isLHS = true;
        this.varSort.clear();
        node.getLeft().apply(this);
        this.isLHS = false;
        this.pushSingleSort(this.curRetSortName);
        node.getRight().apply(this);
    }


    @Override
    public void caseAConstVarLterm(AConstVarLterm node) {
        String curFunctName = this.chop(node.getId());
        if (!this.oldFunctName.equals(curFunctName)) {
            this.addParseError(node.getId(), "Function \""+this.oldFunctName+"\" expected, but \""+curFunctName+"\" found.");
            return;
        }
        if (this.newFunctName != null) {
            node.getId().setText(this.newFunctName);
        }
    }

    @Override
    public void caseAFunctAppLterm(AFunctAppLterm node) {
        String curFunctName = this.chop(node.getId());
        if (!this.oldFunctName.equals(curFunctName)) {
            this.addParseError(node.getId(), "Function \""+this.oldFunctName+"\" expected, but \""+curFunctName+"\" found.");
            return;
        }
        if (this.newFunctName != null) {
            node.getId().setText(this.newFunctName);
        }
        this.pushSortNamesInRevOrder(this.curArgSortsNames);

        node.getTermlist().apply(this);
    }


////////////////////////////////////////////////////////////////////////
    // modifying function applications found on right hand sides and non-root positions
////////////////////////////////////////////////////////////////////////


    @Override
    public void caseAFunctAppTterm(AFunctAppTterm node) {
        String name = this.chop(node.getId());

        if (this.isOverloadedConstructor(name)) {
            this.consAppOverload(name, node);
        }
        else
        if (this.isOverloadedFunction(name)) {
            this.functAppOverload(name, node);
        }
        else {

            if (this.possibleSortsStack.isEmpty()) {
                this.addParseError(node.getId(), "no type found, maybe insufficiently many arguments declared?");
                this.addReturnSort(this.intSortName);
                return;
            }

            Set<String> possibleSortsNames = this.possibleSortsStack.pop();
            if (this.consSymCounts.get(name) != null) {
                Set<String> retSortNames = this.getConsPossibleRetSortsNames(name);
                if (aprove.Globals.useAssertions) {
                    assert retSortNames.size() == 1 : "found overloaded constructor ''"+name+"'' that is not marked as overloaded but has return sorts "+retSortNames;
                }
                String retSortName = retSortNames.iterator().next();
                this.pushSortNamesInRevOrder(this.getConsArgSortsNames(name, retSortName));
                this.pushNewFunctLevel();
                node.getTermlist().apply(this);
                this.popFunctArgSorts();
                this.addReturnSort(retSortName);
            }
            else
            if (this.funcSymCounts.get(name) != null) {
                List<String> argSortsNames = this.getSingleArgSortsNames(name);
                this.pushSortNamesInRevOrder(argSortsNames);
                this.pushNewFunctLevel();
                node.getTermlist().apply(this);
                this.popFunctArgSorts();
                this.addReturnSort(this.getFunctSymRetSortName(name, argSortsNames));
            }
            else {
                this.addParseError(node.getId(), "No function or constructor with name ''"+name+"'' found!");
                this.addReturnSort(possibleSortsNames.iterator().next());
            }
        }
    }


    private void consAppOverload(String name, AFunctAppTterm node) {
        if (node.getCasting() != null) {
            node.getCasting().apply(this);
        }

        Set<String> possibleSorts = this.possibleSortsStack.pop();
        String retSortName = possibleSorts.iterator().next();
        possibleSorts.retainAll(this.getConsPossibleRetSortsNames(name));

        if (possibleSorts.size() == 1) {
            retSortName = possibleSorts.iterator().next();
        }
        else {
            if (possibleSorts.size() > 1) {
                this.addReturnSorts(possibleSorts);
                return;
            }
            else {
                this.addParseError(node.getId(), "constructor ''"+name+"'' cannot be used here.");
            }
        }

        String newName = this.getNewConsName(name, retSortName);

        // do the renaming
        node.getId().setText(newName);

        // handle all arguments
        this.pushNewFunctLevel();
        this.pushSortNamesInRevOrder(this.getConsArgSortsNames(name, retSortName));
        node.getTermlist().apply(this);
        this.popFunctArgSorts();

        // publish the return sort of this constructor
        this.addReturnSort(retSortName);
    }



    private void functAppOverload(String name, AFunctAppTterm node) {
        if (node.getCasting() != null) {
            this.addParseError(((ACasting)node.getCasting()).getDblcolon(), "casting is not allowed here.");
        }

        Set<String> possibleSorts = this.possibleSortsStack.pop();

        int numArgs = ((ATermlist)node.getTermlist()).getTermcomma().size()+1;

        // push the expected sorts
        int realNumArgs = this.pushPossibleSorts(name);

        if (numArgs != realNumArgs) {
            this.addParseError(node.getId(), "expected "+realNumArgs+" arguments, but "+numArgs+" arguments found.");
        }


        List<String> argSortsNames = null;
        while(argSortsNames == null) {
            // creating a new level
            this.pushNewFunctLevel();

            // process the arguments
            node.getTermlist().apply(this);

            // get the possible sort names of the individual arguments
            List<Set<String>> maybeArgSortsNames = this.popFunctArgSorts();

            List<Set<String>> possibleArgSortsNames = this.getFunctPossibleArgsSortsNames(name, maybeArgSortsNames);

            if(RenameConstFuncPass.sizeOf(possibleArgSortsNames) == 1) {
                // build name from the argument sorts
                argSortsNames = this.getFirstArgsSortsNames(possibleArgSortsNames);

                // in this case the applicable functions determined the sorts, so no renaming yet
                if (RenameConstFuncPass.sizeOf(maybeArgSortsNames) > 1) {
                    // push the sorts that were found to enable renaming
                    this.pushSortNamesInRevOrder(argSortsNames);
                    this.pushNewFunctLevel();
                    node.getTermlist().apply(this);
                    this.popFunctArgSorts();
                }
            }
            else
            if (RenameConstFuncPass.sizeOf(maybeArgSortsNames) <= RenameConstFuncPass.sizeOf(possibleArgSortsNames)) {
                this.addParseError(node.getId(), "could not determine the arguments sorts.");
                argSortsNames = this.getFirstArgsSortsNames(possibleArgSortsNames);
            }
            else {
                // push the (smaller) possible sorts for the arguments and redo
                this.pushPossibleSortNamesInRevOrder(possibleArgSortsNames);
            }
        }

        String newName = this.getNewFunctName(name, argSortsNames);

        // do the renaming
        node.getId().setText(newName);

        // get the return sort of this function symbol
        String retSortName = this.getFunctSymRetSortName(name, argSortsNames);

        // publish the return type
        this.addReturnSort(retSortName);
    }


////////////////////////////////////////////////////////////////////////
    // modifying operator definitions and rules
////////////////////////////////////////////////////////////////////////


    @Override
    public void caseAOpdef(AOpdef node) {
        this.curArgSortsNames = new Vector<String>();
        this.curRetSortName = this.chop(node.getReturn());
        node.getIdlist().apply(this);
        this.oldFunctName = this.chop(node.getOpname());
        this.newFunctName = this.getNewFunctName(this.oldFunctName, this.curArgSortsNames);
        if (this.newFunctName != null) {
            node.getOpname().setText(this.newFunctName);
        }
        for(Object ruleNode : node.getOprule()) {
            ((POprule)ruleNode).apply(this);
        }
    }

    @Override
    public void caseAOprule(AOprule node) {
        this.varSort.clear();
        this.isLHS = true;
        this.isLHSOpRoot = true;
        node.getLeft().apply(this);
        this.isLHS = false;
        this.pushSingleSort(this.curRetSortName);
        node.getRight().apply(this);
    }

    @Override
    public void caseAOperatorTerm(AOperatorTerm node) {
        if ( (this.isLHS) && (this.isLHSOpRoot) ) {
            this.isLHSOpRoot = false;
            String curFunctName = this.chop(node.getInfixid());
            if (!this.oldFunctName.equals(curFunctName)) {
                this.addParseError(node.getInfixid(), "Function \""+this.oldFunctName+"\" expected, but  \""+curFunctName+"\" found.");
                return;
            }
            if (this.newFunctName != null) {
                node.getInfixid().setText(this.newFunctName);
            }

            this.pushSortNamesInRevOrder(this.curArgSortsNames);
            node.getLeft().apply(this);
            node.getRight().apply(this);
        }
        else {
            String opName = this.chop(node.getInfixid());

            if (this.consSymCounts.get(opName) != null) {
                this.constructorOperator(node);
            }
            else
            if (this.funcSymCounts.get(opName) != null) {
                this.functionOperator(node);
            }
            else
            if (opName.equals("==")) {
                this.pushNewFunctLevel();
                // this will be taken care of later...
                Set<String> unknownPossibleSorts = new HashSet<String>(Arrays.asList(Pass.FP_UNKNOWN_SORT.getName()));
                this.possibleSortsStack.push(unknownPossibleSorts);
                this.possibleSortsStack.push(unknownPossibleSorts);
                node.getLeft().apply(this);
                node.getRight().apply(this);
                this.popFunctArgSorts();
                this.addReturnSort("bool");
            }
            else {
                this.addParseError(node.getInfixid(), "operator ''"+opName+"'' is unknown.");
                String someRetSort = this.possibleSortsStack.pop().iterator().next();
                this.addReturnSort(someRetSort);
                return;
            }
        }
    }



    private void constructorOperator(AOperatorTerm node) {
        String opName = this.chop(node.getInfixid());
        Set<String> possibleSorts = this.possibleSortsStack.pop();
        String someRetSortName = possibleSorts.iterator().next();
        String retSortName = someRetSortName;
        if (this.isOverloadedConstructor(opName)) {
            possibleSorts.retainAll(this.getConsPossibleRetSortsNames(opName));
        }
        if (possibleSorts.size() > 1) {
            this.addReturnSorts(possibleSorts);
            return;
        }
        else if (possibleSorts.isEmpty()) {
            this.addParseError(node.getInfixid(), "constructor ''"+opName+"'' is not allowed here.");
        }
        else {
            retSortName = possibleSorts.iterator().next();
        }
        String newOpName = this.getNewConsName(opName, retSortName);

        // do the renaming
        if (newOpName != null) {
            node.getInfixid().setText(newOpName);
        }

        // process the arguments
        List<String> consArgSortNames = this.getConsArgSortsNames(opName, retSortName);
        this.pushSortNamesInRevOrder(consArgSortNames);

        this.pushNewFunctLevel();
        node.getLeft().apply(this);
        node.getRight().apply(this);
        this.popFunctArgSorts();

        this.addReturnSort(retSortName);
    }



    private void functionOperator(AOperatorTerm node) {
        String opName = this.chop(node.getInfixid());
        Set<String> possibleSorts = this.possibleSortsStack.pop();
        String someRetSortName = possibleSorts.iterator().next();
        String retSortName = someRetSortName;


        this.pushPossibleSorts(opName);

        List<String> argSortsNames = null;
        while(argSortsNames == null) {
            this.pushNewFunctLevel();

            node.getLeft().apply(this);
            node.getRight().apply(this);


            // get the possible sort names of the individual arguments
            List<Set<String>> maybeArgSortsNames = this.popFunctArgSorts();

            List<Set<String>> possibleArgSortsNames = this.getFunctPossibleArgsSortsNames(opName, maybeArgSortsNames);

            if(RenameConstFuncPass.sizeOf(possibleArgSortsNames) == 1) {
                // build name from the argument sorts
                argSortsNames = this.getFirstArgsSortsNames(possibleArgSortsNames);

                // in this case the applicable functions determined the sorts, so no renaming yet
                if (RenameConstFuncPass.sizeOf(maybeArgSortsNames) > 1) {
                    // push the sorts that were found to enable renaming
                    this.pushSortNamesInRevOrder(argSortsNames);
                    this.pushNewFunctLevel();
                    node.getLeft().apply(this);
                    node.getRight().apply(this);
                    this.popFunctArgSorts();
                }
            }
            else
            if (RenameConstFuncPass.sizeOf(maybeArgSortsNames) <= RenameConstFuncPass.sizeOf(possibleArgSortsNames)) {
                this.addParseError(node.getInfixid(), "could not determine the arguments sorts.");
                argSortsNames = this.getFirstArgsSortsNames(possibleArgSortsNames);
            }
            else
            if (RenameConstFuncPass.sizeOf(possibleArgSortsNames) == 0) {
                this.addParseError(node.getInfixid(), "operator not applicable for these argument sorts.");
                this.addReturnSort(Pass.FP_UNKNOWN_SORT.getName());
                return;
            }
            else {
                // push the (smaller) possible sorts for the arguments and redo
                this.pushPossibleSortNamesInRevOrder(possibleArgSortsNames);
            }
        }

        // building the new name
        String newOpName = this.getNewFunctName(opName, argSortsNames);

        // special handling of integers, since they expect only basenames
        boolean isIntOp = true;
        for(String argSortName : argSortsNames) {
            isIntOp &= argSortName.equals(this.intSortName);
        }
        if ( (!isIntOp) && (newOpName != null) ) {
            node.getInfixid().setText(newOpName);
        }

        this.addReturnSort(this.getFunctSymRetSortName(opName, argSortsNames));
    }


}
