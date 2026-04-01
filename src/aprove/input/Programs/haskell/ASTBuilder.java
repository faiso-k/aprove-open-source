package aprove.input.Programs.haskell;

import java.util.*;

import aprove.input.Generated.haskell.analysis.*;
import aprove.verification.oldframework.Haskell.*;

/**
 * The ASTBuilder offers three stacks,
 * one for HaskellObjects, one for the current marks and one for the curent mode
 *
 */
public class ASTBuilder extends DepthFirstAdapter {
    public static final int EXP = 1;
    public static final int PAT = 2;

    Vector<HaskellObject> vector; // carries the objects
    Stack<Integer> markStack; // carries the stacksize of the begin of a stack frame
    Stack<Integer> modeStack; // carries the mode

    public ASTBuilder(){
        this.vector = new Vector<HaskellObject>();
        this.markStack = new Stack<Integer>();
        this.modeStack = new Stack<Integer>();
        this.pushMode(ASTBuilder.EXP);
    }

    public void push(HaskellObject ho){
        this.vector.add(ho);
    }

    /**
     * checks if the current mode is a pattern
     */
    public boolean isPatMode(){
        return (this.modeStack.peek().intValue() & ASTBuilder.PAT) > 0;
    }

    /**
     * checks if the current mode is a expression
     */
    public boolean isExpMode(){
        return (this.modeStack.peek().intValue() & ASTBuilder.EXP) > 0;
    }

    public void pushMode(int i){
        this.modeStack.push(Integer.valueOf(i));
    }

    public int popMode(){
        return this.modeStack.pop().intValue();
    }

    public void pushMark(){
        this.markStack.push(Integer.valueOf(this.vector.size()));
    }

    public int popMark(){
        int i = this.markStack.pop().intValue();
        return i;
    }

    /**
     * @returns the size of the current stackframe
     */
    public int popMarkCount(){
        return this.vector.size() - this.markStack.pop().intValue();
    }

    public HaskellObject pop(){
        HaskellObject ho = this.vector.remove(this.vector.size()-1);
        return ho;
    }

    public HaskellObject peek(){
        return this.vector.get(this.vector.size()-1);
    }

    /**
     * @return pops the current stackframe of haskellobjects as array
     */
    public HaskellObject[] popMarkArray(){
        int mark = this.popMark();
        HaskellObject[] pArray = this.vector.subList(mark,this.vector.size()).toArray(new HaskellObject[0]);
        this.vector.setSize(mark);
        return pArray;
    }

    /**
     * @return pops the current stackframe of haskellobjects as list
     */
    public List<HaskellObject> popMarkList(){
        int mark = this.popMark();
        List<HaskellObject> pList = new Vector<HaskellObject>();
        pList.addAll(this.vector.subList(mark,this.vector.size()));
        this.vector.setSize(mark);
        return pList;
    }

}
