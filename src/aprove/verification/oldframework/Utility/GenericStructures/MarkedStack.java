package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

public class MarkedStack<T> {

    protected Object mark;
    protected Stack<Object> internStack;

    public MarkedStack(){
        this.internStack = new Stack<Object>();
        this.mark = new Object();
    }

    public void push (T t){
        this.internStack.push(t);
    }

    @SuppressWarnings("unchecked")
    public T peek(){
        Object peekedElement = this.internStack.peek();
        if(this.mark == peekedElement) {
            throw new MarkOnTopException();
        }
        return (T) peekedElement;
    }

    @SuppressWarnings("unchecked")
    public T pop(){
        Object poppedElement = this.internStack.pop();
        if(this.mark == poppedElement) {
            throw new MarkOnTopException();
        }
        return (T) poppedElement;
    }

    @SuppressWarnings("unchecked")
    public List<T> popDownToMark(){
        List<T> list = new Vector<T>();
        if(this.internStack.isEmpty()){
            throw new MissingMarkException();
        }
        while (!this.internStack.isEmpty()){
           Object popedElement = this.internStack.pop();
           if (popedElement == this.mark) {
               return list;
           }
           list.add(0, (T) popedElement);
        }
        return list;
    }

    public void deleteMarkOnTop() {
        if(this.isMarkOnTop()) {
            this.internStack.pop();
        }
        else {
            throw new NoMarkOnTopException();
        }
    }

    public void pushMark(){
        this.internStack.push(this.mark);
    }

    @SuppressWarnings("unchecked")
    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();

        Iterator<Object> it = this.internStack.iterator();
        sb.append("[");
        if(it.hasNext()) {
            Object o = it.next();
            if(o != this.mark) {
                T t = (T) o;
                sb.append(t.toString());
            }
            else {
                sb.append("mark");
            }
        }
        while(it.hasNext()) {
            Object o = it.next();
            sb.append(",\n");
            if(o != this.mark) {
                T t = (T) o;
                sb.append(t.toString());
            }
            else {
                sb.append("mark");
            }
        }
        return sb.append("]").toString();
    }

    public boolean isEmpty(){
        return this.internStack.isEmpty();
    }

    public int size(){
        return this.internStack.size();
    }

    public boolean hasProperTop() {
        return this.isNotEmpty() && this.isNoMarkOnTop();
    }

    public boolean isNotEmpty() {
        return (! (this.internStack.isEmpty()));
    }

    public boolean isNoMarkOnTop() {
        return this.isNotEmpty() ? this.internStack.peek() != this.mark : true;
    }

    public boolean isMarkOnTop() {
        return this.internStack.peek() == this.mark;
    }

    public static class MissingMarkException extends RuntimeException {
        public MissingMarkException() {
            super("Stack is empty, it has no mark!");
        }
    }

    public static class MarkOnTopException extends RuntimeException {
        public MarkOnTopException() {
            super("Mark is on top of the stack which cannot be popped");
        }
    }

    public static class NoMarkOnTopException extends RuntimeException {
        public NoMarkOnTopException() {
            super("No Mark on top of the stack to be popped");
        }
    }
}
