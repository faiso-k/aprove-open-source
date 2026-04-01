package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;

public class SubTermIterator implements Iterator<Apply> {
    protected List<HaskellObject> terms;
    protected Apply next;

    public SubTermIterator(HaskellObject ho){
        this.terms = new LinkedList<HaskellObject>();
        this.terms.add(ho);
        this.next = this.getNext();
    }

    protected Apply getNext(){
        while (!this.terms.isEmpty()) {
            HaskellObject term = this.terms.remove(0);
            if (term instanceof Apply){
                Apply apply = (Apply) term;
                this.terms.add(0,apply.getFunction());
                this.terms.add(apply.getArgument());
                return apply;
            }
        }
        return null;
    }

    @Override
    public boolean hasNext(){
        return this.next != null;
    }

    @Override
    public Apply next(){
        Apply buf = this.next;
        this.next = this.getNext();
        return buf;
    }

    @Override
    public void remove(){
    }

}
