package aprove.verification.oldframework.Haskell;

import java.util.*;
import java.util.regex.*;

import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Narrowing.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Haskell.Typing.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 * HaskellTools is a collection of convenience methods for working in the Haskell Framework,
 * especially there are methods for the fixity and priority (Pixity) reordering of RawTerms
 * and somethings like apply flatten or apply create.
 */

public class HaskellTools{

    /**
     * for (...((h t1) t2 )...tn)
     * it returns h
     */
    public static HaskellObject getLeftMost(HaskellObject obj){
        while (obj instanceof Apply){
           obj = ((Apply) obj).getFunction();
        }
        return obj;
    }

    /**
     * for (...((h t1) t2 )...tn)
     * it returns (h t1)
     */
    public static Apply getLeftMostApply(HaskellObject obj){
        Apply lastApply = null;
        while (obj instanceof Apply){
           lastApply = (Apply) obj;
           obj = lastApply.getFunction();
        }
        return lastApply;
    }

    /**
     * for (...((h t1) t2 )...tn)
     * it returns [h,t1,t2,...,tn]
     */
    public static List<HaskellObject> applyFlatten(HaskellObject obj){
        List<HaskellObject> res = new Vector<HaskellObject>();
        while (obj instanceof Apply){
           Apply apply = (Apply) obj;
           res.add(0,apply.getArgument());
           obj = apply.getFunction();
        }
        res.add(0,obj);
        return res;
    }

    /**
     * returns the i's apply of an apply stack
     * for (...((h tn) tn-1 )...t0)
     * it returns (...((h tn) tn-1 )...ti)
     * example:  applyGet( ((a b) c) d) , 1) == (a b) c)
     */
    public static Apply applyGet(Apply apply,int i){
         while (i > 0){
             i--;
             apply = (Apply) apply.getFunction();
         }
         return apply;
    }


    /**
     * returns the List of Typeterms by reading each form a List of HaskellObjects
     */
    public static List<HaskellType> getTypeTerms(List<? extends HaskellObject> hos){
       List<HaskellType> res = new Vector<HaskellType>();
       for (HaskellObject ho : hos){
           res.add(ho.getTypeTerm());
       }
       return res;

    }

    /**
     * for [h,t1,t2,...,tn]
     * returns (...((h t1) t2) ... tn)
     */
    public static HaskellObject buildApplies(List<? extends HaskellObject> list){
        Iterator<? extends HaskellObject> it = list.iterator();
        HaskellObject res = it.next();
        while(it.hasNext()){
            res = (new Apply(res,it.next()));
        }
        return res;
    }

    private static HaskellObject buildApply(HaskellObject a,HaskellObject b,HaskellObject c){
        return HaskellTools.buildApply(HaskellTools.buildApply(a,b),c);
    }

    private static HaskellObject buildApply(HaskellObject a,HaskellObject b){
        return (new Apply(a,b)).transferToken(a);
    }

    /**
     * terms with operators are correctly orderByPixity
     */
    public static HaskellObject arrangeFixityPriority(List <HaskellObject> objs){
        List<Pixity> pixis = new Vector<Pixity>();
        for (HaskellObject ho : objs){
            pixis.add(new Pixity(ho));
        }
        return HaskellTools.orderByPixity(pixis);
    }

    private static HaskellObject orderByPixity(List<Pixity> pixis){
        int i=0;
        while ((pixis.size()>1) && (i<pixis.size())) {
            int size = pixis.size();
            Pixity a = pixis.get(i);
            if (a.isMono()) {
               HaskellTools.getMono(pixis.subList(i,pixis.size()));
               i = 0;
            } else if ((size>i+4) && (a.priority < 0) && HaskellTools.pat5Check(pixis.subList(i,i+5))) {
               i = 0;
            } else if ((size==i+3) && (a.priority < 0) && HaskellTools.pat3Check(pixis.subList(i,i+3))) {
               i = 0;
            } else {
               i++;
            }
        }
        return pixis.get(0).getObject();
    }

    /**
     * [-,5,+,6,+,7,+,8,*,9]
     * is reduced to
     * [(- 5),+,6,+,7,+,8,*,9]
     *
     * [-,5,*,6,*,7,+,8,*,9]
     * is reduced to
     * [(- (((*) 5) (((*) 6) 7))),+,8,*,9]
     *
     */
    private static void getMono(List <Pixity> pixis){
        List<Pixity> result = new Vector<Pixity>();
        Pixity mono = pixis.remove(0);
        // as long as there are values, or ops with higer priority get them in a new group
        while ((pixis.size()> 0) && ((pixis.get(0).priority > mono.priority) || pixis.get(0).isVal())){
            result.add(pixis.remove(0));
        }
        pixis.add(0,new Pixity(HaskellTools.buildApply(mono.getObject(),HaskellTools.orderByPixity(result))));
    }

    /**
     * [5,*,6,*,7,+,8]
     * is reduced to
     * [((*) 5 6),*,7,+,8]
     *
     * it checks the priority of the second operator
     * and if this is lower (or equal with left fixity)
     * the reduction is made.
     */
    private static boolean pat5Check(List<Pixity> pixis){
        Pixity a = pixis.get(0);
        Pixity b = pixis.get(1);
        Pixity c = pixis.get(2);
        Pixity d = pixis.get(3);
        Pixity e = pixis.get(4);
        if (a.isVal() && b.isOp() && c.isVal() && d.isOp() && e.isVal()) {
           if (b.priority == d.priority) {
               if (!HaskellTools.isCorrectFixity(b,d)) {
                   HaskellError.output(b.getObject(),"ambiguous operator application");
               }
           }
           if  ((b.priority > d.priority) ||
                  ((b.priority == d.priority) && b.isLeft() && d.isLeft())) {
               pixis.remove(0);
               pixis.remove(0);
               pixis.remove(0);
               pixis.add(0,new Pixity(HaskellTools.buildApply(b.getObject(),a.getObject(),c.getObject())));
               return true;
           }
        }
        return false;
    }

    private static boolean isCorrectFixity(Pixity a,Pixity b){
        return (a.isRight() && b.isRight()) || (a.isLeft() && b.isLeft());
    }

    /**
     * [1,*,3,...]
     * is reduced to
     * [(((*) 1) 3),...]
     */
    private static boolean pat3Check(List<Pixity> pixis){
        Pixity a = pixis.get(0);
        Pixity b = pixis.get(1);
        Pixity c = pixis.get(2);
        if (a.isVal() && b.isOp() && c.isVal()) {
            pixis.remove(0);
            pixis.remove(0);
            pixis.remove(0);
            pixis.add(0,new Pixity(HaskellTools.buildApply(b.getObject(),a.getObject(),c.getObject())));
            return true;
        }
        return false;
    }

    /**
     * Wrapper for a HaskellObject which contains
     * Fixity and Priority informations
     */
    public static class Pixity{
        public int fixity;
        public int priority;
        HaskellObject obj;

        public Pixity(HaskellObject obj){
            if (obj instanceof Operator) {
                Operator op = (Operator) obj;
                Atom atom = op.getAtom();
                this.obj = atom;
                HaskellEntity e = atom.getSymbol().getEntity();
                this.fixity = e.getFixity();
                this.priority = e.getPriority();
            } else {
                this.fixity = -1;
                this.priority = -1;
                this.obj = obj;
            }
        }

        public HaskellObject getObject(){
            return this.obj;
        }

        public boolean isVal(){
            return this.priority == -1;
        }

        public boolean isOp(){
            return this.priority >= 0;
        }

        public boolean isMono(){
            return (this.fixity == InfixDecl.FIXITY_MONO);
        }

        public boolean isLeft(){
            return (this.fixity == InfixDecl.FIXITY_LEFT);
        }

        public boolean isRight(){
            return (this.fixity == InfixDecl.FIXITY_RIGHT);
        }

        public boolean isNon(){
            return (this.fixity == InfixDecl.FIXITY_DEFAULT) || (this.fixity == InfixDecl.FIXITY_NON);
        }
    }


    private static Pattern startTermPattern = Pattern.compile("\\s*<([^>]+)>\\s*(.*)");

    /**
     * parses a startterm and returns the startterm that is split into the term part and a type
     * @see StartTerm.toString()
     * @param startTerm the startterm, which might contain &lt;type&gt;
     * @return a StartTerm
     */
    public static StartTerm parseStartTerm(String startTerm) {
        Matcher m = HaskellTools.startTermPattern.matcher(startTerm);
        StartTerm.Type startTermType = StartTerm.Type.H_TERMINATION;
        if (m.matches()) {
            startTerm = m.group(2);
            startTermType = StartTerm.Type.getTypeOf(m.group(1));
            if (startTermType == null) {
                HaskellError.output((HaskellObject)null, "unknown start term type: "+m.group(1));
            }
        }
        return new StartTerm(startTerm, startTermType);
    }


    /**
     * gets a subterm of a term by its subtermID
     * @param bt the HaskellObject to get the subterm from
     * @param id the ID of the subterm
     * @return the subterm or null if no such subterm exists
     */
    public static HaskellObject getSubtermByID(BasicTerm bt, int id) {
        // is the outermost already the subterm requested?
        if (bt.getSubtermNumber() == id) {
            return bt;
        }

        SubTermIterator sti = new SubTermIterator(bt);
        while(sti.hasNext()) {
            Apply subtermApply = sti.next();
            /*
            if (subtermApply.getSubtermNumber() == id) {
                return subtermApply;
            }
            */

            for(HaskellObject sho : Arrays.asList(subtermApply.getFunction(), subtermApply.getArgument())) {
                if ( (sho instanceof BasicTerm) && (((BasicTerm)sho).getSubtermNumber() == id) ) {
                    return sho;
                }
            }
        }
        return null;
    }

}
