package aprove.verification.dpframework.HaskellProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.theoremprover.TerminationProofs.*;
/**
 * Helper class for proof output in Haskell transformation processors.
 *
 * @author Stephan Swiderski
 */
public abstract class HaskellProof extends Proof implements Exportable {
    HaskellProgram oldHaskellProgram;
    HaskellProgram newHaskellProgram;

    List<OldNew> reductions;

    public HaskellProof(){
        this.reductions = new Vector<OldNew>();
    }

    public HaskellProof(HaskellProgram oldHaskellProgram, HaskellProgram newHaskellProgram) {
        this();
    this.oldHaskellProgram = oldHaskellProgram;
    this.newHaskellProgram = newHaskellProgram;
    this.name = "HaskellProof";
    this.shortName = "HL";
    this.longName = "Haskell";
    };

    public void setReductions(List<OldNew> reductions){
        this.reductions = reductions;
    }

    public List<OldNew> getReductions(){
        return this.reductions;
    }

    public void add(Object a,Module ma,Object b,Module mb){
        this.reductions.add(new OldNew(a,ma,b,mb));
    }

    public HaskellProgram getOriginalHaskellProgram() {
    return this.oldHaskellProgram;
    }

    public HaskellProgram getNewHaskellProgram() {
    return this.newHaskellProgram;
    }

    /**
     * Formats the output string of the proof and returns it.
     */
    @Override
    public String export(Export_Util o) {
        this.startUp();
    this.result.append("This is a haskell proof." + o.paragraph() + "\n");
        return this.result.toString();
    }

    public String export(Export_Util o,String before,String between) {
        StringBuffer res = new StringBuffer();
        res.append(o.linebreak());
        for (OldNew t : this.reductions){
            res.append(before);
            res.append(o.linebreak());
            res.append(o.quote(o.haskellObject((HaskellObject)t.getA(),t.getMa())));
            res.append(o.linebreak());
            res.append(between);
            res.append(o.linebreak());
            res.append(o.quote(o.haskellObject((HaskellObject)t.getB(),t.getMb())));
            res.append(o.linebreak());

        }
    return res.toString();
    };

    public String exportSets(Export_Util o,String before,String between) {
        StringBuffer res = new StringBuffer();
        res.append(o.linebreak());
        for (OldNew t : this.reductions){
            res.append(before);
            res.append(o.linebreak());
            res.append(o.quote(o.haskellObject((HaskellObject)t.getA(),t.getMa())));
            res.append(o.linebreak());
            res.append(between);
            res.append(o.linebreak());
            for (HaskellObject ho : ((Set<HaskellObject>)t.getB())){
               res.append(o.quote(o.haskellObject(ho,t.getMb())));
               res.append(o.linebreak());
            }
        }
    return res.toString();
    };


    /**
     * Returns a BibTeX citation string for elements of this proof.
     */
    public String toBibTeX(){
    // No citations are given.
    return "";
    };

    public static class OldNew{
        Object a;
        Module ma;
        Object b;
        Module mb;

        OldNew(){
        }

        OldNew(Object a,Module ma,Object b,Module mb){
            this.a = a;
            this.ma = ma;
            this.b = b;
            this.mb = mb;
        }

        public void setA(Object a){
            this.a = a;
        }

        public Object getA(){
            return this.a;
        }

        public void setB(Object b){
            this.b = b;
        }

        public Object getB(){
            return this.b;
        }

        public void setMa(Module ma){
            this.ma = ma;
        }

        public Module getMa(){
            return this.ma;
        }

        public void setMb(Module mb){
            this.mb = mb;
        }

        public Module getMb(){
            return this.mb;
        }
    }
}
