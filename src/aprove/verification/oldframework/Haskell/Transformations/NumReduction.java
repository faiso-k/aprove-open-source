package aprove.verification.oldframework.Haskell.Transformations;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Literals.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;


/**
 *
 * Converts numbers/chars (e.g. 1) to their representation as data structure (e.g. Pos (Succ Zero))
 * Futhermore all type expressions are reduced to their expression only
 *
 * @author Stephan Swiderski
 * @version $Id$
 *
 */
public class NumReduction extends BasicReduction {

    HaskellEntity succEntity;
//    HaskellEntity predEntity;
    HaskellEntity posEntity;
    HaskellEntity negEntity;
    HaskellEntity zeroEntity;
    HaskellEntity charEntity;
    HaskellEntity fromIntEntity;
    HaskellEntity fromDoubleEntity;
    HaskellEntity doubleEntity;
    HaskellEntity tyCharEntity;
    HaskellEntity tyNatEntity;
    HaskellEntity tyIntEntity;
    HaskellEntity tyDoubleEntity;
    HaskellObject csucc;
//    HaskellObject cpred;
    HaskellObject cpos;
    HaskellObject cneg;
    HaskellObject czero;
    HaskellObject cchar;
    HaskellObject cdouble;
    HaskellType tyNat;
    HaskellType tyInt;
    HaskellType tyChar;
    HaskellType tyDouble;

    private HaskellEntity getEntity(String name){
        return this.prelude.getEntityN(this,"Prelude",name,HaskellEntity.Sort.VAR);
    }

    private HaskellEntity getCoEntity(String name){
        return this.prelude.getEntityN(this,"Prelude",name,HaskellEntity.Sort.CONS);
    }

    private HaskellEntity getTyCoEntity(String name){
        return this.prelude.getEntityN(this,"Prelude",name,HaskellEntity.Sort.TYCONS);
    }


    private HaskellObject buildNatNumber(int j) {
        if (j < 0) {
            HaskellError.output((HaskellObject)null, "Negative number, expecting a natural number!");
        }

        HaskellObject num = Copy.deep(this.czero);
        for (int i=0;i<j;i++){
            num = this.prelude.buildApply(Copy.deep(this.csucc),num);
        }
        return num;
    }

    private HaskellObject buildNumber(int j){
        HaskellObject num = Copy.deep(this.czero);
        if (j >= 0) {
            return this.prelude.buildApply(Copy.deep(this.cpos), this.buildNatNumber(j));
        } else {
            return this.prelude.buildApply(Copy.deep(this.cneg), this.buildNatNumber(-j));
        }
    }

    @Override
    public HaskellObject caseCharLit(CharLit ho) {
        this.setChanged();
        return this.prelude.buildApply(Copy.deep(this.cchar),this.buildNatNumber(ho.getCharValue()));
    }

     @Override
    public HaskellObject caseIntegerLit(IntegerLit ho) {
        this.setChanged();
        HaskellObject num = this.buildNumber(ho.getIntValue());
        if (((BasicTerm)this.tyInt).equivalentTo((BasicTerm)ho.getTypeTerm())){
            return num;  // Int need no fromInt
        }
        HaskellObject fromInt = new Var(new HaskellNamedSym(this.fromIntEntity)).setTypeTerm(this.prelude.buildArrow(this.tyInt,ho.getTypeTerm()));
        return this.prelude.buildApply(fromInt,num);
     }

     @Override
    public HaskellObject caseFloatLit(FloatLit ho) {
        this.setChanged();

        BigDecimal val = ho.getFloatValue();
        BigInteger val_unscaled = val.unscaledValue();
        BigInteger val_scale = BigInteger.TEN.pow(val.scale());
        BigInteger gcd = val_unscaled.gcd(val_scale);
        val_unscaled = val_unscaled.divide(gcd);
        val_scale = val_scale.divide(gcd);

        HaskellObject numerator = this.buildNumber(val_unscaled.intValue());
        HaskellObject denominator = this.buildNumber(val_scale.intValue());

//        return ho;
        HaskellObject numTerm = this.prelude.buildApplies(Copy.deep(this.cdouble), Arrays.asList(numerator,denominator));
        HaskellObject fromDouble = new Var(new HaskellNamedSym(this.fromDoubleEntity)).setTypeTerm(this.prelude.buildArrow(this.tyDouble,ho.getTypeTerm()));
        return this.prelude.buildApply(fromDouble, numTerm);
     }



     /*
      * Removed here, since this replacement is EQUIVALENT, but the rest is only SOUND
      *
     public HaskellObject caseTypeExp(TypeExp ho) {
        this.setChanged();
        return ho.getExpression();
     }
     */


    public static boolean applyTo(Modules modules,Abortion aborter){
        NumReduction br = new NumReduction();
        br.setAborter(aborter);
        br.prelude = modules.getPrelude();
        br.tyNatEntity  = br.checkNull(br.getTyCoEntity("Nat"));
        br.zeroEntity = br.checkNull(br.getCoEntity("Zero"));
        br.succEntity = br.checkNull(br.getCoEntity("Succ"));
//        br.predEntity = br.checkNull(br.getCoEntity("Pred"));
        if (!br.nullCheck) {
            br.tyNat = (new Cons(new HaskellNamedSym(br.tyNatEntity)));
            br.czero = (new Cons(new HaskellNamedSym(br.zeroEntity))).setTypeTerm(br.tyNat);
            br.csucc = (new Cons(new HaskellNamedSym(br.succEntity))).setTypeTerm(br.prelude.buildArrow(br.tyNat,br.tyNat));
//            br.cpred = (new Cons(new HaskellNamedSym(br.predEntity))).setTypeTerm(br.prelude.buildArrow(br.tyInt,br.tyInt));
        }

        br.tyIntEntity  = br.checkNull(br.getTyCoEntity("Int"));
        br.posEntity = br.checkNull(br.getCoEntity("Pos"));
        br.negEntity = br.checkNull(br.getCoEntity("Neg"));
        if (!br.nullCheck) {
            br.tyInt = (new Cons(new HaskellNamedSym(br.tyIntEntity)));
            br.cpos = (new Cons(new HaskellNamedSym(br.posEntity))).setTypeTerm(br.prelude.buildArrow(br.tyNat,br.tyInt));
            br.cneg = (new Cons(new HaskellNamedSym(br.negEntity))).setTypeTerm(br.prelude.buildArrow(br.tyNat,br.tyInt));
        }

        br.fromIntEntity = br.checkNull(br.getEntity("fromInt"));

        br.nullCheck = false;
        br.tyCharEntity = br.checkNull(br.getTyCoEntity("Char"));
        br.charEntity = br.checkNull(br.getCoEntity("Char"));
        if (!br.nullCheck) {
            br.tyChar = (new Cons(new HaskellNamedSym(br.tyCharEntity)));
            br.cchar = (new Cons(new HaskellNamedSym(br.charEntity))).setTypeTerm(br.prelude.buildArrow(br.tyNat,br.tyChar));
        }

        br.nullCheck = false;
        br.tyDoubleEntity = br.checkNull(br.getTyCoEntity("Double"));
        br.doubleEntity = br.checkNull(br.getCoEntity("Double"));
        if (!br.nullCheck) {
            br.tyDouble = (new Cons(new HaskellNamedSym(br.tyDoubleEntity)));
            br.cdouble = (new Cons(new HaskellNamedSym(br.doubleEntity))).setTypeTerm(br.prelude.buildArrow(br.tyInt,br.prelude.buildArrow(br.tyInt,br.tyDouble)));
        }

        br.fromDoubleEntity = br.checkNull(br.getEntity("fromDouble"));

        br.forModules(modules);
        return br.wasChanged();
    }



}
