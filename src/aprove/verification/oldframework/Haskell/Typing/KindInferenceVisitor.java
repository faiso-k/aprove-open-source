package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Syntax.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This visitor infers the kinds of all type constructors and type classes.
 *
 */
public class KindInferenceVisitor extends OmegaVisitor {
    Set <HaskellEntity.Sort> TYPESOF = EnumSet.of(HaskellEntity.Sort.VAR,
                                                  HaskellEntity.Sort.CONS);
    Set <HaskellEntity.Sort> VALUESOF = EnumSet.of(HaskellEntity.Sort.TYCLASS,
                                  HaskellEntity.Sort.INST,
                                  HaskellEntity.Sort.TYCONS);

    public KindInferenceVisitor(EntityAssumptions entityAssumptions,Prelude prelude){
        super(entityAssumptions,prelude);
    }

    /**
     * this methode starts the kind inference, it walks through the groups,
     * after each group the type variables in assumptions, are instantiated
     * with Stars (*), see Haskell-Report.
     */
    public void infer(List<Set<HaskellEntity>> groups,Set<HaskellPreType> innerTypes){
        for (Set<HaskellEntity> group : groups) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println(group);
            }

            for(HaskellEntity e : group){
                e.visit(this);
            }
            this.resetStack();
            this.assumptions.refine(new AllToStar(this.prelude.getKindStar()));
        }
        for (HaskellPreType ty : innerTypes){
            ty.visit(this);
            this.resetStack();
        }
        //HaskellSym.show("Kind Assumptions",this.assumptions);
    }

/*    public void fcaseTypeSchema(TypeSchema ho){
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("CurTypeSchema:"+ho);
        }
    };

    public void fcaseEntity(HaskellEntity ho){
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("CurEntity:"+ho);
        }
    };
*/
    @Override
    public HaskellType buildArrow(HaskellType f,HaskellType x){
        return this.prelude.buildKindArrow(f,x);
    }

    @Override
    public HaskellSubstitution mgu(BasicTerm a,BasicTerm b,HaskellObject ho) {
        HaskellSubstitution subs = BasicTerm.Tools.mgu(a,b);
    if (subs == null) {
        HaskellSym.showee(this);
        HaskellError.output(ho,"kinds are not unifiable "+a+" -:- "+b);
    }
    return subs;
    }

    @Override
    public boolean guardValue(HaskellEntity ho){
        return this.VALUESOF.contains(ho.getSort());
    }

    @Override
    public boolean guardType(HaskellEntity ho){
        return this.TYPESOF.contains(ho.getSort());
    }

    @Override
    public boolean guardMember(HaskellEntity ho){
        return ho.getSort() != HaskellEntity.Sort.INST;
    }

    @Override
    public boolean guardHaskellNamedSym(HaskellNamedSym ho) {
        return false;
    }

    @Override
    public boolean guardDecls(TTDecl ho){
        return false;
    }

    @Override
    public boolean guardDefType(SynTypeDecl ho) {
        return true;
    }

    @Override
    public boolean guardConss(DataDecl ho){
        return false;
    }

    /**
     * Each variable should be replaced by a Star (*)
     * and this is the substitution for that purpose.
     */
    public class AllToStar extends HaskellSubstitution{
        Cons star;

        public AllToStar(Cons star){
           this.star = star;
        }

        @Override
        public HaskellObject get(Object sym){
            return this.star;
        }
    }
}
