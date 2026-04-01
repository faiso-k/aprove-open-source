package aprove.verification.oldframework.Typing;
import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/**
 * The <code>TypeCheckerVistor</code> try to infer the single type of a given
 * {@link aprove.verification.oldframework.Algebra.Terms.AlgebraTerm} with a given type context.
 * (multiple type environment is not compatible with this visitor)
 * @author Stephan Swiderski
 * @version $Id$
 */
public class TypeCheckerVisitor extends AbstractTypeVisitor<AlgebraTerm> {
    private boolean stop;
    private AlgebraSubstitution ref;

    public TypeCheckerVisitor(FreshVarGenerator fvg,TypeContext tct,TypeAssumption loc){
        super(fvg,tct,tct.curTa,loc);
    this.stop = false;
    this.ref = AlgebraSubstitution.create();
    }

    public TypeCheckerVisitor(FreshVarGenerator fvg,TypeContext tct){
        super(fvg,tct,tct.curTa,new TypeAssumption.TypeAssumptionSkeleton());
    this.stop = false;
    this.ref = AlgebraSubstitution.create();
    }

    @Override
    public AlgebraTerm caseVariable(AlgebraVariable v) {
        if (this.stop) { return null; } // stop by typecheck error
        try {
            return this.getFreshTypeTermOf((Symbol)v.getVariableSymbol());
        } catch (TypingException e) {
            throw new RuntimeException( e.getMessage() );
        }
    }

    @Override
    public AlgebraTerm caseFunctionApp(AlgebraFunctionApplication f) {
        /*
        * t1,...,tn: terms
        * f: n-arity function symbol
    * A: type assumtion
    * s1,...,sn: substitutions
    *
    *
        * Input term: f(t1,...,tn)
    *
    * Loop:
        *   W(A,t1):=(s1,ty_1):=res_1;
    *   ...
        *   W(A * s1*...*sn,tn):=(sn,ty_n):=res_n;
    *
    * sigma=mgu(tau_f * s1*...*sn,
    *           ty_1 * s2*...*sn-> ... -> ty_n -> b * s1* ...*sn)
        *
    * W(A * s1*...*sn*sigma,f(t1,...,tn))=(b,s1*...*sn*sigma)
        */
        if (this.stop) { return null; } // stop by typecheck error
        AlgebraTerm tau_f = this.getFreshTypeTermOf(f.getFunctionSymbol());
    List<AlgebraTerm> args =  f.getArguments();
    List<AlgebraTerm> argTypes = TypeTools.getFunctionArgs(tau_f);
    if (args.size() != argTypes.size()) {
            this.stop = true;
        return null;
    }
    Iterator i = args.iterator();
    Iterator j = argTypes.iterator();
    while (i.hasNext()) {
        AlgebraTerm curTerm = (AlgebraTerm)i.next();
        AlgebraTerm curTermType = (AlgebraTerm)(curTerm).apply(this);
        if (this.stop) { return null; }
        AlgebraTerm expectedType = (AlgebraTerm) j.next();
        AlgebraSubstitution sigma;
            try {
            sigma=(curTermType.unifies(expectedType));
            } catch (UnificationException ue){
                this.stop = true;
            return null;
        }
        tau_f = tau_f.apply(sigma);
        (new SubstitutionTCModifier(this.fvg,sigma)).caseTypeAssumption(this.locals);
    }
    return TypeTools.getResultTerm(tau_f);
    }

    public static AlgebraTerm getRetAndBuildAssumption(TypeContext tct,Rule r,TypeAssumption.TypeAssumptionSkeleton loc){
        if (tct == null) { return null; }
        TypeCheckerVisitor tcv = new TypeCheckerVisitor(new FreshVarGenerator(),tct,loc);
        Iterator i = r.getConds().iterator();
    while (i.hasNext()){
        Rule cr = (Rule) i.next();
        TypeTools.equi(cr.getLeft(),cr.getRight()).apply(tcv);
    }
    return (AlgebraTerm) TypeTools.equi(r.getLeft(),r.getRight()).apply(tcv);
    }

    public static AlgebraTerm combinedTypeTerm(TypeContext tct,AlgebraTerm s,AlgebraTerm t){
        if (tct == null) { return null; }
        TypeCheckerVisitor tcv = new TypeCheckerVisitor(new FreshVarGenerator(),tct);
    return (AlgebraTerm) (TypeTools.equi(s,t)).apply(tcv);
    }

}
