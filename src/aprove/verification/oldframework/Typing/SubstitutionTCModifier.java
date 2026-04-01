package aprove.verification.oldframework.Typing;
import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Algebra.Terms.Visitors.*;
import aprove.verification.oldframework.Utility.*;

/**
 * The <code>SubstitutionTCModifier</code> is the expansion of a normal
 * {@link aprove.verification.oldframework.Algebra.Terms.Visitors.SubstitutionVisitor}
 * to handle types, especially the type quantifiers are considered.
 * @author Stephan Swiderski
 * @version $Id$
 */
public class SubstitutionTCModifier extends SubstitutionVisitor implements TCModifier{
    FreshVarGenerator fvg;
    boolean ignoreQuan;

    /**
     * construct a SubstitutionTCModifier with the option to ignore quantifiers
     * @param fvg for fresh variables
     * @param sub substitution to apply to the type context
     */
    public SubstitutionTCModifier(FreshVarGenerator fvg, AlgebraSubstitution sub){
    super(sub);
        this.fvg = fvg;
    this.ignoreQuan = false;
    }

    /**
     * construct a SubstitutionTCModifier with the option to ignore quantifiers
       @param fvg for fresh variables
     * @param sub substitution to apply to the type context
     * @param ignoreQuan set to true, if you wish to ignore the quantifiers otherwise set to false
     */
    public SubstitutionTCModifier(FreshVarGenerator fvg, AlgebraSubstitution sub, boolean ignoreQuan){
    super(sub);
        this.fvg = fvg;
    this.ignoreQuan = ignoreQuan;
    }

    @Override
    public Object caseVariable(AlgebraVariable v) {
    AlgebraTerm t = this.sub.get(v.getVariableSymbol());
    if (t == null) {
        t = v;
    }
    return t.deepcopy();
    }

    @Override
    public void caseType(Type t){
        AlgebraSubstitution ren;
        if (this.ignoreQuan) {
            //ren = Substitution.create();
        } else {
        ren = t.typeQuantifier.refreshVars(this.fvg); // handle the quantifier
            t.applyToMatrix(ren);
        }
        t.applyToMatrix(this);
    }

    @Override
    public void caseSetOfTypes(Set<Type> ts){
        Iterator i = ts.iterator();
    while(i.hasNext()){
            this.caseType((Type)i.next());
    }
    }

    @Override
    public void caseTypeAssumption(TypeAssumption ta){
        Iterator it = ta.getRange().iterator();
        while (it.hasNext()){
            this.caseSetOfTypes((Set<Type>) it.next());
        }
    }

    @Override
    public void caseTypeDefinition(TypeDefinition td){
        AlgebraSubstitution ren;
        if (this.ignoreQuan) {
            ren = AlgebraSubstitution.create();
        } else {
        ren = td.refreshVars(this.fvg); // type definitions have got an intern quantifier
    }
        Iterator it = td.typeMap.entrySet().iterator();
        while (it.hasNext()){
            Map.Entry entry = (Map.Entry) it.next();
            Iterator jt = ((Set<Type>)entry.getValue()).iterator();
        while (jt.hasNext()){
               Type t = (Type) jt.next();
               t.typeMatrix = (AlgebraTerm) t.typeMatrix.apply(ren).apply(this);
        }
        }
    }

    @Override
    public void caseTypeContext(TypeContext tct){
        Iterator it = tct.typeDefMap.entrySet().iterator();
    while (it.hasNext()){
            Map.Entry entry = (Map.Entry) it.next();
        TypeDefinition td = (TypeDefinition)entry.getValue();
        this.caseTypeDefinition(td);
    }
    this.caseTypeAssumption(tct.curTa);
    }

}
