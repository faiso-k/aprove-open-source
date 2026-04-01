package aprove.verification.oldframework.Haskell.BasicTerms;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * A BasicTerm of Haskell
 * BasicTerms consist of Applies, Variables and Constructors
 */
public interface BasicTerm extends HaskellObject {
    public static enum Sort {APPLY,VAR,CONS}

    /**
     * sets the subterm number of a basicterm
     */
    public void setSubtermNumber(int num);

    /**
     * sets the subterm number of a basicterm
     */
    public int getSubtermNumber();

    /**
     * returns the sort of an basicterm
     */
    public BasicTerm.Sort getBasicSort();

    /**
     * checks structurally equivalence of this and another Basicterm
     */
    public boolean equivalentTo(BasicTerm t);

    /**
     * Tools for BasicTerms
     */
    public static class Tools {

        /* return true if and only if t1 subterm of t2
         *
         */
        public static boolean isSubTerm(BasicTerm t1,BasicTerm t2){
            if (t2.equivalentTo(t1)) {
                return true;
            }
            if (t2.getBasicSort() == BasicTerm.Sort.APPLY) {
                Apply app = (Apply) t2;
                if (Tools.isSubTerm(t1,(BasicTerm)app.getFunction())) {
                    return true;
                }
                if (Tools.isSubTerm(t1,(BasicTerm)app.getArgument())) {
                    return true;
                }
            }
            return false;
        }

        /*public static Triple<BasicTerm,Substitution,Substitution> generalize(BasicTerm t1,BasicTerm t2){
            if (t1.equivalentTo(t2)){
                return new Triple<BasicTerm,Substitution,Substitution>(t1,new Substitution(),new Substitution());
            }
            BasicTerm.Sort s1 = t1.getBasicSort();
            BasicTerm.Sort s2 = t2.getBasicSort();
            if (s1 == s2){
                switch (s1){
                    case APPLY: {
                        Apply app1 = (Apply) t1;
                        Apply app2 = (Apply) t2;
                        Triple<BasicTerm,Substitution,Substitution> resFunc = generalize((BasicTerm)app1.getFunction(),(BasicTerm)app2.getFunction());
                        Triple<BasicTerm,Substitution,Substitution> resArg = generalize((BasicTerm)app1.getArgument(),(BasicTerm)app2.getArgument());
                        Substitution sub1 = resFunc.y.combineWith(resArg.y);
                        Substitution sub2 = resFunc.z.combineWith(resArg.z);
                        return new Triple<BasicTerm,Substitution,Substitution>((BasicTerm)app1.hoCopy(new Apply(resFunc.x,resArg.x)),sub1,sub2);
                        }
                    case CONS: {
                        HaskellSym sym = new HaskellSym();
                        Substitution sub1 = new Substitution(sym,t1);
                        Substitution sub2 = new Substitution(sym,t2);
                        return new Triple<BasicTerm,Substitution,Substitution>((BasicTerm)t1.hoCopy(new Var(sym)),sub1,sub2);
                        }
                    case VAR: {
                        Substitution sub1 = new Substitution();
                        Substitution sub2 = new Substitution((Var)t1,t2);
                        return new Triple<BasicTerm,Substitution,Substitution>(t1,sub1,sub2);
                        }
                }
                return null;
            } else {
                HaskellSym sym = new HaskellSym();
                Substitution sub1 = new Substitution(sym,t1);
                Substitution sub2 = new Substitution(sym,t2);
                return new Triple<BasicTerm,Substitution,Substitution>((BasicTerm)t1.hoCopy(new Var(sym)),sub1,sub2);
            }
        } */

        /**
         * the normal matching
         * if subs=/=null then
         * gen * subs = constant holds
         */
        public static HaskellSubstitution match(BasicTerm gen,BasicTerm constant){
            HaskellSubstitution subs = new HaskellSubstitution();
            if (Tools.match(gen,constant,false,subs)){
                return subs.eliminateDuplicates();
            }
            return null;
        }

        /*
        public static Substitution matchI(BasicTerm gen,BasicTerm constant){
            Substitution subs = new Substitution();
            if (match(gen,constant,true,subs)){
                return subs;
            }
            return null;
        }
        */

        /**
         * the normal matching
         * returns true iff gen matches constant (gen * subs = constant)
         * @param subs substitution to fill up with the matching relevant replacements
         */
        public static boolean match(BasicTerm gen,BasicTerm constant,boolean checkLocal,HaskellSubstitution subs){
            //if (gen.equivalentTo(constant)) return true;
            if (gen.getBasicSort() == BasicTerm.Sort.VAR){
                Var var = (Var) gen;
                HaskellSym sym = var.getSymbol();
                if (checkLocal) {
                    HaskellEntity e = sym.getEntity();
                    if (e != null) {
                        if (e instanceof VarEntity){
                            if (!(((VarEntity)e).getLocal())){
                                return gen.equivalentTo(constant);//false;
                            }
                        }
                    }
                }
                HaskellObject rep = subs.getReplaceFor(sym);
                if (rep == null) {
                    subs.put(sym,constant);
                    return true;
                } else {
                    return constant.equivalentTo((BasicTerm)rep);
                }
            } else if (gen.getBasicSort() == BasicTerm.Sort.CONS) {
                return gen.equivalentTo(constant);
            } else {
                if ((gen.getBasicSort() == BasicTerm.Sort.APPLY) &&
                   (constant.getBasicSort() == BasicTerm.Sort.APPLY)) {
                      Apply app1 = (Apply) gen;
                      Apply app2 = (Apply) constant;
                      return Tools.match((BasicTerm)app1.getArgument(),(BasicTerm)app2.getArgument(),checkLocal,subs) &&
                             Tools.match((BasicTerm)app1.getFunction(),(BasicTerm)app2.getFunction(),checkLocal,subs);
                }
            }
            return false;
        }


        /**
         * returns true iff two BasicTerms a equivalent modulo variable renaming
         */
        public static boolean equalsModuloVariables(BasicTerm t1,BasicTerm t2){
            return Tools.varEqui(t1,t2,new HashMap<HaskellSym,HaskellSym>());
        }

        private static boolean varEqui(BasicTerm t1,BasicTerm t2,Map<HaskellSym,HaskellSym> symMap){
            BasicTerm.Sort s1 = t1.getBasicSort();
            BasicTerm.Sort s2 = t2.getBasicSort();
            if (s1 != s2) {
                return false;
            }
            if (s1 == BasicTerm.Sort.APPLY){
                Apply app1 = (Apply) t1;
                Apply app2 = (Apply) t2;
                return Tools.varEqui((BasicTerm)app1.getArgument(),(BasicTerm)app2.getArgument(),symMap) &&
                       Tools.varEqui((BasicTerm)app1.getFunction(),(BasicTerm)app2.getFunction(),symMap);

            }
            HaskellSym sym1 = ((Atom)t1).getSymbol();
            HaskellSym sym2 = ((Atom)t2).getSymbol();
            if (s1 == BasicTerm.Sort.VAR){
                HaskellSym sym2t = symMap.get(sym1);
                if (sym2t == null) {
                   return true;
                } else {
                   return sym2.equivalentTo(sym2t);
                }
            }
            if (s1 == BasicTerm.Sort.CONS){
                return sym1.equivalentTo(sym2);
            }
            return false;
        }

        /**
         * destructive (speed)
         * if subs is applied to (possible modified) t1 or to (possible modified) t2 the result will be the the expected
         * subs = mgu(t1,t2), subs != null
         * nt1 = (t1 destructive modified by call of mgu(t1,t2))
         * nt2 = (t2 destructive modified by call of mgu(t1,t2))
         * ==>  t1 * subs == nt1 * subs,   t2 * subs == nt2 * subs
         * so if t1 * subs is only used later no copy of t1 is needed
         * same for t2
         *
         * if you are not sure how to use: call it like this:
         * subs = mgu(Copy.deep(t1),Copy.deep(t2))
         * @return the most general unifier of t1 and t2, if one exist, null otherwise
         */
        public static HaskellSubstitution mgu(BasicTerm t1,BasicTerm t2){
            List<Pair<BasicTerm,BasicTerm>> eqs = new Vector<Pair<BasicTerm,BasicTerm>>();
            eqs.add(new Pair<BasicTerm,BasicTerm>(t1,t2));
            return Tools.mgu(eqs,false,false);
        }

        public static HaskellSubstitution mgu(Collection<Pair<BasicTerm,BasicTerm>> neqs,boolean match,boolean checklocal){
            Boolean change = true;
            // carries the equations
            List<Pair<BasicTerm,BasicTerm>> eqs = new Vector<Pair<BasicTerm,BasicTerm>>(neqs);
            // carries the equations of the solutions
            List<Pair<BasicTerm,BasicTerm>> soleqs = new Vector<Pair<BasicTerm,BasicTerm>>();
            while(eqs.size()>0) {
                Pair<BasicTerm,BasicTerm> eq = eqs.remove(0);
                if (!match) {
                    if (eq.getKey().getBasicSort() != BasicTerm.Sort.VAR){
                        if (eq.getValue().getBasicSort() == BasicTerm.Sort.VAR){
                            // if no flip is allowed only the key side of the pair
                            // could change
                            Pair.flip(eq);
                        }
                    }
                }
                if (eq.getKey().equivalentTo(eq.getValue())) {
                    // trivial equations are removed
                } else if (eq.getKey().getBasicSort() == BasicTerm.Sort.VAR){
                    // occur check
                    if (checklocal){
                        Var vs = (Var)eq.getKey();
                        HaskellEntity e = vs.getSymbol().getEntity();
                        if (e != null) {
                            if (e instanceof VarEntity){
                                if (!(((VarEntity)e).getLocal())){
                                    return null;
                                }
                            }
                        }
                    }
                    if (match){
                        HaskellSubstitution subs = new HaskellSubstitution(eq);
                        for (Pair<BasicTerm,BasicTerm> ceq : eqs){
                            ceq.setKey(subs.applyToDestructive(ceq.getKey()));
                        }
                    } else {
                        if (Tools.isSubTerm(eq.getKey(),eq.getValue())) {
                            HaskellError.println("SubTerm("+eq.getKey()+","+eq.getValue()+")");
                            return null;
                        }
                        HaskellSubstitution subs = new HaskellSubstitution(eq);
                        for (Pair<BasicTerm,BasicTerm> soleq : soleqs){
                            soleq.setValue(subs.applyToDestructive(soleq.getValue()));
                        }
                        for (Pair<BasicTerm,BasicTerm> ceq : eqs){
                            ceq.setKey(subs.applyToDestructive(ceq.getKey()));
                            ceq.setValue(subs.applyToDestructive(ceq.getValue()));
                        }
                    }
                    soleqs.add(eq);
                } else if ((eq.getKey().getBasicSort() == BasicTerm.Sort.APPLY) &&
                           (eq.getValue().getBasicSort() == BasicTerm.Sort.APPLY)) {
                    // attention: don't mix keys and values, its a basic assumption for matching
                    Apply app1 = (Apply) eq.getKey();
                    Apply app2 = (Apply) eq.getValue();
                    eqs.add(new Pair<BasicTerm,BasicTerm>((BasicTerm)app1.getFunction(),(BasicTerm)app2.getFunction()));
                    eqs.add(new Pair<BasicTerm,BasicTerm>((BasicTerm)app1.getArgument(),(BasicTerm)app2.getArgument()));
                } else {
                    // clash check
                    return null;
                }
            }
            return new HaskellSubstitution(soleqs);
        }
    }
}
