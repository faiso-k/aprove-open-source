package aprove.verification.dpframework.TRSProblem.Utility;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * represents a minimized RedexAlgebra corresponding to {@link RedexAlgebra}<br>
 * for more information see [ENDRULLIS_HENRIKS_2009]
 * @author Tim Enger
 */

public class MinimizedRedexAlgebra {

    /**
     * underlying CoreRedexAlgebra
     */
    private RedexAlgebra algebra;

    /**
     * equivalence classes
     */
    private Set<Set<TRSFunctionApplication>> eClasses;

    public MinimizedRedexAlgebra(ImmutableSet<? extends GeneralizedRule> rules,
            Set<FunctionSymbol> signature) {

        this.algebra = new RedexAlgebra(rules, signature);
        if (Globals.DEBUG_NEX) {
            System.err.println("Redexalgebra: " + this.algebra.getA());
        }

        this.algebra.buildCore();
        if (Globals.DEBUG_NEX) {
            System.err.println("core Redexalgebra: " + this.algebra.getA());
        }

        this.eClasses = this.minimize(signature);
        if (Globals.DEBUG_NEX) {
            System.err.println("minimized RedexAlgebra: " + this.eClasses);
        }
    }

    /**
     * represents [.]^E<br>
     * [f]^E(|a_1|,...,|a_n|) = |f(a_1,...,a_n)|<br>
     * where |..| denotes equivalence class
     * @param f
     * @param argsClasses
     * @return
     */
    public Set<TRSFunctionApplication> interpret(FunctionSymbol f,
        List<Set<TRSFunctionApplication>> argsClasses) {
        // build f(a_1,..._a_n)
        ArrayList<TRSFunctionApplication> args = new ArrayList<TRSFunctionApplication>();
        for (Set<TRSFunctionApplication> argClass : argsClasses) {
            args.add(this.getClassRep(argClass));
        }
        TRSFunctionApplication funApp = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(args));
        funApp = this.algebra.interpret(f, args);
        return this.getEquivClass(funApp);
    }

    /**
     * represents the function isRedex^E_f<br>
     * isRedex^E_f(|a_1|,...,|a_n|) = isRedex_f(a_1,...,a_n)<br>
     * where isRedex_f(a_1,...,a_n) is defined by the underlying RedexAlgebra
     * @param f
     * @param argsClasses
     * @return
     */
    public boolean isRedex(FunctionSymbol f,
        List<Set<TRSFunctionApplication>> argsClasses) {
        ArrayList<TRSFunctionApplication> args =
            new ArrayList<TRSFunctionApplication>();
        for (Set<TRSFunctionApplication> argClass : argsClasses) {
            args.add(this.getClassRep(argClass));
        }
        return this.algebra.isRedex(f, args);
    }

    private Set<TRSFunctionApplication> getEquivClass(TRSFunctionApplication funApp) {
        for (Set<TRSFunctionApplication> eClass : this.eClasses) {
            if (eClass.contains(funApp)) {
                return eClass;
            }
        }
        // must not happen
        assert (false);
        return null;
    }

    private TRSFunctionApplication getClassRep(Set<TRSFunctionApplication> eClass) {
        return eClass.iterator().next();
    }

    /**
     * minimize the underlying core algebra
     * @param sig
     * @return set of equivalence classes
     */
    private Set<Set<TRSFunctionApplication>> minimize(Set<FunctionSymbol> sig) {
        int iteration = 0;

        // E_0 equivalence
        Set<Set<TRSFunctionApplication>> classes =
            this.divideClass(this.algebra.getA(), iteration, sig);
        iteration++;
        Set<Set<TRSFunctionApplication>> newClasses;

        boolean changed = true;
        while (changed) {
            changed = false;

            newClasses = new LinkedHashSet<Set<TRSFunctionApplication>>();
            for (Set<TRSFunctionApplication> eClass : classes) {
                // E_i
                if (eClass.size() < 2) {
                    newClasses.add(eClass);
                } else {
                    newClasses.addAll(this.divideClass(eClass, iteration, sig));
                }
            }
            if (!classes.equals(newClasses)) {
                classes = newClasses;
                changed = true;
                iteration++;
            }
        }

        return classes;
    }

    /**
     * divides equiv-classes
     * @param eClass equiv class
     * @param sig all {@link FunctionSymbol FunctionSymbols} f
     * @return new list of classes if the class could be divided in more classes
     */
    private Set<Set<TRSFunctionApplication>> divideClass(Set<TRSFunctionApplication> eClass,
        int iteration,
        Set<FunctionSymbol> sig) {

        Set<Set<TRSFunctionApplication>> classes =
            new LinkedHashSet<Set<TRSFunctionApplication>>();

        List<TRSFunctionApplication> listClass =
            new ArrayList<TRSFunctionApplication>(eClass);

        for (int i = 0; i < listClass.size(); i++) {
            for (int j = i; j < listClass.size(); j++) {
                TRSFunctionApplication a = listClass.get(i);
                TRSFunctionApplication b = listClass.get(j);

                // if a and b are equiv, we only need to find one class
                if (this.equivI(a, b, sig, iteration)) {
                    if (classes.isEmpty()) {
                        Set<TRSFunctionApplication> newClass =
                            new LinkedHashSet<TRSFunctionApplication>();
                        newClass.add(a);
                        newClass.add(b);
                        classes.add(newClass);
                    }

                    boolean inserted = false;
                    for (Set<TRSFunctionApplication> testClass : classes) {
                        // pick an arbitrary term of class testClass
                        TRSFunctionApplication c = testClass.iterator().next();

                        // if c is equivalent we can add a and b to this class
                        if (this.equivI(a, c, sig, iteration)) {
                            testClass.add(a);
                            testClass.add(b);
                            inserted = true;
                            break;
                        }
                    }

                    // if no class is equivalent we need a new class
                    if (!inserted) {
                        Set<TRSFunctionApplication> newClass =
                            new LinkedHashSet<TRSFunctionApplication>();
                        newClass.add(a);
                        newClass.add(b);
                        classes.add(newClass);
                    }
                } else { // a and b are not equiv
                    if (classes.isEmpty()) {
                        Set<TRSFunctionApplication> newClass =
                            new LinkedHashSet<TRSFunctionApplication>();
                        newClass.add(a);
                        classes.add(newClass);
                        newClass = new LinkedHashSet<TRSFunctionApplication>();
                        newClass.add(b);
                        classes.add(newClass);
                    }

                    boolean insertedA = false;
                    boolean insertedB = false;

                    for (Set<TRSFunctionApplication> testClass : classes) {
                        // pick an arbitrary term of class testClass
                        TRSFunctionApplication c = testClass.iterator().next();

                        // if c is equivalent we can add a to this class
                        if (this.equivI(a, c, sig, iteration)) {
                            testClass.add(a);
                            insertedA = true;
                        }

                        // if c is equivalent we can add b to this class
                        if (this.equivI(b, c, sig, iteration)) {
                            testClass.add(b);
                            insertedB = true;
                        }

                        if (insertedA && insertedB) {
                            break;
                        }
                    }

                    // if no class is equivalent we need a new class
                    if (!insertedA) {
                        Set<TRSFunctionApplication> newClass =
                            new LinkedHashSet<TRSFunctionApplication>();
                        newClass.add(a);
                        classes.add(newClass);
                    }
                    if (!insertedB) {
                        Set<TRSFunctionApplication> newClass =
                            new LinkedHashSet<TRSFunctionApplication>();
                        newClass.add(b);
                        classes.add(newClass);
                    }
                }
            }
        }
        return classes;
    }

    /**
     * checks if a and b are E_i equivalent<br>
     * <br>
     * a E_0 b if<br>
     * isRedex(f,{x,a,y}) == isRedex(f, {x,b,y}) <br>
     * for all f \in sig, j \in {1,...,#f}, <br>
     * x \in A^{j-1}, y \in setA^{#f-j}, #f = arity of f<br>
     * <br>
     * a E_i+1 b if <br>
     * [f](x,a,y) E_i [f](x,b,y) <br>
     * for all f \in sig, j \in {1,...,#f}, <br>
     * x \in A^{j-1}, y \in setA^{#f-j}, #f = arity of f
     * @param a
     * @param b
     * @param sig
     * @param iteration
     * @return true, if a nd b are equivalent, false otherwise
     */
    private boolean equivI(TRSFunctionApplication a,
        TRSFunctionApplication b,
        Set<FunctionSymbol> sig,
        int iteration) {

        for (FunctionSymbol f : sig) {
            if (f.getArity() != 0) { // if f is a constant isRedex_f is trivially true
                List<TRSFunctionApplication> args1 =
                    new ArrayList<TRSFunctionApplication>();
                List<TRSFunctionApplication> args2 =
                    new ArrayList<TRSFunctionApplication>();

                for (int j = 1; j <= f.getArity(); j++) {
                    List<List<TRSFunctionApplication>> x =
                        Combinations.createCombinations(
                            new ArrayList<TRSFunctionApplication>(this.algebra.getA()),
                            j - 1);

                    List<List<TRSFunctionApplication>> y =
                        Combinations.createCombinations(
                            new ArrayList<TRSFunctionApplication>(this.algebra.getA()),
                            f.getArity() - j);

                    for (List<TRSFunctionApplication> argsX : x) {
                        for (List<TRSFunctionApplication> argsY : y) {
                            args1 = new ArrayList<TRSFunctionApplication>(argsX);
                            args1.add(a);
                            args1.addAll(argsY);

                            args2 = new ArrayList<TRSFunctionApplication>(argsX);
                            args2.add(b);
                            args2.addAll(argsY);

                            if (iteration == 0) { // E_0 equivalence
                                if (this.algebra.isRedex(f, args1) != this.algebra.isRedex(
                                    f, args2)) {
                                    return false;
                                }
                            } else { // E_i equivalence
                                if (!this.equivI(this.algebra.interpret(f, args1),
                                    this.algebra.interpret(f, args2), sig,
                                    iteration - 1)) {
                                    return false;
                                }
                            }
                        }
                    }
                }
            }
        }
        return true;
    }

    /**
     * extends the algebra to top-algebra
     * @param top {@link FunctionSymbol} to denote top
     */
    public void extendTop(FunctionSymbol top) {
        this.algebra.extendTop(top);
    }

    /**
     * @return set of all equivalence classes
     */
    public Set<Set<TRSFunctionApplication>> getE() {
        return this.eClasses;
    }

}
