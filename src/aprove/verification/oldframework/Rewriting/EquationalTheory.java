package aprove.verification.oldframework.Rewriting ;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/** A collection of equations defining an equational theory.
 *  @author Stephan Falke
 *  @version $Id$
 */

public class EquationalTheory extends LinkedHashSet<TRSEquation> implements LaTeX_Able, HTML_Able {

    /* constructors */

    private EquationalTheory(Collection<TRSEquation> E) {
    super();
    if(E != null) {
        this.addAll(E);
    }
    }

    /** Constructor for an equational theory from a given set of TRSEquations.
     */
    public static EquationalTheory create(Collection<TRSEquation> E) {
    return new EquationalTheory(E);
    }

    /** Constructor for an empty equational theory.
     */
    public static EquationalTheory create() {
    return new EquationalTheory(null);
    }

    /** Creates an equational theory stating that symb is associative and commutative.
     * For this, symb has to be binary and the types of the arguments have to
     * be the same as the symbol's type.
     */
    public static EquationalTheory createACTheory(SyntacticFunctionSymbol symb, Program prog) {
        List<String> signatureOfProg;
        if (prog == null) {
            signatureOfProg = new Vector<String>();
        } else {
            signatureOfProg = prog.getSignature();
        }
        FreshNameGenerator fng = new FreshNameGenerator(signatureOfProg, FreshNameGenerator.VARIABLES);
    EquationalTheory res = EquationalTheory.create();
    Sort sort = symb.getSort();
    AlgebraVariable x = AlgebraVariable.create(VariableSymbol.create(fng.getFreshName("x",false), sort));
    AlgebraVariable y = AlgebraVariable.create(VariableSymbol.create(fng.getFreshName("y",false), sort));
    AlgebraVariable z = AlgebraVariable.create(VariableSymbol.create(fng.getFreshName("z",false), sort));

    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    args.add(x);
    args.add(y);
    AlgebraTerm fxy = AlgebraFunctionApplication.create(symb, args);

    args = new Vector<AlgebraTerm>();
    args.add(y);
    args.add(x);
    AlgebraTerm fyx = AlgebraFunctionApplication.create(symb, args);

    args = new Vector<AlgebraTerm>();
    args.add(y);
    args.add(z);
    AlgebraTerm fyz = AlgebraFunctionApplication.create(symb, args);

    args = new Vector<AlgebraTerm>();
    args.add(x);
    args.add(fyz);
    AlgebraTerm fxfyz = AlgebraFunctionApplication.create(symb, args);

    args = new Vector<AlgebraTerm>();
    args.add(fxy);
    args.add(z);
    AlgebraTerm ffxyz = AlgebraFunctionApplication.create(symb, args);

    res.add(TRSEquation.create(fxfyz, ffxyz));
    res.add(TRSEquation.create(fxy, fyx));

    return res;
    }

    /** Creates an equational theory stating that symb is commutative.
     * For this, symb has to be binary and the arguments need to have the
     * same type.
     */
    public static EquationalTheory createCTheory(SyntacticFunctionSymbol symb, Program prog) {
        List<String> signatureOfProg;
        if (prog == null) {
            signatureOfProg = new Vector<String>();
        } else {
            signatureOfProg = prog.getSignature();
        }
        FreshNameGenerator fng = new FreshNameGenerator(signatureOfProg, FreshNameGenerator.VARIABLES);
    EquationalTheory res = EquationalTheory.create();
    Sort sort = symb.getArgSort(0);
    AlgebraVariable x = AlgebraVariable.create(VariableSymbol.create(fng.getFreshName("x",false), sort));
    AlgebraVariable y = AlgebraVariable.create(VariableSymbol.create(fng.getFreshName("y",false), sort));

    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    args.add(x);
    args.add(y);
    AlgebraTerm fxy = AlgebraFunctionApplication.create(symb, args);

    args = new Vector<AlgebraTerm>();
    args.add(y);
    args.add(x);
    AlgebraTerm fyx = AlgebraFunctionApplication.create(symb, args);

    res.add(TRSEquation.create(fxy, fyx));

    return res;
    }

    /** Creates an equational theory stating that symb is associative.
     * For this, symb has to be binary and the arguments need to have the
     * same type as the function symbol.
     */
    public static EquationalTheory createATheory(SyntacticFunctionSymbol symb, Program prog) {
        List<String> signatureOfProg;
        if (prog == null) {
            signatureOfProg = new Vector<String>();
        } else {
            signatureOfProg = prog.getSignature();
        }
        FreshNameGenerator fng = new FreshNameGenerator(signatureOfProg, FreshNameGenerator.VARIABLES);
        EquationalTheory res = EquationalTheory.create();
    Sort sort = symb.getSort();
    AlgebraVariable x = AlgebraVariable.create(VariableSymbol.create(fng.getFreshName("x",false), sort));
    AlgebraVariable y = AlgebraVariable.create(VariableSymbol.create(fng.getFreshName("y",false), sort));
    AlgebraVariable z = AlgebraVariable.create(VariableSymbol.create(fng.getFreshName("z",false), sort));

    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    args.add(x);
    args.add(y);
    AlgebraTerm fxy = AlgebraFunctionApplication.create(symb, args);

    args = new Vector<AlgebraTerm>();
    args.add(y);
    args.add(z);
    AlgebraTerm fyz = AlgebraFunctionApplication.create(symb, args);

    args = new Vector<AlgebraTerm>();
    args.add(x);
    args.add(fyz);
    AlgebraTerm fxfyz = AlgebraFunctionApplication.create(symb, args);

    args = new Vector<AlgebraTerm>();
    args.add(fxy);
    args.add(z);
    AlgebraTerm ffxyz = AlgebraFunctionApplication.create(symb, args);

    res.add(TRSEquation.create(fxfyz, ffxyz));

    return res;
    }


    /** Determines if this is the theory of an AC symbol.
     */
    public boolean isACTheory() {
    Set<SyntacticFunctionSymbol> symbs = this.getFunctionSymbols();
    if(symbs.size()!=1) {
        return false;
    }
    SyntacticFunctionSymbol symb = (SyntacticFunctionSymbol)symbs.iterator().next();
    if(symb.getArity()!=2 ||
       !symb.getSort().equals(symb.getArgSort(0)) ||
       !symb.getSort().equals(symb.getArgSort(1))) {
        return false;
    }

    return this.equals(EquationalTheory.createACTheory(symb,null));
    }

    /** Determines if this is the theory of a C symbol.
     */
    public boolean isCTheory() {
    Set<SyntacticFunctionSymbol> symbs = this.getFunctionSymbols();
    if(symbs.size()!=1) {
        return false;
    }
    SyntacticFunctionSymbol symb = (SyntacticFunctionSymbol)symbs.iterator().next();
    if(symb.getArity()!=2 ||
       !symb.getArgSort(1).equals(symb.getArgSort(0))) {
        return false;
    }

    return this.equals(EquationalTheory.createCTheory(symb,null));
    }

    /** Determines if this is the theory of an A symbol.
     */
    public boolean isATheory() {
    Set<SyntacticFunctionSymbol> symbs = this.getFunctionSymbols();
    if(symbs.size()!=1) {
        return false;
    }
    SyntacticFunctionSymbol symb = (SyntacticFunctionSymbol)symbs.iterator().next();
    if(symb.getArity()!=2 ||
       !symb.getSort().equals(symb.getArgSort(0)) ||
       !symb.getSort().equals(symb.getArgSort(1))) {
        return false;
    }

    return this.equals(EquationalTheory.createATheory(symb,null));
    }


    /** Returns all function symbols occuring in this equational theory.
     */
    public Set<SyntacticFunctionSymbol> getFunctionSymbols() {
    Set<SyntacticFunctionSymbol> res = new HashSet<SyntacticFunctionSymbol>();
    Iterator i = this.iterator();
    while(i.hasNext()) {
        res.addAll(((TRSEquation)i.next()).getFunctionSymbols());
    }
    return res;
    }

    /** Returns all constructor  symbols occuring in this equational theory.
     */
    public Set<SyntacticFunctionSymbol> getConstructorSymbols() {
    Set<SyntacticFunctionSymbol> res = new HashSet<SyntacticFunctionSymbol>();
    Iterator i = this.iterator();
    while(i.hasNext()) {
        res.addAll(((TRSEquation)i.next()).getConstructorSymbols());
    }
    return res;
    }

    /** Two equational theories are equal if their defining equations are equal
     * up to a renaming of variables.
     */
    @Override
    public boolean equals(Object o) {
    EquationalTheory other = (EquationalTheory)o;
    return LightweightEquations.create(this).equals(LightweightEquations.create(other));
    }

    /** Returns all equations containing fun.
     */
    public EquationalTheory getEquations(SyntacticFunctionSymbol fun) {
    EquationalTheory res = EquationalTheory.create();
    Iterator i = this.iterator();
    while(i.hasNext()) {
        TRSEquation eq = (TRSEquation)i.next();
        if(eq.getFunctionSymbols().contains(fun)) {
        res.add(eq);
        }
    }
    return res;
    }

    /** Returns all equations containing a symbol of funs.
     */
    public EquationalTheory getEquations(Collection<SyntacticFunctionSymbol> funs) {
    EquationalTheory res = EquationalTheory.create();
    Iterator i = funs.iterator();
    while(i.hasNext()) {
        res.addAll(this.getEquations((SyntacticFunctionSymbol)i.next()));
    }
    return res;
    }

    /** Returns the smallest disjoint subtheories of this equational theory.
     */
    public EquationalTheories getDisjointSubtheories() {
    Vector<SyntacticFunctionSymbol> funs = new Vector<SyntacticFunctionSymbol>(this.getFunctionSymbols());

    int size = funs.size();
    boolean[] sameTheory = new boolean[size*size];
    Map indices = new HashMap();
    int index = 0;
    Iterator i = funs.iterator();
    while(i.hasNext()) {
        indices.put(i.next(), Integer.valueOf(index));
        index++;
    }

    /* symbol is in same theory as itself */
    for(int s=0; s<size; s++) {
        sameTheory[s + size*s] = true;
    }

    /* symbols are in same theory if there is an equation containing them */
    i = this.iterator();
    while(i.hasNext()) {
        TRSEquation eq = (TRSEquation)i.next();
        Set<SyntacticFunctionSymbol> setSameTheory = eq.getFunctionSymbols();
        Iterator j = setSameTheory.iterator();
        while(j.hasNext()) {
        SyntacticFunctionSymbol symb1 = (SyntacticFunctionSymbol)j.next();
        int index1 = ((Integer)indices.get(symb1)).intValue();
        Iterator k = setSameTheory.iterator();
        while(k.hasNext()) {
            SyntacticFunctionSymbol symb2 = (SyntacticFunctionSymbol)k.next();
            int index2 = ((Integer)indices.get(symb2)).intValue();
            sameTheory[index1 + size*index2] = true;
            sameTheory[index2 + size*index1] = true;
        }
        }
    }

    /* transitive closure */
    for(int y=0; y<size; y++) {
        for(int x=0; x<size; x++) {
        if(sameTheory[x + size*y]) {
            for(int z=0; z<size; z++) {
            if(sameTheory[y + size*z]) {
                sameTheory[x + size*z] = true;
            }
            }
        }
        }
    }

    /* construct signatures of subtheories */
    LinkedHashSet eqclasses = new LinkedHashSet();
    for(int s=0; s<size; s++) {
        Vector<SyntacticFunctionSymbol> eqclass = new Vector<SyntacticFunctionSymbol>();
        for(int t=0; t<size; t++) {
        if(sameTheory[s + size*t]) {
            eqclass.add(funs.elementAt(t));
        }
        }
        eqclasses.add(eqclass);
    }

    /* create subtheories */
    EquationalTheories res = EquationalTheories.create();
    i = eqclasses.iterator();
    while(i.hasNext()) {
        res.add(EquationalTheory.create(this.getEquations((Vector<SyntacticFunctionSymbol>)i.next())));
    }

    return res;
    }

    /** Determines whether this theory contains only constructors and variables.
     */
    public boolean isConstructorTheory() {
    Iterator i = this.iterator();
    while(i.hasNext()) {
        TRSEquation eq = (TRSEquation)i.next();
        if(!eq.isConstructorEquation()) {
        return false;
        }
    }
    return true;
    }

    /** Returns the root symbols on either side of all equations.
     */
    public Set<SyntacticFunctionSymbol> getRootSymbols() {
    Set<SyntacticFunctionSymbol> res = new LinkedHashSet<SyntacticFunctionSymbol>();
    Iterator i = this.iterator();
    while(i.hasNext()) {
        TRSEquation eq = (TRSEquation)i.next();
        res.addAll(eq.getRootSymbols());
    }
    return res;
    }

    /** Determines whether this theory is suitable for the Dp method.
     */
    public boolean isDpSuitable() {
    Iterator i = this.iterator();
    while(i.hasNext()) {
        TRSEquation eq = (TRSEquation)i.next();
        if(eq.isCollapsing() || !eq.hasIdenticalUniqueVars()) {
        return false;
        }
    }
    return true;
    }

    /** Computes the sub-theory indices of the root symbols of this theory.
     */
    public Map getTheoryIndices() {
    Vector<SyntacticFunctionSymbol> funs = new Vector<SyntacticFunctionSymbol>(this.getFunctionSymbols());

    int size = funs.size();
    boolean[] sameTheory = new boolean[size*size];
    Map indices = new HashMap();
    int index = 0;
    Iterator i = funs.iterator();
    while(i.hasNext()) {
        indices.put(i.next(), Integer.valueOf(index));
        index++;
    }

    /* symbol is in same theory as itself */
    for(int s=0; s<size; s++) {
        sameTheory[s + size*s] = true;
    }

    /* symbols are in same theory if there is an equation containing them at the root position */
    i = this.iterator();
    while(i.hasNext()) {
        TRSEquation eq = (TRSEquation)i.next();
        Set<SyntacticFunctionSymbol> setSameTheory = eq.getRootSymbols();
        Iterator j = setSameTheory.iterator();
        while(j.hasNext()) {
        SyntacticFunctionSymbol symb1 = (SyntacticFunctionSymbol)j.next();
        int index1 = ((Integer)indices.get(symb1)).intValue();
        Iterator k = setSameTheory.iterator();
        while(k.hasNext()) {
            SyntacticFunctionSymbol symb2 = (SyntacticFunctionSymbol)k.next();
            int index2 = ((Integer)indices.get(symb2)).intValue();
            sameTheory[index1 + size*index2] = true;
            sameTheory[index2 + size*index1] = true;
        }
        }
    }

    /* transitive closure */
    for(int y=0; y<size; y++) {
        for(int x=0; x<size; x++) {
        if(sameTheory[x + size*y]) {
            for(int z=0; z<size; z++) {
            if(sameTheory[y + size*z]) {
                sameTheory[x + size*z] = true;
            }
            }
        }
        }
    }

    /* construct signatures of subtheories */
    LinkedHashSet eqclasses = new LinkedHashSet();
    for(int s=0; s<size; s++) {
        Vector<SyntacticFunctionSymbol> eqclass = new Vector<SyntacticFunctionSymbol>();
        for(int t=0; t<size; t++) {
        if(sameTheory[s + size*t]) {
            eqclass.add(funs.elementAt(t));
        }
        }
        eqclasses.add(eqclass);
    }

    /* construct map */
    Map res = new LinkedHashMap();
    i = eqclasses.iterator();
    index = 0;
    while(i.hasNext()) {
        Vector<SyntacticFunctionSymbol> eqc = (Vector<SyntacticFunctionSymbol>)i.next();
        Iterator j = eqc.iterator();
        while(j.hasNext()) {
        res.put(j.next(), Integer.valueOf(index));
        }
        index++;
    }
    return res;
    }

    @Override
    public String toHTML() {
        StringBuffer result = new StringBuffer();
        Iterator i = this.iterator();
        while (i.hasNext()) {
            result.append(((TRSEquation) i.next()).toHTML());
            if (i.hasNext()) {
                result.append("<BR>");
            }
        }
        return result.toString();
    }

    @Override
    public String toLaTeX() {
        StringBuffer result = new StringBuffer();
        result.append("\\begin{longtable}{rcl}\n");
        Iterator i = this.iterator();
        while (i.hasNext()) {
            result.append(((TRSEquation) i.next()).toLaTeX());
            if (i.hasNext()) {
                result.append("\\\\ \n");
            }
        }
        result.append("\n\\end{longtable}\n");
        return result.toString();
    }

}
