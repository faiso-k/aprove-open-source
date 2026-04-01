package aprove.verification.oldframework.Rewriting.Transformers;
import java.math.*;
import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Programs.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TRSProblem.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.theoremprover.TerminationProcedures.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/** Transforms a conditional Program into an unconditional program.
 * <p>
 * Enno Ohlebusch, "Advanced Topics in Term Rewriting", p. 212
 * @author Stephan Falke
 * @version $Id$
 */
@NoParams
public class ConditionalTransformer extends TRSProcessor {
    /* tymap :: NewIfSymbols -> VektorOfTerms(retTy,t1,..,tn)
     * retTy = return type term
     * ti = argument type terms
     */
    private Program newProg;
    private Map tymap;
    private Map maxUsedNumbers;
    private List signature;
    private Set<Rule> newR;
    private Vector<Rule> helperR;
    private Collection<Rule> R;
    private TypeContext typeContext;
    /** A hashtable that assigns a bitfield to a (helper)function-name
     *  representing whether the variable is important or not.
     */
    private Hashtable neededFunctArgs;

    public static ConditionalTransformer create() {
        return new ConditionalTransformer();
    }

    public Program transform(Program prog) {
//      if (prog.getStrategy() != Program.NONE) {
        boolean innermost = prog.getStrategy() == Program.INNERMOST;
        if (innermost && !prog.isInnermostQuasiDecreasingnessCompatible()) {
            return null;
        }
        if (!innermost && prog.getStrategy() != Program.ALL) {
            return null;
        }
//      }
        try {
            prog = this.itransform(prog);
        } catch (Exception e){
            e.printStackTrace();
        }
        return prog;
    }

    public Program itransform(Program prog) {
//      System.out.println(prog.toString());
        this.signature = prog.getSignature();
        this.maxUsedNumbers = new HashMap();
        this.R = prog.getRules();
        this.newR = new LinkedHashSet<Rule>();
        this.helperR = new Vector<Rule>();
        this.neededFunctArgs = new Hashtable();
        if (prog.getTypeContext() != null) {
            this.typeContext = prog.getTypeContext().deepcopy();
        } else {
            this.typeContext = null;
        }
        this.tymap = new HashMap();
        this.fillNumbers();

        Iterator i = this.R.iterator();
        while(i.hasNext()) {
            Rule rule = (Rule)i.next();
            if(rule.getConds().isEmpty()) {
                /* unconditional rule */
                this.newR.add(rule);
            }
            else {
                this.translate(rule);
            }
        }
        this.deleteUnneededArgs();
        this.buildTypes();

        prog.setType(AbstractProgram.CONDITIONAL);
        Program    nprog = Program.create(this.newR, prog, AbstractProgram.DEFAULT);
        nprog.setTypeContext(this.typeContext);
        boolean nonOverlap = nprog.isNonOverlapping();
        boolean complete = prog.isComplete();
        if (nonOverlap) {
            nprog.setStrategy(Program.INNERMOST);
            nprog.setComplete(complete);
        } else {
            nprog.setStrategy(prog.isFromProlog() ? Program.INNERMOST : prog.getStrategy());
            nprog.setComplete(prog.isFromProlog() ? complete : false);
        }
//      System.out.println(nprog.toString());
//      System.out.println(typeContext.toString());
        return nprog;
    }


    private void translate(Rule rule) {
        AlgebraTerm l = rule.getLeft();
        AlgebraTerm r = rule.getRight();
        List<Rule> conds = rule.getConds();
        TypeAssumption.TypeAssumptionSkeleton varTa = new TypeAssumption.TypeAssumptionSkeleton();
        AlgebraTerm retTy = TypeCheckerVisitor.getRetAndBuildAssumption(this.typeContext,rule,varTa);

        // Delete conditions which have a new variable at the rhs and
        // make apropriate substitutions.
        /* This is only correct if certain requirements are met.
         * We still need to check which requirements are sufficient.
         Set<Variable> oldVars = new HashSet<Variable>();
         oldVars.addAll(l.getVars());
         List<Rule> conds2 = new Vector<Rule>();
         Vector<Substitution> subs = new Vector<Substitution>();
         Iterator cond_it = conds.iterator();
         while(i.hasNext()) {
         Rule cond = (Rule)cond_it.next();
         Term s = cond.getLeft();
         Term t = cond.getRight();
         // check whether it is sufficient to use a substitution.
          if (t.isVariable() && !oldVars.contains(t)) {
          Substitution sub = Substitution.create();
          sub.put(((Variable)t).getVariableSymbol(), s);
          subs.insertElementAt(sub, 0);
          }
          else {
          Iterator sub_it = subs.iterator();
          while (sub_it.hasNext()) {
          Substitution sub = (Substitution)sub_it.next();
          s = s.apply(sub);
          t = t.apply(sub);
          }
          conds2.add(Rule.create(s, t));
          oldVars.addAll(t.getVars());
          }
          }
          Iterator sub_it = subs.iterator();
          while (sub_it.hasNext()) {
          Substitution sub = (Substitution)sub_it.next();
          r = r.apply(sub);
          }
          conds = conds2;
          */

        // calculate which variables are needed when
        Set<AlgebraVariable> curNeededVars = new HashSet<AlgebraVariable>(r.getVars());
        Stack neededVars = new Stack();
        for (int j=conds.size()-1; j>=0; j--) {
            Rule cond = conds.get(j);
            curNeededVars.addAll(cond.getRight().getVars());
            neededVars.push(new HashSet<AlgebraVariable>(curNeededVars));
            curNeededVars.addAll(cond.getLeft().getVars());
        }

        Sort sort = l.getSort();
        DefFunctionSymbol symbol = (DefFunctionSymbol)l.getSymbol();

        String name = symbol.getName();
        Vector<AlgebraVariable> rVars = new Vector<AlgebraVariable>();
        Vector<Sort> rSorts = new Vector<Sort>();
        int leftIndex = 0;
        int rightIndex = ((Integer)this.maxUsedNumbers.get(name)).intValue() + 1;
        AlgebraTerm lastT = null;
        AlgebraTerm lastTy = null;

        // Make the non-conditional rules (without superfluous variables).
        Iterator i = conds.iterator();
        while(i.hasNext()) {
            Rule cond = (Rule)i.next();
            AlgebraTerm s = cond.getLeft();
            AlgebraTerm t = cond.getRight();
            Sort sSort = s.getSort();
            AlgebraTerm coTy = TypeCheckerVisitor.combinedTypeTerm(this.typeContext,s,t);
            Vector<AlgebraTerm> rArgs = null;
            AlgebraTerm newLeft = null;
            IfSymbol rightSymbol = null;
            if (lastT == null) {
                /* add l -> if_1_rule(Var(l), s_1) */
                rVars = this.getVars(l);
                newLeft = l;
            }
            else {
                /* add if_j_rule(Var(l,t_1,...,t_(j-1)),t_j)
                 ->  if_(j+1)_rule(Var(l,t_1,...,t_(j-1),t_j),s_(j+1)) */
                Vector<AlgebraVariable> lVars = new Vector<AlgebraVariable>(rVars);

                this.merge(rVars, this.getVars(lastT));
                Vector<Sort> lSorts = this.getSorts(lVars);
                lSorts.add(lastT.getSort());
                Vector<AlgebraTerm> lArgs = new Vector<AlgebraTerm>(lVars);
                lArgs.add(lastT);

                DefFunctionSymbol leftSymbol = IfSymbol.create(name, leftIndex, lSorts, sort);
                newLeft = AlgebraFunctionApplication.create(leftSymbol, lArgs);
            }
            rArgs = new Vector<AlgebraTerm>(rVars);
            rArgs.add(s);
            rSorts = this.getSorts(rVars);
            rSorts.add(sSort);
            rightSymbol = IfSymbol.create(name, rightIndex, rSorts, sort);
            this.addToTyMap(rightSymbol,varTa,rVars,coTy,retTy);
            AlgebraTerm newRight = AlgebraFunctionApplication.create(rightSymbol, rArgs);
            Rule newRule = Rule.create(newLeft, newRight);

            int identified = this.identify(newRule);
            if(identified > 0) {
                rightIndex = identified;
            } else {
                this.newR.add(newRule);
                this.maxUsedNumbers.put(name, Integer.valueOf(rightIndex));
            }

            String sname = IfSymbol.createName(name, rightIndex);
            curNeededVars = (Set<AlgebraVariable>)neededVars.pop();
            for (int j=rVars.size()-1; j>=0; j--) {
                if (curNeededVars.contains(rVars.get(j))) {
                    this.setArgNeeded(sname, j);
                }
            }
            this.setArgNeeded(sname, rVars.size());  // coTy
            leftIndex = rightIndex;
            rightIndex = ((Integer)this.maxUsedNumbers.get(name)).intValue() + 1;
            lastT = t;
            lastTy = coTy;
        }

        AlgebraTerm newLeft = null;
        if (lastT == null) {
            newLeft = l;
        } else {
            /* add if_n_rule(Var(l,t_1,...,t_(n-1)), t_n) -> r*/
            Vector<Sort> lSorts = this.getSorts(rVars);
            lSorts.add(lastT.getSort());

            Vector<AlgebraTerm> lArgs = new Vector<AlgebraTerm>(rVars);
            lArgs.add(lastT);

            DefFunctionSymbol leftSymbol = IfSymbol.create(name, leftIndex, lSorts, sort);
            newLeft = AlgebraFunctionApplication.create(leftSymbol, lArgs);
        }
        AlgebraTerm newRight = r;
        Rule newRule = Rule.create(newLeft, newRight);

        this.newR.add(newRule);
        return;
    }

    /**
     * build up the types of the new created if-symbols
     * under consideration of the needed function arguments
     * and update the typecontext
     */
    private void buildTypes(){
        if (this.typeContext == null) { return; }
        Iterator it = this.tymap.entrySet().iterator();
        while (it.hasNext()) {
            Map.Entry sl= (Map.Entry)it.next();
            IfSymbol ifsym = (IfSymbol) sl.getKey();
            BigInteger active = (BigInteger)this.neededFunctArgs.get(ifsym.getName());
            if (active != null) {
                Vector<AlgebraTerm> vot = (Vector<AlgebraTerm>) sl.getValue();
                AlgebraTerm retTy = vot.get(0);
                Vector<AlgebraTerm> nvot = new Vector<AlgebraTerm>();
                Vector<Sort> sorts = new Vector<Sort>();
                for (int i=0; i<vot.size();i++){
                    if (active.testBit(i)) {
                        nvot.add(vot.get(i+1)); //ignore the retTy
                        sorts.add(ifsym.getArgSort(i));
                    }
                }

                IfSymbol nIfsym = IfSymbol.create(ifsym.getShortName(),
                        ifsym.getNumber(),sorts, ifsym.getSort());
                Type ct = TypeTools.autoQuan(TypeTools.function(nvot,retTy));
                this.typeContext.setSingleTypeOf(nIfsym,ct);
            }
        }
    }

    /** Deletes the unneeded arguments in the newly created functions.
     */
    private void deleteUnneededArgs() {
        Set<Rule> myNewR = new LinkedHashSet<Rule>();
        Iterator it = this.newR.iterator();
        while (it.hasNext()) {
            Rule rule = (Rule)it.next();
            AlgebraTerm left = rule.getLeft();
            AlgebraTerm right = rule.getRight();
            myNewR.add(Rule.create(this.filter(left), this.filter(right)));
        }
        this.newR = myNewR;
    }

    /** Filters a term according to the bit-fields that describe the
     *  needed arguments.
     */
    private AlgebraTerm filter(AlgebraTerm t) {
        Symbol sym = t.getSymbol();
        if (! (sym instanceof DefFunctionSymbol)) {
            return t;
        }
        BigInteger i = (BigInteger)this.neededFunctArgs.get(sym.getName());
        int arity = ((SyntacticFunctionSymbol)sym).getArity();
        if (i == null || i.equals(BigInteger.ONE.shiftLeft(arity).subtract(BigInteger.ONE))) {
            return t;
        }
        List<Sort> sorts = new Vector<Sort>();
        List<AlgebraTerm> args = new Vector<AlgebraTerm>();
        for (int j=0; j<arity; j++) {
            if (i.testBit(j)) {
                sorts.add(((SyntacticFunctionSymbol)sym).getArgSort(j));
                args.add(t.getArgument(j));
            }
        }
        IfSymbol ifsym = (IfSymbol)sym;
        DefFunctionSymbol def = IfSymbol.create(ifsym.getShortName(), ifsym.getNumber(), sorts, sym.getSort());
        return AlgebraFunctionApplication.create(def, args);
    }

    /**************************/

    private void fillNumbers() {
        Iterator i = this.signature.iterator();

        /* initialize with 0's */
        while(i.hasNext()) {
            String name = (String)i.next();
            this.maxUsedNumbers.put(name, Integer.valueOf(0));
        }

        /* scan the signature */
        i = this.signature.iterator();
        while(i.hasNext()) {
            String name = (String)i.next();
            String ifName = IfSymbol.PREFIX + name + IfSymbol.INFIX;
            int ifNameLength = ifName.length();
            Iterator j = this.signature.iterator();
            while(j.hasNext()) {
                String testName = (String)j.next();
                if(testName.startsWith(ifName)) {
                    /* let's see weather the rest of testName is a number */
                    try {
                        int nr = Integer.parseInt(testName.substring(ifNameLength));
                        int oldNr = ((Integer)this.maxUsedNumbers.get(name)).intValue();
                        if(oldNr < nr) {
                            this.maxUsedNumbers.put(name, Integer.valueOf(nr));
                        }
                    }
                    catch(NumberFormatException e) {
                        /* no number */
                    }
                }
            }
        }

        /* increment to the next multiple of 10 */
        i = this.signature.iterator();
        while(i.hasNext()) {
            String name = (String)i.next();
            int value = ((Integer)this.maxUsedNumbers.get(name)).intValue();
            if(value != 0 && ((value % 10) == 0)) {
                value++;
            }
            double doubleValue = Double.valueOf(value).doubleValue();
            int newValue = 10 * Double.valueOf(Math.ceil(doubleValue / 10.0)).intValue();
            this.maxUsedNumbers.put(name, Integer.valueOf(newValue));
        }

        return;
    }

    private int identify(Rule rule) {
        Iterator i = this.newR.iterator();
        AlgebraTerm right = rule.getRight();
        IfSymbol rightSymbol = (IfSymbol)right.getSymbol();
        List<AlgebraTerm> rightArguments = right.getArguments();
        while(i.hasNext()) {
            Rule testRule = (Rule)i.next();
            if(testRule.getLeft().equals(rule.getLeft())) {
                AlgebraTerm testRight = testRule.getRight();
                if(testRight.getSymbol() instanceof IfSymbol) {
                    IfSymbol testRightSymbol = (IfSymbol) testRight.getSymbol();
                    if(rightSymbol.getShortName().equals(testRightSymbol.getShortName())) {
                        if(rightArguments.equals(testRight.getArguments())) {
                            /* we can identify the symbols */
                            return testRightSymbol.getNumber();
                        }
                    }
                }
            }
        }

        return -1;
    }

    private void merge(Vector<AlgebraVariable> l, Vector<AlgebraVariable> r) {
        Iterator i = r.iterator();
        while(i.hasNext()) {
            AlgebraVariable v = (AlgebraVariable)i.next();
            if(!l.contains(v)) {
                l.add(v);
            }
        }
        return;
    }

    private Vector<AlgebraVariable> getVars(AlgebraTerm t) {
        Vector<AlgebraVariable> res = new Vector<AlgebraVariable>();
        if(t.isVariable()) {
            res.add((AlgebraVariable) t);
        }
        else {
            Iterator i = t.getArguments().iterator();
            while(i.hasNext()) {
                this.merge(res, this.getVars((AlgebraTerm)i.next()));
            }
        }
        return res;
    }

    private Vector<Sort> getSorts(List<AlgebraVariable> vars) {
        Vector<Sort> res = new Vector<Sort>();
        Iterator i = vars.iterator();
        while(i.hasNext()) {
            res.add(((AlgebraVariable)i.next()).getSort());
        }
        return res;
    }

    private void addToTyMap(IfSymbol ifsym, TypeAssumption.TypeAssumptionSkeleton ta,List<AlgebraVariable> vars,AlgebraTerm coTy,AlgebraTerm retTy){
        if (this.typeContext == null) { return; }
        Vector<AlgebraTerm> vot = new Vector<AlgebraTerm>();
        vot.add(retTy);
        Iterator i = vars.iterator();
        while (i.hasNext()){
            Type ct = ta.getSingleTypeOf(((AlgebraVariable)i.next()).getVariableSymbol());
            vot.add(ct.getTypeMatrix());
        }
        if (coTy!=null) {
            vot.add(coTy);
        }
        this.tymap.put(ifsym,vot);
    }

    private void setArgNeeded(String name, int i) {
        BigInteger bits = (BigInteger)this.neededFunctArgs.get(name);
        BigInteger newbits;
        // null (no entry) should be treated like a zero.
        newbits = (bits == null ? BigInteger.ZERO : bits).setBit(i);
        this.neededFunctArgs.put(name, newbits);
    }

    @Override
    protected Result processProgram(TRS trs, Abortion aborter) throws AbortionException {
        Program prog = trs.getProgram();
        if (prog.isEquational() || !prog.isConditional()) {
            return ResultFactory.notApplicable("Transformation from CTRS to TRS is not applicable.");
        }
        this.newProg = this.transform(prog);
        if (this.newProg == null) {
            return ResultFactory.notApplicable("Transformation from CTRS to TRS is not applicable.");
        } else {
            TRS newTRS = new TRS(this.newProg, trs.getInnermost());
            return ResultFactory.proved(newTRS, this.computeImplication(trs), new CTRStoTRSProof(trs,newTRS));
        }
    }

    @Override
    public boolean isEquationalAble() {
        return true;
    }

    public Implication computeImplication(TRS obl) {
        return (this.newProg!=null) && this.newProg.isNonOverlapping() ? YNMImplication.EQUIVALENT : YNMImplication.SOUND;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (!(obl instanceof TRS)) {
            return false;
        }
        TRS trs = (TRS) obl;
        if (!trs.isConditional()) { // no conditional
            return false;
        }
        if (!trs.getProgram().isDeterministic()) { // and no free vars on lhs
            return false;
        }
        if (trs.isEquational() && !this.isEquationalAble()) {
            return false;
        }
        return true;
    }

}
