package aprove.verification.oldframework.Haskell.Transformations;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


/**
 *
 * Adds for every data type the corresponding instance of LazyTermination
 *
 *
 * @author matraf
 * @version $Id$
 *
 */
public class LazyReduction extends BasicReduction {

    private Set<DerivedInstEntity> lazyInstances = new HashSet<DerivedInstEntity>();

    @Override
    public HaskellObject caseEntity(HaskellEntity ho) {
        if (ho instanceof TyConsEntity) {
            TyConsEntity tcoe = (TyConsEntity)ho;

            if (tcoe == this.prelude.getTypeArrow()) {
                return super.caseEntity(ho);
            }

            // XXX DEBUG
            if (aprove.Globals.DEBUG_MATRAF) {
                System.out.println("TyCons: "+tcoe.getName());

                System.out.println("\tlazy Zero x = True");

                for(ConsEntity consEntity : tcoe.getConsList()) {
                    StringBuilder sb = new StringBuilder();
                    StringBuilder tail = new StringBuilder();
                    String andStr = "";
                    String prefix = "lazy n ";
                    for(int i=0;i<consEntity.getArity(); ++i) {
                        sb.append(" ");
                        sb.append("x"+i);
                        tail.append(andStr).append(prefix).append("x").append(i);
                        andStr = " && ";
                    }
                    System.out.print("\t");
                    String constrName = consEntity.getName();
                    if (consEntity.isInfix()) {
                        constrName = "("+constrName+")";
                    }
                    String resString = tail.toString();
                    if (resString.length() == 0) {
                        resString = "True";
                    }
                    System.out.println("lazy (Succ n) ("+constrName+sb.toString()+") = "+resString);
                }
            }
            // XXX END OF DEBUG

            DataDecl dd = (DataDecl) tcoe.getValue();
            TypeSchema ts;
            if (dd == null) {

                // this should only occur for Prelude hardcoded types, such as Bool, Tuples, Lists
                ts = null;

                if (tcoe == this.prelude.getBool()) {
                    ts = this.prelude.getBoolTypeSchema();
                }
                else if (tcoe == this.prelude.getList()) {
                    Var tyvar = Var.createFreshVar();
                    HaskellType listCons = new Cons(new HaskellNamedSym(this.prelude.getList()));
                    ts = TypeSchema.create(new Apply(listCons, tyvar));
                    ts.autoQuantor();
                }
                else if (tcoe.getConsList().get(0).getTuple() >= 0) {
                    List<HaskellType> hts = new ArrayList<HaskellType>();
                    hts.add(new Cons(new HaskellNamedSym(tcoe)));
                    for (int i=0; i<tcoe.getConsList().get(0).getTuple(); ++i) {
                        hts.add(Var.createFreshVar());
                    }
                    ts = TypeSchema.create((HaskellType)HaskellTools.buildApplies(hts));
                    ts.autoQuantor();
                }


                if (ts == null) {
                    throw new RuntimeException("could not find predef type for "+tcoe.getName());
                }
            }
            else {
                ts = dd.getTypeSchema();
            }
            HaskellSym lazyClassSym = new HaskellNamedSym("", "LazyTermination");
            lazyClassSym.setEntity(this.prelude.getEntity(lazyClassSym, HaskellEntity.Sort.TYCLASS));
            Set<DerivedInstEntity> derivedInstEntities = this.prelude.generateDerivedInstEntities(tcoe, dd, ts, Arrays.asList(lazyClassSym), tcoe.getModule());
            this.lazyInstances.addAll(derivedInstEntities);

        }

        return super.caseEntity(ho);
    }


    public static boolean applyTo(Modules modules, Abortion aborter){
        if (modules.getPrelude().isSimplePrelude()) {
            // not applicable in simple mode
            return false;
        }

        LazyReduction br = new LazyReduction();
        br.setAborter(aborter);
        br.prelude = modules.getPrelude();

        br.forModules(modules);

        TypeInferenceVisitor tiv = new TypeInferenceVisitor(modules.getPrelude(), modules.getAssumptions(), modules.getClassConstraintGraph());

        for(Pair<Module,HaskellEntity> mhe : modules.getPrelude().getAndClearLazyGenFuncs()) {
            TypeSchema type = (TypeSchema) tiv.forTerm(mhe.y, mhe.x);
            modules.getAssumptions().pushAssumption(mhe.y, type);
            mhe.x.addEntity(mhe.y);
        }

        // setting the types and adding to module
        for(DerivedInstEntity die : br.lazyInstances) {
            modules.getMainModule().addEntity(die);
            tiv.forTerm(die, modules.getMainModule());

            for (HaskellEntity he : die.getSubEntities()) {
                Function func = ((InstFunction)he.getValue()).getFunction();
                HaskellRule rule = func.getRules().iterator().next();
                List<HaskellType> hts = HaskellTools.getTypeTerms(rule.getPatterns());
                hts.add(rule.getExpression().getTypeTerm());
                HaskellType newType = (HaskellType)modules.getPrelude().buildArrows(hts);
                TypeSchema ts = TypeSchema.create(newType);
                ts.autoQuantor();
                modules.getAssumptions().pushAssumption(he, ts);
            }
        }

        //changeStartTerms(modules, modules.getStartTerms());

        return true; // the program was changed
    }



    public static void changeStartTerms(Modules modules, Collection<Pair<HaskellObject, HaskellExp>> starttermsForChange) {
        List<Pair<HaskellObject, HaskellExp>> newStartTerms = new ArrayList<Pair<HaskellObject,HaskellExp>>();

        for(Pair<HaskellObject, HaskellExp> typedterm : modules.getStartTerms()) {

            if (starttermsForChange.contains(typedterm)) {
                TypeSchema ts = (TypeSchema) typedterm.x;
                QuantorExp startterm = (QuantorExp) typedterm.y;

                // automatically add lazyGenerator until the outermost arity is completed
                //startterm.setResult(varExp(modules, startterm.getResult()));

                HaskellEntity lazyT = modules.getPrelude().getEntity(null, "", "lazyTerminating", HaskellEntity.Sort.VAR);

                VarEntity ne = new VarEntity(modules.getPrelude().getFreshNameFor("n"),modules.getMainModule(),null,null,true);
                startterm.getEntityFrame().addEntity(ne);

                startterm.setResult(new Apply(new Apply(new Var(new HaskellNamedSym(lazyT)), new Var(new HaskellNamedSym(ne))), startterm.getResult()));
                typedterm.y = startterm;
                typedterm.x = modules.checkTerm(typedterm.y);
            }

            newStartTerms.add(typedterm);
        }
        modules.setStartTerms(newStartTerms);
    }

    /*
    private static HaskellExp varExp(Modules modules, HaskellExp term) {
        List<HaskellObject> hos = HaskellTools.applyFlatten(term);

        HaskellObject head = hos.get(0);

        int diff = 0;

        if (head instanceof Cons) {
            Cons cons = (Cons) head;
            ConsEntity ce = (ConsEntity) cons.getSymbol().getEntity();
            diff = ce.getArity() - hos.size() +1; // +1 accounts for the constructor
        }
        else if (head instanceof Var) {
            Var v = (Var) head;
            VarEntity ve = (VarEntity) v.getSymbol().getEntity();
            if (!ve.getLocal()) {
                diff = getTypeArity(modules, ve) - hos.size() +1; // 1 accounts for the function
            }
        }
        else {
            // should never happen
            throw new RuntimeException("Entity "+head+" should not be here...");
        }

        HaskellEntity lazyG = modules.getPrelude().getEntity(null, "", "lazyGenerator", HaskellEntity.Sort.VAR);

        for(int i=0;i<diff;++i) {
            //VarEntity ve = new VarEntity(modules.getPrelude().buildUniqueName(),modules.getMainModule(), null, null, true);
            //hos.add(new Var(new HaskellNamedSym(ve)));
            hos.add(new Var(new HaskellNamedSym(lazyG)));
        }

        return (HaskellExp) HaskellTools.buildApplies(hos);
    }


    private static int getTypeArity(Modules modules, HaskellEntity e){
       int typeArity = 0;
       TypeSchema ts = modules.getAssumptions().getTypeSchemaFor(e);
       List<HaskellType> types = modules.getPrelude().deArrow(ts.getMatrix());
       typeArity = types.size()-1;
       return typeArity;
    }
    */
}
