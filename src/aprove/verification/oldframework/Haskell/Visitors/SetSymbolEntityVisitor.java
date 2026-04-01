package aprove.verification.oldframework.Haskell.Visitors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Syntax.*;

 /**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The SetSymbolEntityVisitor walks through all entities ones
 * (it ignore the entities in the ignoreSet)
 * and sets the entity of each atom, by consideration of
 * the EntityFrames surrounding these atoms.
 * On the fly all raw terms are transformed to real terms with correct pixity,
 * and PreFunction are transformed to Functions, by calling
 * thier special transforming methods.
 * Also the type synonyms are collected in a type rule set and
 * it collects the free local variables in a QuantorExp
 * (the free local variables in a QuantorExp are the non-bounded ones)
 */

public class SetSymbolEntityVisitor extends HaskellVisitor{
    Stack<EntityFrame> curFrames;
    Set<HaskellEntity> ignoreSet;
    Set<HaskellBasicRule> typeRules;
    Module mainModule;
    int collectFree;

    public SetSymbolEntityVisitor(Set<HaskellEntity> ignoreSet, Set<HaskellBasicRule> typeRules,Module mainModule){
        this.ignoreSet = ignoreSet;
        this.typeRules = typeRules;
        this.curFrames = new Stack<EntityFrame>();
        this.mainModule = mainModule;
        this.collectFree = 1;
    }

    public void setModule(Module module){
        this.curFrames.push(module);
    }

    public Set<HaskellBasicRule> getTypeRules(){
        return this.typeRules;
    }

    @Override
    public HaskellObject caseModule(Module ho){
        DefaultDecl dd = ho.getDefaultDecl();
        if (dd != null){
           dd.addToModule();
           this.curFrames.push(ho);
           dd.visit(this);
           this.curFrames.pop();
        }
        return ho;
    }

    @Override
    public void fcaseEntityFrame(EntityFrame ho){
        this.curFrames.push(ho);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("CurFrame: "+ho);
        }
    }

    @Override
    public void icaseEntityFrame(EntityFrame ho){
        this.curFrames.pop();

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("LeaveCurFrame: "+ho);
        }
    }

    @Override
    public void fcaseQuantorExp(QuantorExp ho) {
    }

    @Override
    public void icaseQuantorExp(QuantorExp ho) {
        this.collectFree--;
    }

    @Override
    public HaskellObject caseQuantorExp(QuantorExp ho) {
        this.collectFree++;
        return ho;
    }

    @Override
    public void fcaseLambdaExp(LambdaExp ho) {
        this.collectFree++;
    }

    @Override
    public HaskellObject caseLambdaExp(LambdaExp ho) {
        this.collectFree--;
        return ho;
    }

    @Override
    public void fcaseAtom(Atom atom) {
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println(atom.getSymbol().getToken().getLine()+"#"+atom.getSymbol().getToken().getPos()+"."+atom.getSymbol().getName(false));
            /*if (atom.getSymbol().getToken() != null) {
               System.out.println(atom.getSymbol().getToken().getLine()+"#"+atom.getSymbol().getToken().getPos());
            } else {
               System.out.println("Intern#"+atom.getSymbol().getName(false));
            }*/
        }

        if (this.collectFree == 0) {
            if (atom instanceof Var){
                HaskellSym sym = atom.getSymbol();
                if (this.curFrames.peek().getFrameEntity(sym,((Var)atom).getSort()) == null){
                    HaskellEntity e = this.mainModule.getEntityN(sym,sym.getQualifier(),sym.getName(false),((Var)atom).getSort());
                    if (e == null){
                        e = new VarEntity(atom.getSymbol().getName(true),this.mainModule,null,null,true);
                        sym.setEntity(e);
                        this.curFrames.peek().addEntity(e);
                    }
                }
            }
        }
        atom.setEntityPer(this.curFrames.peek());
    }

    @Override
    public void fcaseInstFunction(InstFunction infu) {
        infu.setEntityPer(this.curFrames.peek());
    }


    @Override
    public boolean guardEntity(HaskellEntity ho){
        boolean ww = !(this.ignoreSet.contains(ho));

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("Cur Entity: "+ho);
            //System.out.println("Visit: "+ww);
        }

        return ww;
    }

    @Override
    public boolean guardDerivings(DataDecl ho){
        return true;
    }

    @Override
    public HaskellObject caseRawTerm(RawTerm rt) {
        return rt.correctPixity();
    }

    @Override
    public HaskellObject casePreFunction(PreFunction pf){
        return pf.createFunction();
    }

    @Override
    public HaskellObject caseSynTypeDecl(SynTypeDecl ho){
        this.typeRules.add(ho.buildTypeRule());
        return ho;
    }

 }
