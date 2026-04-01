package aprove.verification.oldframework.Haskell.Declarations;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * PatDecl represents a pattern declaration, which is expanded to simple pattern declarations.
 */
public class PatDecl extends SymObject implements HaskellDecl {
    protected HaskellPat pat;
    protected HaskellExp exp;
    protected List<FuncDecl> funcDecls;


    public PatDecl(HaskellSym sym,HaskellPat pat,HaskellExp exp){
        this(sym,pat,exp,new Vector<FuncDecl>());
    }

    public PatDecl(HaskellSym sym, HaskellPat pat,HaskellExp exp,List<FuncDecl> funcDecls){
        super(sym);
        this.pat = pat;
        this.exp = exp;
    this.funcDecls = funcDecls;
    }

    public HaskellPat getPattern(){
        return this.pat;
    }

    public HaskellExp getResultExpression(){
        return this.exp;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new PatDecl(Copy.deep(this.getSymbol()),Copy.deep(this.pat),Copy.deep(this.exp),Copy.deepCol(this.funcDecls)));
    }


    public List<FuncDecl> getFuncDecls(){
        return this.funcDecls;
    }


    /**
     * creates new FuncDecl name = exp which is used by addFuncDecl
     */
    public String startFuncDecl(){
    List<HaskellPat> pats = new Vector<HaskellPat>();
    Vector<HaskellObject> hos = new Vector<HaskellObject>();
    HaskellNamedSym sym = (HaskellNamedSym) this.getSymbol();
    hos.add(new Var(sym));
    this.funcDecls.add(new FuncDecl(sym,new RawTerm(hos),this.exp));
        String name = sym.getName(false);
        return name;
    }

    /**
     * expand the pattern declaration with a new fresh function declaration for
     * each founded variable (used by CollectEntityVisitor)
     */
    public void addFuncDecl(Var var,String name){
    List<HaskellPat> pats = new Vector<HaskellPat>();
    Vector<HaskellObject> hos = new Vector<HaskellObject>();
    HaskellNamedSym sym = (HaskellNamedSym) var.getSymbol();
    HaskellSym nSym = this.getNewSym(sym);
    hos.add(new Var(nSym)); // nSym Variable at begin of lhs
    SymVisitor sv = new SymVisitor();
    HaskellPat nPat = Copy.deep(this.pat);
    nPat = (HaskellPat)nPat.visit(sv);
    pats.add(nPat);
    this.funcDecls.add(new FuncDecl(nSym, // nSym must be the same as at the begin of lhs !!!
                                        new RawTerm(hos),
                                    new Apply(new PatLambdaExp(pats,new Var(this.getNewSym(sym))),
                                    new Var(new HaskellNamedSym("",name)))) );
    }

    /**
     * creates a structural copy of a symbol
     */
    private HaskellNamedSym getNewSym(HaskellNamedSym sym){
        return new HaskellNamedSym(sym.getQualifier(),sym.getNoQualName());
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcasePatDecl(this);
    if (hv.guardPatDecl(this)) {
           this.pat = this.walk(this.pat,hv);
    }
        if (hv.guardPatDeclSymbol(this)){
           this.setSymbol(this.walk(this.getSymbol(),hv));
        }
        hv.icasePatDecl(this);
        this.exp = this.walk(this.exp,hv);
        return hv.casePatDecl(this);
    }

    /**
     * copyies all Symbols structurally in a HaskellObject
     */
    public class SymVisitor extends HaskellVisitor{

    @Override
    public HaskellObject caseVar(Var var) {
        HaskellNamedSym sym = (HaskellNamedSym) var.getSymbol();
            return new Var(new HaskellNamedSym(sym.getQualifier(),sym.getNoQualName()));
    }
    }

}
