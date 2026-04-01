package aprove.input.Programs.haskell;

import aprove.input.Generated.haskell.analysis.*;
import aprove.input.Generated.haskell.node.*;

/**
 * checks whether the current module is compatible to the simple version
 * of the Prelude, where nothing is predefined.
 * This is the case if the only import is "import qualified Prelude [as SomeName]"
 * and no qualified reference is found.
 *
 */
public class HaskellSimplePreludeAnalyzer extends DepthFirstAdapter {


    /**
     * stores whether a switch to simple Prelude could be performed
     */
    private boolean simplePreludeCompatible;

    /**
     * stores whether there was an import
     */
    private boolean hasImports;


    public HaskellSimplePreludeAnalyzer() {
        this.simplePreludeCompatible = true;
        this.hasImports = false;
    }


    /**
     * @return whether this module is compatible with the simple Prelude
     */
    public boolean isSimplePreludeCompatible() {
        return this.simplePreludeCompatible && this.hasImports;
    }


    private void updateSimplePreludeCompat(Token node) {
        if (this.simplePreludeCompatible) {
            this.simplePreludeCompatible = node.getText().indexOf('.') < 0;
        }
    }


    @Override
    public void caseTConid(TConid node)           { this.updateSimplePreludeCompat(node); }
    @Override
    public void caseTQqconid(TQqconid node)       { this.updateSimplePreludeCompat(node); }
    @Override
    public void caseTConsym(TConsym node)         { this.updateSimplePreludeCompat(node); }
    @Override
    public void caseTQqconsym(TQqconsym node)     { this.updateSimplePreludeCompat(node); }
    @Override
    public void caseTVarid(TVarid node)           { this.updateSimplePreludeCompat(node); }
    @Override
    public void caseTQqvarid(TQqvarid node)       { this.updateSimplePreludeCompat(node); }
    @Override
    public void caseTVarsympre(TVarsympre node)   { this.updateSimplePreludeCompat(node); }
    @Override
    public void caseTQqvarsym(TQqvarsym node)     { this.updateSimplePreludeCompat(node); }
    @Override
    public void outAMinusVarsym(AMinusVarsym node){ this.updateSimplePreludeCompat(node.getMinus()); }
    @Override
    public void outAExclaVarsym(AExclaVarsym node){ this.updateSimplePreludeCompat(node.getExcla()); }

    @Override
    public void  inAImpdecl(AImpdecl node){
        this.hasImports = true;
        if (this.simplePreludeCompatible) {
            boolean isQualified = node.getKwqualified() != null;
            boolean isPrelude = node.getConid().getText().equals("Prelude");
            this.simplePreludeCompatible = isQualified & isPrelude;
        }
    }


    @Override
    public void caseTLopen(TLopen node) {
        this.simplePreludeCompatible = false;
    }


    @Override
    public void caseACharLiteral(ACharLiteral node) {
        this.simplePreludeCompatible = false;
    }


    @Override
    public void caseAIntegerLiteral(AIntegerLiteral node) {
        this.simplePreludeCompatible = false;
    }

    @Override
    public void caseAFloatLiteral(AFloatLiteral node) {
        this.simplePreludeCompatible = false;
    }


    @Override
    public void caseAStringLiteral(AStringLiteral node) {
        this.simplePreludeCompatible = false;
    }
}
