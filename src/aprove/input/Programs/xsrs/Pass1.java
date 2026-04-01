package aprove.input.Programs.xsrs;

import java.util.*;

import aprove.input.Generated.xsrs.node.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** Treewalker that implements the first pass of
 *  the AST conversion.
 *  <p>
 *  This pass basically just picks up all defined functions.
 * @author Peter Schneider-Kamp, Stephan Falke
 * @version $Id$
 */

class Pass1 extends Pass {

    private boolean haveLeftMost = false;
    private boolean haveRightMost = false;

    @Override
    public void inALeftmostStrategydecl(ALeftmostStrategydecl node) {
        this.haveLeftMost = true;
    }

    @Override
    public void inARightmostStrategydecl(ARightmostStrategydecl node) {
        this.haveRightMost = true;
    }

    @Override
    public void inASimpleRule(ASimpleRule node) {
    AWord w = (AWord)node.getLeft();
    String name = this.chop(((AIdi)w.getIdi().get(0)).getId());
        DefFunctionSymbol f;
        f = this.prog.getDefFunctionSymbol(name);
        if (f == null) {
            f = DefFunctionSymbol.create(name, new Vector<Sort>(), this.poly);
            f.addArgSort(this.poly);
            try {
                this.prog.addDefFunctionSymbol(f);
                this.prog.setFunctionSignature(f, Symbol.MAINSIG);
            } catch (ProgramException e) {}
        }
    }

    @Override
    public void inACollapseRule(ACollapseRule node) {
    AWord w = (AWord)node.getLeft();
    String name = this.chop(((AIdi)w.getIdi().get(0)).getId());
        DefFunctionSymbol f;
        f = this.prog.getDefFunctionSymbol(name);
        if (f == null) {
            f = DefFunctionSymbol.create(name, new Vector<Sort>(), this.poly);
            f.addArgSort(this.poly);
            try {
                this.prog.addDefFunctionSymbol(f);
                this.prog.setFunctionSignature(f, Symbol.MAINSIG);
            } catch (ProgramException e) {}
        }
    }

    public void checkStrategy() {
        if (this.haveLeftMost) {
            if (this.haveRightMost) {
                this.prog.setStrategy(Program.NONE);
                this.prog.setComplete(false);
            } else {
                this.prog.setStrategy(Program.ALL);
                this.prog.setComplete(false);
            }
        } else if (this.haveRightMost) {
            this.prog.setStrategy(Program.INNERMOST);
            this.prog.setComplete(true);
        }
    }

}
