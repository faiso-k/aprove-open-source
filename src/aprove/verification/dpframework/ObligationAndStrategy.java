package aprove.verification.dpframework;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Parameters.*;

public class ObligationAndStrategy {

    ObligationNode root;
    Processor proc;
    StrategyProgram strategyProgram;
    List<BasicObligationNode> positions;

    //String inputName; // name of the used input (file name, ..)
    String pathName;  // name of path
    int index;

    //  Default constructor should only be used publicly by XML serialization.
    public ObligationAndStrategy() {

    }

    public ObligationAndStrategy(ObligationNode root, List<BasicObligationNode> positions, StrategyProgram strategyProgram, String name, int index) {
        this.root = root;
        this.positions = positions;
        this.strategyProgram = strategyProgram;
        this.pathName = name;
        this.index = index;
    }

    public ObligationNode getRoot() {
        return this.root;
    }

    public Processor getProcessor() {
        return this.proc;
    }

    public String getPathName() {
        return this.pathName;
    }

    public int getIndex() {
        return this.index;
    }

    public void setRoot(ObligationNode root) {
    this.root = root;
    }

    public void setProcessor(Processor proc) {
    this.proc = proc;
    }

    public void setPathName(String name) {
        this.pathName = name;
    }

    public void setIndex(int index) {
        this.index = index;
    }

    public StrategyProgram getStrategyProg() {
        return this.strategyProgram;
    }

    /**
     * Public getter method which should only be used by XMLEncoder.
     */
    public Processor getProc() {
        return this.proc;
    }

    /**
     * Public setter method which should only be used by XMLDecoder.
     */
    public void setProc(Processor proc) {
        this.proc = proc;
    }

    public List<BasicObligationNode> getPositions() {
        return this.positions;
    }

    public void setPositions(List<BasicObligationNode> positions) {
        this.positions = positions;
    }

//    public Result apply() {
//        ObligationNode oobl = this.obl;
//        Machine.theMachine.start(new ProcessorStrategy(this.proc), oobl);
//        throw new RuntimeException("processor do not directly return their result");
//    }



}
