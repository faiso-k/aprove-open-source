package aprove.verification.dpframework.MCSProblem.run;
import java.io.*;
import java.util.*;

import aprove.verification.dpframework.MCSProblem.mcnp.*;


/*
 * This class used to run one SCC program in separate thread
 * It saves how much time it took and alsol the bigtgest MCG.
 * In addition if so0me error/exception occured dujring the run  it also saved.
 */
public class RunnerThread extends Thread {

    private String biggestMCGSize = ""; //max number of edges per MCG (or NO_MCGsw if no MCGs)
    private boolean verify = false; //verikfy the ranking function
    private long time;
    private List<MCGraphMapping> rankingFunction = null;
    private Throwable error = null;
    private Program _program = null;

    public RunnerThread(File file) {
        this._program = Program.create(file.getAbsolutePath());
    }

    public RunnerThread(File file, boolean verify) {
        this(file);
        this.verify = verify;
    }

    public RunnerThread(Program program) {
        this._program = program;
    }

    public RunnerThread(Program program, boolean verify) {
        this(program);
        this.verify = verify;
    }


    @Override
    public void run() {
        long startTime = System.currentTimeMillis();
        try {
            this.biggestMCGSize = "0";
            if (this._program.getBiggestMCG()!=null) {
                this.biggestMCGSize = ""+this._program.getBiggestMCG().getNumOfEdges();
            } else {
                this.biggestMCGSize = "No_MCGs";
            }
            this._program.findLevelMappings();
            this.rankingFunction = this._program.getMcGraphsMappings();
            this.time = System.currentTimeMillis()-startTime;
            if (this.verify && this.rankingFunction!=null) {
                Verifier ver = new Verifier();
                ver.verify(this._program.getInitialMCGraphs(), this.rankingFunction);
            }
        } catch (Throwable t) {
            this.time = System.currentTimeMillis()-startTime;
            this.error=t;
        }
    }

    public List<MCGraphMapping> getRankingFunction() {
        return this.rankingFunction;
    }

    public long getTime() {
        return this.time;
    }

    public String getBiggestMCGSize() {
        return this.biggestMCGSize;
    }

    public boolean isErrorOccured() {
        return this.error!=null;
    }

    public Throwable getEerror() {
        return this.error;
    }

}
