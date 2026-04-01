package aprove.strategies.ExecutableStrategies;

import java.io.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.UserStrategies.*;

/**
 * Profiler for strategies. Executes a given strategy and writes the needed time
 * to the given file.
 * @author Andreas Kelle-Emden
 */
public class ExecProfileFile extends ExecutableStrategy {

    private ExecutableStrategy exStr;
    private boolean isWaiting = false;
    private String s;
    private long time = 0;
    private String filename;
    private FileOutputStream file;

    public ExecProfileFile(String filename, UserStrategy str, BasicObligationNode pos, RuntimeInformation rti) {
        super(rti);
        this.exStr    = str.getExecutableStrategy(pos, rti);
        this.filename = filename;
    }

    @Override
    ExecutableStrategy exec() {
        ExecutableStrategy retVal;
        if (!this.exStr.isNormal()) {
            if (!this.isWaiting) {
                this.time = -System.currentTimeMillis();
                this.s = this.exStr.toString();
                this.isWaiting = true;
            }
            ExecutableStrategy newEx = this.exStr.exec();
            if (newEx != null) {
                this.time += System.currentTimeMillis();
                String sOut = this.time + "\t" + this.s + "\t" + newEx + "\n";
                try{
                    this.file = new FileOutputStream(this.filename, true);
                    this.file.write(sOut.getBytes());
                    this.file.close();
                }
                catch(IOException e) {
                    System.err.println("Profiling file " + this.filename + " could not be opened!");
                }
                this.isWaiting = false;
            }
            if (newEx == null) {
                retVal =  null;
            } else {
                this.exStr = newEx;
                retVal =  this;
            }
        } else {
            retVal =  this.exStr;
        }
        return retVal;
    }

    @Override
    void stop(String reason) {
    }

    @Override
    public String toString() {
        return "Profile("+this.exStr+")";
    }

}
