package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import java.io.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.dpframework.*;

public abstract class CpxIntTrsExportProcessor extends CpxIntTrsProcessor {

    protected abstract void export(CpxIntTrsProblem obl, Appendable o) throws IOException;

    @Override
    public Result processCpxIntTrs(
        CpxIntTrsProblem obl,
        BasicObligationNode oblNode,
        Abortion aborter,
        RuntimeInformation rti) throws AbortionException
    {
        String fn = System.getenv().get("OUTPUTFILE");
        if (fn == null) {
            throw new RuntimeException("$OUTPUTFILE must be set to use this processor");
        }
        FileWriter o = null;
        try {
            // We use a StringBuilder, because we want to avoid writing
            // something if the obligation is not exportable for some reason.
            StringBuilder sb = new StringBuilder();
            this.export(obl, sb);
            o = new FileWriter(new File(fn));
            o.append(sb.toString());
        } catch (IOException e) {
            throw new RuntimeException(e);
        } finally {
            if (o != null) {
                try {
                    o.close();
                } catch (IOException e) {
                    // couldn't close?
                    throw new RuntimeException(e);
                }
            }
        }

        return ResultFactory.unsuccessful();
    }

    @Override
    boolean isCpxIntTrsApplicable(CpxIntTrsProblem obl) {
        return true;
    }

}
