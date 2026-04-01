package aprove.verification.dpframework.MCSProblem.mcnp;

import java.util.*;

/*
 * Numeric level mapping. Each program point has a number
 */

public class NumericMapping implements MCGraphMapping
{
    private Hashtable<String,Integer> _mappingHT = new Hashtable<String,Integer>();

    public NumericMapping(List<List<String>> elements)
    {
        int current = 0;
        for (Iterator<List<String>> it=elements.iterator(); it.hasNext(); ) {
            List<String> currentSCC = it.next();
            for (Iterator<String> it2=currentSCC.iterator(); it2.hasNext(); ) {
                String progPointID = it2.next();
                this._mappingHT.put(progPointID, current);
            }
            current++;
        }
    }

    public Integer getMapping(String progPointID)
    {
        if (this._mappingHT.containsKey(progPointID)) {
            return this._mappingHT.get(progPointID);
        } else {
            return null;
        }
    }

    @Override
    public String toString()
    {
        String res="Numeric Mapping:\n";

        for (Iterator<String> it=this._mappingHT.keySet().iterator(); it.hasNext(); ) {
            String progPointID = it.next();
            res = res + "   Program Point "+progPointID+" - "+this._mappingHT.get(progPointID)+"\n";
        }
        return res+"\n";
    }

}
