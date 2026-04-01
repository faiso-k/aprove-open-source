package aprove.verification.dpframework.MCSProblem.mcnp;

import java.util.*;

public class TaggedLevelMapping extends LevelMapping {

    // Stores tag for each variable in low or high set (per program point)
    // key=Program Point ID, value=Hashtable<Argument_Ind,tag>
    private Hashtable<String,Hashtable<Integer,Integer>> _argsTagsHT = new Hashtable<String,Hashtable<Integer,Integer>>();

    public TaggedLevelMapping(String type)
    {
        super(type);
    }

    public void addTag(String progPointID, int argument, int tag)
    {
        Hashtable<Integer,Integer> progPointArgsTags = null;
        if (this._argsTagsHT.containsKey(progPointID)) {
            progPointArgsTags = this._argsTagsHT.get(progPointID);
        } else {
            progPointArgsTags = new Hashtable<Integer,Integer>();
            this._argsTagsHT.put(progPointID, progPointArgsTags);
        }
        progPointArgsTags.put(argument, tag);
    }

    public String getTag(String progPointID, int argument)
    {
        Hashtable<Integer,Integer> progPointArgsTags = this._argsTagsHT.get(progPointID);
        if (progPointArgsTags.containsKey(argument)) {
            return ""+progPointArgsTags.get(Integer.valueOf(argument));
        } else {
            return "-";
        }
    }

    @Override
    public String toString()
    {
        String res="Tagged Level Mapping (type="+this._type+"):\n";
        res+=this.coverageToString();
        res+=this.progPointBoundNumberingToString();
        res+=this.progPointStrictNumberingToString();
        for (Iterator<String> it=this._argumentsFilteringHi.keySet().iterator(); it.hasNext(); ) {
            String progPointID = it.next();
            Set<Integer> argumentsHi = this._argumentsFilteringHi.get(progPointID);
            Set<Integer> argumentsLo = this._argumentsFilteringLo.get(progPointID);
            res = res + "   Program Point: " + progPointID+"\n"+"\tArguments: Low="+Arrays.toString(argumentsLo.toArray())+"; High="+Arrays.toString(argumentsHi.toArray())+"\n";
            res = res + "\tArguments Tags: ";
            if (this._argsTagsHT.containsKey(progPointID)) {
                Hashtable<Integer,Integer> progPointArgsTags = this._argsTagsHT.get(progPointID);
                Set<Integer> allArguments = new HashSet<Integer>();
                allArguments.addAll(argumentsHi);
                allArguments.addAll(argumentsLo);
                for (Iterator<Integer> it2=allArguments.iterator(); it2.hasNext(); ) {
                    Integer arg = it2.next();
                    if (progPointArgsTags.containsKey(arg)) {
                        Integer argTag = progPointArgsTags.get(arg);
                        res = res + "("+arg+","+argTag+") ";
                    } else {
                        res = res + "("+arg+","+"_"+") ";
                    }
                }
            }
            res = res + "\n";
        }
        res = res + "   Weakly ordered MC Graphs: "+Arrays.toString(this._graphsOrderedWeak.toArray())+"\n";
        if (Config.CUTSET_METHOD) {
            res = res + "   Strictly ordered MC Graphs: "+Arrays.toString(this._graphsOrderedStrict.toArray())+"\n";
            res = res + "   Anchors MC Graphs: "+Arrays.toString(this._graphsRemovable.toArray())+"\n";
            res = res + "   Bounded MC Graphs: "+Arrays.toString(this._graphsInCutset.toArray())+"\n";
        } else {
            res = res + "   Strictly ordered MC Graphs: "+Arrays.toString(this._graphsOrderedStrict.toArray())+"\n";
        }
        return res+"\n";
    }
}
