package aprove.input.Programs.llvm.utils;

import java.io.*;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.TimeZone;

import org.apache.commons.codec.digest.DigestUtils;

import aprove.*;
import aprove.verification.oldframework.Logic.*;

public final class GraphMLFormatter {

    private static boolean hasSink = false;
    
    public static String calcSHA256(File file) throws FileNotFoundException, IOException {
        return DigestUtils.sha256Hex(new FileInputStream(file));
    }

    /**
     * @param source The state where the edge starts.
     * @param target The state where the edge ends.
     * @return A string representing the witness edge.
     */
    public static String createWitnessEdge(CState source, CState target, YNM control) {
        return
                edge(
                        source.getNodeID(),
                        target.getNodeID(),
                        target.isLoopHead(),
                        source.getCLine(),
                        source.getCLine(),
                        source.getSourceCode(),
                        control,
                        source.isEntry() ? source.getFunctionName() : null
                );
    }
    
    public static String createSinkEdge(CState source, YNM control) {
        return
                edgeToSink(
                           source.getNodeID(),
                           false,
                           source.getCLine(),
                           source.getCLine(),
                           source.getSourceCode(),
                           control,
                           source.isEntry() ? source.getFunctionName() : null
                   );
    }

    public static String createWitnessNode(CState state, boolean cyclehead) {
        return node(state.getNodeID(), state.isEntry(), cyclehead, state.isLoopHead(), state.getInvariant());
    }

    private static String edge(
            int sourceID,
            int targetID,
            boolean enterLoopHead,
            int startline,
            int endline,
            String sourceCode,
            YNM control,
            String enterFunction
    ) {
        StringBuilder builder = new StringBuilder("    <edge source=\"" + "S" + sourceID + "\" target=\"" + "S" + targetID + "\">\n");
        // TODO assumption for nondet
//        String code = sourceCode.y;
//        if (sourceCode.x) {
//            String cond = "[" + code + "]";
//            String negCond = "[!(" + code + ")]";
//            String neg;
//            if (!hasSink) {
//                res = res.concat(sink());
//                hasSink = true;
//            }source.getFunctionName()
//            if (code.equals("1")) {
//                control = YNM.YES;
//            }
//            assert(!control.equals(YNM.MAYBE));
//            if (control.equals(YNM.YES)) {
//                code = cond;
//                neg = negCond;
//            } else {
//                code = negCond;
//                neg = cond;
//            }
//            YNM negControl = control.equals(YNM.YES) ? YNM.NO : YNM.YES;
//            res = res.concat(edgeToSink(source, false, startline, endline, neg, negControl, enterFunction));
//        }
        if (enterLoopHead) {
            builder.append("      <data key=\"enterLoopHead\">true</data>\n");
        }
        if (sourceCode != null && enterFunction == null) {
            builder.append("      <data key=\"sourcecode\">" + sourceCode + "</data>\n");
        }
        if (startline >= 0) {
            builder.append("      <data key=\"startline\">" + startline + "</data>\n");
        }
        if (endline >= 0) {
            builder.append("      <data key=\"endline\">" + endline + "</data>\n");
        }
        if (control.equals(YNM.YES)) {
            builder.append("      <data key=\"control\">condition-true</data>\n");
        } else if (control.equals(YNM.NO)) {
            builder.append("      <data key=\"control\">condition-false</data>\n");
        }
        if (enterFunction != null) {
            builder.append("      <data key=\"enterFunction\">" + enterFunction + "</data>\n");
        }
        builder.append("    </edge>\n");
        return builder.toString();
    }

    private static String edgeToSink(
            int sourceID,
            boolean enterLoopHead,
            int startline,
            int endline,
            String sourceCode,
            YNM control,
            String enterFunction
    ) {
        StringBuilder builder = new StringBuilder("    <edge source=\"" + "S" + sourceID + "\" target=\"" + "sink" + "\">\n");
        if (enterLoopHead) {
            builder.append("      <data key=\"enterLoopHead\">true</data>\n");
        }
        if (sourceCode != null && enterFunction == null) {
            builder.append("      <data key=\"sourcecode\">" + sourceCode + "</data>\n");
        }
        if (startline >= 0) {
            builder.append("      <data key=\"startline\">" + startline + "</data>\n");
        }
        if (endline >= 0) {
            builder.append("      <data key=\"endline\">" + endline + "</data>\n");
        }
        if (control.equals(YNM.YES)) {
            builder.append("      <data key=\"control\">condition-true</data>\n");
        } else if (control.equals(YNM.NO)) {
            builder.append("      <data key=\"control\">condition-false</data>\n");
        }
        if (enterFunction != null) {
            builder.append("      <data key=\"enterFunction\">" + enterFunction + "</data>\n");
        }
        builder.append("    </edge>\n");
        return builder.toString();
    }

    public static String finish() {
        return "  </graph>\n</graphml>\n";
    }
    
    
    public static String init(String programFile, String programHash) {
        StringBuilder builder = new StringBuilder("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n");
        builder.append("<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" xsi:schemaLocation=\"http://graphml.graphdrawing.org/xmlns http://graphml.graphdrawing.org/xmlns/1.0/graphml.xsd\">\n");
        builder.append("  <key id=\"programfile\" attr.name=\"programfile\" for=\"graph\"/>\n");
        builder.append("  <key id=\"programhash\" attr.name=\"programhash\" for=\"graph\"/>\n");
        builder.append("  <key id=\"sourcecodelang\" attr.name=\"sourcecodelang\" for=\"graph\"/>\n");
        builder.append("  <key id=\"producer\" attr.name=\"producer\" for=\"graph\"/>\n");
        builder.append("  <key id=\"specification\" attr.name=\"specification\" for=\"graph\"/>\n");
        builder.append("  <key id=\"creationtime\" attr.name=\"creationtime\" for=\"graph\"/>\n");
        builder.append("  <key id=\"witness-type\" attr.name=\"witness-type\" for=\"graph\"/>\n");
        builder.append("  <key id=\"architecture\" attr.name=\"architecture\" for=\"graph\"/>\n");
        builder.append("  <key id=\"entry\" attr.name=\"entry\" for=\"node\">\n");
        builder.append("    <default>false</default>\n");
        builder.append("  </key>\n");
        builder.append("  <key id=\"nodetype\" attr.name=\"nodetype\" for=\"node\">\n");
        builder.append("    <default>path</default>\n");
        builder.append("  </key>\n");
        builder.append("  <key id=\"violation\" attr.name=\"violation\" for=\"node\">\n");
        builder.append("    <default>false</default>\n");
        builder.append("  </key>\n");
        builder.append("  <key id=\"cyclehead\" attr.name=\"cyclehead\" for=\"node\">\n");
        builder.append("    <default>false</default>\n");
        builder.append("  </key>\n");
        builder.append("  <key id=\"invariant\" attr.name=\"invariant\" for=\"node\">\n");
        builder.append("    <default>true</default>\n");
        builder.append("  </key>\n");
        builder.append("  <key id=\"sink\" attr.name=\"sink\" for=\"node\">\n");
        builder.append("    <default>false</default>\n");
        builder.append("  </key>\n");
        builder.append("  <key id=\"endline\" attr.name=\"endline\" for=\"edge\"/>\n");
        builder.append("  <key id=\"enterLoopHead\" attr.name=\"enterLoopHead\" for=\"edge\">\n");
        builder.append("    <default>false</default>\n");
        builder.append("  </key>\n");
        builder.append("  <key id=\"enterFunction\" attr.name=\"enterFunction\" for=\"edge\"/>\n");
        builder.append("  <key id=\"startline\" attr.name=\"startline\" for=\"edge\"/>\n");
        builder.append("  <key id=\"returnFrom\" attr.name=\"returnFrom\" for=\"edge\"/>\n");
        builder.append("  <key id=\"assumption\" attr.name=\"assumption\" for=\"edge\"/>\n");
        builder.append("  <key id=\"tokens\" attr.name=\"tokens\" for=\"edge\"/>\n");
        builder.append("  <key id=\"control\" attr.name=\"control\" for=\"edge\"/>\n");
        builder.append("  <key id=\"originfile\" attr.name=\"originfile\" for=\"edge\">\n");
        builder.append("    <default>" + programFile + "</default>\n");
        builder.append("  </key>\n");
        builder.append("  <key id=\"sourcecode\" attr.name=\"sourcecode\" for=\"edge\"/>\n");
        builder.append("  <graph edgedefault=\"directed\">\n");
        builder.append("    <data key=\"witness-type\">violation_witness</data>\n");
        builder.append("    <data key=\"sourcecodelang\">C</data>\n");
        builder.append("    <data key=\"producer\">AProVE</data>\n");
        TimeZone zone = TimeZone.getTimeZone("UTC");
        DateFormat format = new SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss'Z'");
        format.setTimeZone(zone);
        String timestamp = format.format(new Date());
        builder.append("    <data key=\"creationtime\">" + timestamp + "</data>\n");
        builder.append("    <data key=\"specification\">CHECK( init(main()), LTL(F end) )</data>\n");
        builder.append("    <data key=\"programfile\">" + programFile + "</data>\n");
        builder.append("    <data key=\"programhash\">" + programHash + "</data>\n");
        builder.append("    <data key=\"architecture\">" + Globals.bitwidth + "bit</data>\n");
        return builder.toString();
    }

    private static String node(
            int nodeID,
            boolean entry,
            boolean cyclehead,
            boolean loophead,
            String invariant
    ) {
        // TODO invariants (only for loopheads)
        StringBuilder builder = new StringBuilder("    <node id=\"" + "S" + nodeID + "\">\n");
        if (entry) {
            builder.append("      <data key=\"entry\">true</data>\n");
        }
        if (cyclehead) {
            builder.append("      <data key=\"cyclehead\">true</data>\n");
        }
        if (invariant != null) {
            builder.append("      <data key=\"invariant\">" + invariant + "</data>\n");
        }
        if (!entry && !cyclehead && invariant == null) {
            return "    <node id=\"" + "S" + nodeID + "\"/>\n";
        }
        builder.append("    </node>\n");
        return builder.toString();
    }

    public static String sink() {
        String res = "    <node id=\"sink\">\n";
        res = res.concat("      <data key=\"sink\">true</data>\n");
        res = res.concat("    </node>\n");
        return res;
    }

}
