package aprove.input.Programs.llvm.utils;

import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.stream.Stream;

import aprove.Globals;

public class CState {
    
    private static int counter = 0;
    
    private int cLine;
    
    private boolean loopHead;
    
    private String functionName;
    
    private boolean entry;
    
    private String invariant;
    
    private int nodeID;
    
    private String sourceCode;
    
    public CState(int id, int cLine, boolean entry, String functionName, String invariant) {
        this.nodeID = id;
        this.cLine = cLine;
        this.entry = entry;
        this.functionName = functionName;
        this.invariant = invariant;
        this.sourceCode = this.readLine();
        this.loopHead = this.isHeadOfLoop(this.sourceCode);
    }
    
    private static boolean containsCondition(String cLine) {
        if (cLine.startsWith("if") && cLine.substring(2).trim().startsWith("(")) {
            return true;
        }
        if (cLine.startsWith("while") && cLine.substring(5).trim().startsWith("(")) {
            return true;
        }
        return false;
    }
    
    private static String extractCondition(String cLine) {
        // while(x>0) -> x>0
        if (cLine.startsWith("if") && cLine.substring(2).trim().startsWith("(")) {
            int start = cLine.indexOf("(");
            int end = cLine.indexOf(")");
            return cLine.substring(start + 1, end);
        }
        if (cLine.startsWith("while") && cLine.substring(5).trim().startsWith("(")) {
            int start = cLine.indexOf("(");
            int end = cLine.indexOf(")");
            return cLine.substring(start + 1, end);
        }
        assert(false);
        return null;
    }
    
    public boolean equals(CState other) {
        if (this.nodeID == other.nodeID) {
            assert this.entry == other.entry;
            assert this.loopHead == other.loopHead;
            assert this.cLine == other.cLine;
            assert functionName == null && other.functionName == null || this.functionName.equals(other.functionName);
            assert functionName == null && other.functionName == null || this.invariant.equals(other.invariant);
            return true;
        }
        return false;
    }
    
    public static String getFreshNodeID() {
        String id = "A" + counter;
        counter++;
        return id;
    }
    
    public int getCLine() {
        return this.cLine;
    }
    
    public String getFunctionName() {
        return this.functionName;
    }

    public String getInvariant() {
        return this.invariant;
    }
    
    public int getNodeID() {
        return this.nodeID;
    }
    
    public String getSourceCode() {
        return this.sourceCode;
    }
    
    public boolean isEntry() {
        return this.entry;
    }
    
    private boolean isHeadOfLoop(String code) {
        if (code.startsWith("while") && code.substring(5).trim().startsWith("(")) {
            return true;
        }
        if (code.startsWith("for") && code.substring(5).trim().startsWith("(")) {
            return true;
        }
        return false;
    }
    
    public boolean isLoopHead() {
        return this.loopHead;
    }
    
    private String readLine() {
        String programFile = Globals.programFile;
        String code = null;
        try (Stream<String> lines = Files.lines(Paths.get(programFile))) {
            if (this.cLine >= 0) {
                code = lines.skip(this.cLine - 1).findFirst().get();
            }
        } catch (Exception e) {
            System.err.println(e.getMessage());
        }
        // remove leading and trailing whitespace
        if (code == null) code = "";
        code = code.trim();
        code = code.replace("&", "&amp;");
        code = code.replace("<", "&lt;");
        code = code.replace(">", "&gt;");
        code = code.replace("\"", "&quot;");
        code = code.replace("'", "&apos;");
        return code;
    }
    
    public String toString() {
        String res = "";
        res = res.concat("Node ID: " + this.nodeID + "\n");
        res = res.concat("Line of C Program: " + this.cLine + "\n");
        res = res.concat("Entry: " + this.entry + "\n");
        if (this.entry) {
            res = res.concat("Function: " + this.functionName + "\n");
        }
        res = res.concat("Invariant: " + this.invariant + "\n");
        return res;
    }

}
