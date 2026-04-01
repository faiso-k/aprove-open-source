package aprove.verification.oldframework.Output;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

public class TRSGenerator {

    private StringBuffer target = new StringBuffer();
    private Set<TRSVariable> variables = new LinkedHashSet<TRSVariable>();

    private void write(String s){
        this.target.append(s);
    }

    private void writeTerm(TRSTerm t){
        this.variables.addAll(t.getVariables());
        this.target.append(t.toString());
    }

    private void writeRule(GeneralizedRule grule,String arrow){
        this.writeTerm(grule.getLeft());
        this.target.append(arrow);
        this.writeTerm(grule.getRight());
    }

    private void writeTerms(String head,Set<? extends TRSTerm> terms,String nl){
        this.write("(");
        this.write(head);
        this.write(nl);
        for (TRSTerm t : terms){
            this.writeTerm(t);
            this.write(nl);
        }
        this.write(")\n");
    }

    private void writeRules(String head, String arrow, Set<? extends GeneralizedRule> grules){
        this.write("(");
        this.write(head);
        this.write("\n");
        for (GeneralizedRule grule : grules){
            this.writeRule(grule,arrow);
            this.write("\n");
        }
        this.write(")\n");
    }

    private void writeStrategy(boolean writeminimal,boolean minimal, boolean innermost, Map<FunctionSymbol, ? extends Set<Integer>> repMap){
        if (writeminimal){
            if (minimal){
                this.write("(MINIMAL YES)\n");
            } else {
                this.write("(MINIMAL NO)\n");
            }
        }
        if (innermost){
            this.write("(STRATEGY INNERMOST)\n");
         }
        if (repMap != null){
            this.write("(STRATEGY CONTEXTSENSITIVE");
            for (Map.Entry<FunctionSymbol,? extends Set<Integer>> entry : repMap.entrySet()){
                this.write("(");
                this.write(entry.getKey().toString());
                this.write(" ");
                for (Integer i : entry.getValue()){
                    this.write(""+(i+1));
                }
                this.write(")\n");
            }
            this.write(")\n");
        }
    }

    public void writePairs(Set<Rule> rules){
        this.writeRules("PAIRS"," -> ",rules);
    }

    public void writeRules(Set<Rule> rules){
        this.writeRules("RULES"," -> ",rules);
    }

    public void writeRelativeRules(Set<Rule> rules){
        this.writeRules("RULES"," ->= ",rules);
    }

    public void writeGeneralizedRules(Set<GeneralizedRule> rules){
        this.writeRules("RULES"," -> ",rules);
    }

    public void writeEquations(Set<Equation> equations){
        this.write("(THEORY");
        this.write("\n");
        this.write("(EQUATIONS");
        this.write("\n");
        for (Equation e : equations){
            this.writeTerm(e.getLeft());
            this.write(" == ");
            this.writeTerm(e.getRight());
            this.write("\n");
        }
        this.write(")\n");
        this.write(")\n");
    }

    public void writeConditionalRules(Set<ConditionalRule> cRules){
        this.write("(");
        this.write("RULES");
        this.write("\n");
        for (ConditionalRule cr : cRules){
            this.writeTerm(cr.getLeft());
            this.write(" -> ");
            this.writeTerm(cr.getRight());
            if (!cr.getConditions().isEmpty()){
               this.write(" |");
               String co = " ";
               for (Condition c : cr.getConditions()){
                      this.write(co);
                   this.writeTerm(c.getLeft());
                   switch (c.getType()){
                     case ARROW: this.write(" -> "); break;
                     case JOIN: this.write(" -><- "); break;
                     case EQUAL: this.write(" == "); break;
                   }
                      this.writeTerm(c.getRight());
                      co = ", ";
               }
            }
            this.write("\n");
        }
        this.write(")\n");
    }

    public void writeQ(Set<TRSFunctionApplication> qterms){
        this.writeTerms("Q",qterms,"\n");
    }

    public void writeVAR(Set<TRSVariable> variables){
        this.writeTerms("VAR",variables," ");
    }

    public void reset(){
        this.variables.clear();
        this.target = new StringBuffer();
    }

    public String getTRSString(boolean innermost, Map<FunctionSymbol, ? extends Set<Integer>> repMap) {
        String res = this.target.toString();
        this.target = new StringBuffer();
        this.writeStrategy(false,false,innermost, repMap);
        this.writeVAR(this.variables);
        res = this.target.toString()+res;
        this.reset();
        return res;
    }

    public String getTRSString(boolean minimal, boolean innermost, Map<FunctionSymbol, ? extends Set<Integer>> repMap) {
        String res = this.target.toString();
        this.target = new StringBuffer();
        this.writeStrategy(true,minimal,innermost, repMap);
        this.writeVAR(this.variables);
        res = this.target.toString()+res;
        this.reset();
        return res;
    }
}
