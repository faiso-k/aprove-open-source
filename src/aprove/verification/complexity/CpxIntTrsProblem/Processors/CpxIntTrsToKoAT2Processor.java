package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.text.*;

import aprove.strategies.Annotations.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.Algebra.MinMaxExprs.*;
public class CpxIntTrsToKoAT2Processor extends CpxIntTrsToKoATLikeBackendProcessor<CpxIntTrsToKoAT2Processor.Arguments> {

    public static class Arguments extends CpxIntTrsToKoATLikeBackendProcessor.Arguments {
        public String smtSolver = "";
        public int timeout = 0; //in s
    }

    @Override
    public ComplexityValue readFromKoatLikeParser(String resultText) {
      Pattern currCompl = Pattern.compile("EXP");
      Matcher findAsymptotic = currCompl.matcher(resultText);
      if(findAsymptotic.find()){
    	  return ComplexityValue.exponential();
      }
      currCompl = Pattern.compile("O\\(1\\)");
      findAsymptotic = currCompl.matcher(resultText);
      if(findAsymptotic.find()){
    	  return ComplexityValue.constant();
      }
      ComplexityValue cpl = null;
      currCompl = Pattern.compile("O\\(n\\)");
      findAsymptotic = currCompl.matcher(resultText);

      if(findAsymptotic.find()) {
    	  cpl =  ComplexityValue.fixedDegreePoly(1);
      }
      	currCompl = Pattern.compile("O\\(n\\^([1-9][0-9]*)\\)");
      	findAsymptotic = currCompl.matcher(resultText);

      if(findAsymptotic.find()) {
    	  cpl =  ComplexityValue.fixedDegreePoly(Integer.parseInt(findAsymptotic.group(1)));
      }
      return cpl;
    }

    @ParamsViaArgumentObject
    public CpxIntTrsToKoAT2Processor(Arguments args) {
        super(args);
    }

    @Override
    public String getToolName() {
        return "koat2";
    }

    @Override
    public AnalysisGoal getAnalysisGoal() {
        return AnalysisGoal.UpperBound;
    }

    @Override
    public List<String> getCommandLineArgs() {
        List<String> parameters = new ArrayList<>(2);
        parameters.add("analyse");
        parameters.add("--local=mprf,twn");
        parameters.add("-d5");
        parameters.add("--cfr=pe");
        parameters.add("--preprocessors=invgen,sat,reachable,eliminate");
        parameters.add("--rename");
        parameters.add("-rall");
        parameters.add("-i");
        return parameters;
    }
}
