package aprove.verification.oldframework.Bytecode.Processors;

import static java.util.stream.Collectors.*;

import java.io.*;
import java.util.*;

import aprove.input.Programs.jbc.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Bytecode.JBCOptions.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.*;

public class BareJBCToJBCProcessor extends ProcessorSkeleton {

    public static class BareJBCOptions {
        /**
         * JAR files containing libraries (e.g. rt.jar)
         */
        public static StaticOption<Set<File>> cliLibraryJars = new StaticOption<>();
        private InstanceOption<Set<File>> libraryJars = new InstanceOption<Set<File>>(Collections.emptySet(), cliLibraryJars);

        public void setLibraryJars(String paths) {
            libraryJars.set(Arrays.asList(paths.split(":")).stream().map(x -> new File(x)).collect(toSet()));
        }

        public Set<File> getLibraryJars() {
            return libraryJars.get();
        }

        public static void addCliLibraryJar(File file) {
            Set<File> val = cliLibraryJars.get(new LinkedHashSet<>());
            val.add(file);
            cliLibraryJars.set(val);
        }

    }

    private BareJBCOptions options;

    @ParamsViaArgumentObject
    public BareJBCToJBCProcessor(BareJBCOptions options) {
        this.options = options;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) {
        BareJBCProblem bjbc = (BareJBCProblem) obl;
        final ClassPath cPath;
        final Set<File> jars = options.getLibraryJars();
        cPath = new ClassPath(jars, options);
        final ClassStreamProvider jbcProgramStream = bjbc.getJBCProgramStream();
        cPath.addClassStreamProvider(jbcProgramStream);
        cPath.initialize();
        String src = jbcProgramStream.readProgramInformation();
        BasicObligation newObl = new JBCProblem(bjbc.getTranslator(), cPath, src, bjbc.getGoal());
        return ResultFactory.proved(newObl, bjbc.getGoal().equivalent(true), new BareJBCToJBCProof());
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof BareJBCProblem;
    }

    public static class BareJBCToJBCProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "initialized classpath";
        }

    }

}
