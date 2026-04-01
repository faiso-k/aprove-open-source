package aprove.api.impl;

import java.io.*;
import java.nio.charset.*;
import java.nio.file.*;
import java.util.*;
import java.util.stream.*;

import aprove.api.*;
import aprove.api.decisions.*;
import aprove.api.decisions.factory.*;
import aprove.verification.oldframework.Input.*;

public class ProblemInputImpl implements ProblemInput {

    public static ProblemInput from(Path path) {
        return new ProblemInputImpl(path, getFileExtension(path));
    }

    private static String getFileExtension(Path path) {
        String filename = path.getFileName().toString();
        return filename.substring(filename.lastIndexOf(".") + 1);
    }

    private final Path path;
    private final String fileExtension;

    public ProblemInputImpl(Path path, String fileExtension) {
        this.path = path;
        this.fileExtension = fileExtension;
    }

    public Path getPath() {
        return path;
    }

    public String getFileExtension() {
        return fileExtension;
    }

    public Stream<String> lines() throws IOException, UncheckedIOException {
        return Files.lines(path, StandardCharsets.UTF_8);
    }

    public Input createInput() {
        return new FileInput(path.toFile(), fileExtension);
    }

    public String getCPFOnlineCheckerPrefix() {
        return path.toString();
    }

    public AnalyzableProblemInput withAnnotation(String annotation) {
        return new AnalyzableProblemInputImpl(this, annotation);
    }

    @Override
    public AnalyzableProblemInput createAnalyzableProblemInput() {
        return withAnnotation("");
    }

    @Override
    public AnalyzableProblemInput withJBCAnnotation(String startMethod, String jbcAnnotations, String handlingMode) {
        return withAnnotation(handlingMode + "|" + startMethod + "|" + jbcAnnotations);
    }

    @Override
    public Optional<ProblemDecisions> createProblemDecisions() throws ProblemDecisionsInstantiationException {
        return ProblemDecisionsFactory.createProblemDecisions(this);
    }
}
