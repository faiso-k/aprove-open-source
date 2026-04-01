package aprove.input.Programs.newIDP;

import java.io.*;
import java.util.*;

import org.antlr.runtime.*;

import aprove.input.Generated.newIDP.*;
import aprove.input.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Translator.*;
import immutables.*;

public class Translator extends TranslatorSkeleton {

    @Override
    public Language getLanguage() {
        return Language.IDP;
    }

    @Override
    public void translate(final Reader reader) {
        try {
            final NewIDPLexer lex = new NewIDPLexer(new ANTLRReaderStream(reader));
            final CommonTokenStream tokens = new CommonTokenStream(lex);
            final NewIDPParser parser = new NewIDPParser(tokens);
            final RawIDP rawIDP = parser.itrs();
            if (rawIDP.getNodes().isEmpty()) {
                // ITRS
                this.setState(
                    TIDPProblem.create(
                        rawIDP.getItpfFactory(),
                        rawIDP.getPredefinedMap(),
                        rawIDP.getRules(),
                        rawIDP.getQ(),
                        rawIDP.isMinimal(),
                        null
                    )
                );
            } else {
                final Map<INode, VarRenaming> loopRenamings =
                    rawIDP.completeLoopRenamings();
                final Map<INode, ITerm<?>> nodes =
                    new LinkedHashMap<INode, ITerm<?>>(rawIDP.getNodes());
                final Map<INode, Itpf> nodeConditions =
                    new LinkedHashMap<INode, Itpf>(rawIDP.getNodeConditions());
                final Set<INode> initialNodes =
                    new LinkedHashSet<INode>(rawIDP.getInitialNodes());

                final Map<IEdge, Itpf> edges = new LinkedHashMap<IEdge, Itpf>(rawIDP.getEdges());
                final FreshVarGenerator freshVarGenerator = this.createFreshVarGenerator(nodes, nodeConditions, loopRenamings, edges);

                final IDependencyGraph graph =
                    IDependencyGraph.create(rawIDP.getPredefinedMap(),
                        rawIDP.getQ(),
                        rawIDP.getItpfFactory(),
                        null,
                        ImmutableCreator.create(nodes),
                        ImmutableCreator.create(nodeConditions),
                        ImmutableCreator.create(initialNodes),
                        IDependencyGraph.createEmptyNodeUnrollCounter(nodes.keySet()),
                        ImmutableCreator.create(loopRenamings),
                        ImmutableCreator.create(edges), freshVarGenerator);
                this.setState(TIDPProblem.create(graph, rawIDP.isMinimal()));
            }
        } catch (final RecognitionException re) {
            final ParseError pe = new ParseError();
            pe.setLine(re.line);
            pe.setColumn(re.charPositionInLine);
            pe.setMessage(re.getMessage());
            this.getErrors().add(pe);
        } catch (final IOException e) {
            final ParseError pe = new ParseError();
            pe.setMessage(e.getMessage());
            this.getErrors().add(pe);
        } catch (final AbortionException e) {
            final ParseError pe = new ParseError();
            pe.setMessage(e.getMessage());
            this.getErrors().add(pe);
        }
    }

    private FreshVarGenerator createFreshVarGenerator(final Map<INode, ITerm<?>> nodes,
        final Map<INode, Itpf> nodeConditions,
        final Map<INode, VarRenaming> loopRenamings,
        final Map<IEdge, Itpf> edges) {

        final Set<IVariable<?>> usedVars = new HashSet<IVariable<?>>();
        for (final ITerm<?> t : nodes.values()) {
            t.collectVariables(usedVars);
        }

        for (final Itpf f : nodeConditions.values()) {
            usedVars.addAll(f.getVariables());
        }

        for (final VarRenaming sigma : loopRenamings.values()) {
            usedVars.addAll(sigma.getVariables());
        }

        for (final Itpf f : edges.values()) {
            usedVars.addAll(f.getVariables());
        }

        return new FreshVarGenerator(usedVars);
    }
}
