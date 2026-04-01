package aprove.input.Programs.triples;

import java.util.*;

import aprove.input.Programs.prolog.structure.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

public class TriplesProblem extends DefaultBasicObligation {

    private PrologProgram triples;
    private PrologProgram clauses;
    private Afs afs;

    public TriplesProblem(PrologProgram triples, PrologProgram program, Afs afs) {
        super("TRIPLES","Dependency Triple Problem");
        this.triples = triples;
        this.clauses = program;
        this.afs = afs;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination");
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder res = new StringBuilder();
        PrologProgram all = this.triples.copy();
        all.getClauses().addAll(this.clauses.getClauses());
        Set<FunctionSymbol> preds = all.createSetOfAllPredicates(true);
        res.append(o.export("Triples:"));
        res.append(o.linebreak());
        res.append(o.linebreak());
        for (PrologClause c : this.triples.getClauses()) {
            res.append(c.export(o, preds));
            res.append(o.export("."));
            res.append(o.linebreak());
        }
        res.append(o.linebreak());
        res.append(o.export("Clauses:"));
        res.append(o.linebreak());
        res.append(o.linebreak());
        for (PrologClause c : this.clauses.getClauses()) {
            res.append(c.export(o, preds));
            res.append(o.export("."));
            res.append(o.linebreak());
        }
        res.append(o.linebreak());
        res.append(o.export("Afs:"));
        res.append(o.linebreak());
        res.append(o.linebreak());
        res.append(this.afs.export(o));
        return res.toString();
    }

    public PrologProgram getTriples() {
        return this.triples;
    }

    public PrologProgram getClauses() {
        return this.clauses;
    }

    public Afs getAfs() {
        return this.afs;
    }

    @Override
    public String toString() {
        StringBuilder build = new StringBuilder();
        build.append("Triples:\n\n");
        for (final PrologClause c : this.triples.getClauses()) {
            build.append(c.toString());
            build.append(".\n");
        }
        build.append("\n");
        build.append(this.clauses.toString());
        return build.toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "triples";
    }
}
