package aprove.cli.tpdbConverter;

import java.io.*;
import java.net.*;
import java.util.*;

import javax.xml.parsers.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.*;
import javax.xml.transform.stream.*;
import javax.xml.validation.*;

import org.w3c.dom.*;
import org.xml.sax.*;

import aprove.prooftree.Obligations.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Exceptions.*;
import immutables.*;

public class TPDB_Exporter {

    static Element toTPDB(final TRSTerm t, final Document doc) {
        if (t.isVariable()) {
            final Element e = doc.createElement("var");
            e.appendChild(doc.createTextNode(((TRSVariable) t).getName()));
            return e;
        } else {
            final Element e = doc.createElement("funapp");
            final TRSFunctionApplication ft = (TRSFunctionApplication) t;
            final Element g = doc.createElement("name");
            g.appendChild(doc.createTextNode(ft.getRootSymbol().getName()));
            e.appendChild(g);
            for (final TRSTerm arg : ft.getArguments()) {
                final Element f = doc.createElement("arg");
                f.appendChild(TPDB_Exporter.toTPDB(arg, doc));
                e.appendChild(f);
            }
            return e;
        }
    }

    /**
     * creates a standard entry for function-symbol as part of a signature
     */
    static Element toTPDB(final FunctionSymbol fs, final Document doc) {
        final Element e = doc.createElement("funcsym");
        final Element f = doc.createElement("name");
        f.appendChild(doc.createTextNode(fs.getName()));
        e.appendChild(f);
        return e;
    }

    /**
     * creates an element for the signature in equational case
     * @param repMap maybe null
     */
    static Element toTPDB(final FunctionSymbol fs,
        final Set<FunctionSymbol> C,
        final Set<FunctionSymbol> AC,
        final Set<FunctionSymbol> A,
        final Document doc) {
        final Element e = TPDB_Exporter.toTPDB(fs, doc);
        Element f = doc.createElement("arity");
        f.appendChild(doc.createTextNode(fs.getArity() + ""));
        e.appendChild(f);
        if (C.contains(fs)) {
            f = doc.createElement("theory");
            f.appendChild(doc.createTextNode("C"));
            e.appendChild(f);
        } else if (AC.contains(fs)) {
            f = doc.createElement("theory");
            f.appendChild(doc.createTextNode("AC"));
            e.appendChild(f);
        } else if (A.contains(fs)) {
            f = doc.createElement("theory");
            f.appendChild(doc.createTextNode("A"));
            e.appendChild(f);
        }
        return e;
    }

    /**
     * creates an element for the signature in standard or CSR-case
     * @param repMap maybe null
     */
    static Element toTPDB(final FunctionSymbol fs,
        final Map<FunctionSymbol, ImmutableSet<Integer>> repMap,
        final Document doc) {
        final Element e = TPDB_Exporter.toTPDB(fs, doc);
        Element f = doc.createElement("arity");
        f.appendChild(doc.createTextNode(fs.getArity() + ""));
        e.appendChild(f);
        if (repMap != null) {
            Set<Integer> entry = repMap.get(fs);
            if (entry == null) {
                System.err.println("Warning, entry replacement map entry for " + fs + ", choosing full map");
                final int n = fs.getArity();
                entry = new LinkedHashSet<Integer>(n);
                for (int i = 0; i < n; i++) {
                    entry.add(i);
                }
            } else {
                // sorting for convenient output
                entry = new TreeSet<Integer>(entry);
            }
            f = doc.createElement("replacementmap");
            for (final Integer i : entry) {
                final Element g = doc.createElement("entry");
                g.appendChild(doc.createTextNode((i + 1) + ""));
                f.appendChild(g);
            }
            e.appendChild(f);
        }
        return e;
    }

    /**
     * creates an element for the domain
     */
    static Element toTPDB(final Domain domain, final Document doc) {
        if (domain.isBooleanDomain()) {
            return doc.createElement("booleans");
        } else if (domain.isIntegerDomain()) {
            final IntegerDomain intDom = (IntegerDomain) domain;
            final Element e = doc.createElement("integers");
            if (intDom.getBits() > 0) {
                final Element bits = doc.createElement("bits");
                bits.appendChild(doc.createTextNode(String.valueOf(intDom.getBits())));
                e.appendChild(bits);
            }
            return e;
        } else {
            throw new NotExpressibleException("can not export domain " + domain);
        }
    }

    /**
     * creates an element for the pre-defined function
     */
    static Element toTPDB(final Func func, final Document doc) {
        switch (func) {
        case Add:
            return doc.createElement("plus");
        case Sub:
            return doc.createElement("minus");
        case Mul:
            return doc.createElement("times");
        case Div:
            return doc.createElement("div");
        case Mod:
            return doc.createElement("modulo");
        case Cast:
            return doc.createElement("cast");
        case Land:
            return doc.createElement("logical_and");
        case Lor:
            return doc.createElement("logical_or");
        case Lnot:
            return doc.createElement("logical_not");
        case Gt:
            return doc.createElement("greater_than");
        case Ge:
            return doc.createElement("greater_equals");
        case Lt:
            return doc.createElement("less_than");
        case Le:
            return doc.createElement("less_equals");
        case Eq:
            return doc.createElement("equals");
        case Neq:
            return doc.createElement("not_equals");
        case UnaryMinus:
            return doc.createElement("u_minus");
        default:
            throw new NotExpressibleException("can not export function " + func);
        }
    }

    /**
     * creates an element for the signature of a maybe pre-defined function symbol in ITRS case
     */
    static Element toTPDB(final FunctionSymbol fs, final IDPPredefinedMap predefinedMap, final Document doc) {
        final Element symbol = TPDB_Exporter.toTPDB(fs, doc);
        final Element arity = doc.createElement("arity");
        arity.appendChild(doc.createTextNode(fs.getArity() + ""));
        symbol.appendChild(arity);
        final PredefinedSemantics sem = predefinedMap.getPredefinedSemantics(fs);
        if (sem != null) {
            final Element semantics = doc.createElement("semantics");
            symbol.appendChild(semantics);
            if (sem.isConstructor()) {
                final PredefinedConstructor constr = (PredefinedConstructor) sem;
                semantics.appendChild(TPDB_Exporter.toTPDB(constr.getDomain(), doc));
            } else {
                @SuppressWarnings(value = {"unchecked" })
                final PredefinedFunction<? extends Domain> func = (PredefinedFunction<? extends Domain>) sem;
                final Element function = TPDB_Exporter.toTPDB(func.getFunc(), doc);
                semantics.appendChild(function);
                for (final Domain dom : func.getDomains()) {
                    function.appendChild(TPDB_Exporter.toTPDB(dom, doc));
                }
            }
        }
        return symbol;
    }

    static Element toTPDB(final ConditionalRule rule, final Document doc) {
        final Element e = doc.createElement("rule");
        Element f = doc.createElement("lhs");
        f.appendChild(TPDB_Exporter.toTPDB(rule.getLeft(), doc));
        Element g = doc.createElement("rhs");
        g.appendChild(TPDB_Exporter.toTPDB(rule.getRight(), doc));
        e.appendChild(f);
        e.appendChild(g);
        f = doc.createElement("conditions");
        for (final Condition c : rule.getConditions()) {
            g = doc.createElement("condition");
            Element h = doc.createElement("lhs");
            h.appendChild(TPDB_Exporter.toTPDB(c.getLeft(), doc));
            g.appendChild(h);
            h = doc.createElement("rhs");
            h.appendChild(TPDB_Exporter.toTPDB(c.getRight(), doc));
            g.appendChild(h);
            f.appendChild(g);
        }
        e.appendChild(f);
        return e;

    }

    static Element toTPDB(final GeneralizedRule rule, final Document doc) {
        final Element e = doc.createElement("rule");
        final Element f = doc.createElement("lhs");
        f.appendChild(TPDB_Exporter.toTPDB(rule.getLeft(), doc));
        final Element g = doc.createElement("rhs");
        g.appendChild(TPDB_Exporter.toTPDB(rule.getRight(), doc));
        e.appendChild(f);
        e.appendChild(g);
        return e;
    }

    static Element toTPDB(final TermPair rule, final Document doc) {
        final Element e = doc.createElement("rule");
        final Element f = doc.createElement("lhs");
        f.appendChild(TPDB_Exporter.toTPDB(rule.getLeft(), doc));
        final Element g = doc.createElement("rhs");
        g.appendChild(TPDB_Exporter.toTPDB(rule.getRight(), doc));
        e.appendChild(f);
        e.appendChild(g);
        return e;
    }

    private static Element toTPDB(final Set<? extends GeneralizedRule> rules,
        final Set<FunctionSymbol> signature,
        final Document doc) {
        return TPDB_Exporter.toTPDB(rules, null, null, signature, (Map<FunctionSymbol, ImmutableSet<Integer>>) null, doc);
    }

    private static Element toTPDB(final Set<? extends GeneralizedRule> rules,
        final Set<? extends Rule> relRules,
        final Set<ConditionalRule> condRules,
        final Set<FunctionSymbol> signature,
        final Map<FunctionSymbol, ImmutableSet<Integer>> repMap,
        final Document doc) {
        final Element e = doc.createElement("trs");
        Element f = doc.createElement("rules");
        for (final GeneralizedRule r : rules) {
            f.appendChild(TPDB_Exporter.toTPDB(r, doc));
        }
        if (condRules != null) {
            for (final ConditionalRule r : condRules) {
                f.appendChild(TPDB_Exporter.toTPDB(r, doc));
            }
        }
        if (relRules != null) {
            final Element g = doc.createElement("relrules");
            for (final Rule r : relRules) {
                g.appendChild(TPDB_Exporter.toTPDB(r, doc));
            }
            f.appendChild(g);
        }
        e.appendChild(f);
        f = doc.createElement("signature");
        final Set<String> sig = new HashSet<String>();
        for (final FunctionSymbol fs : signature) {
            final String name = fs.getName();
            if (sig.add(name)) {
                f.appendChild(TPDB_Exporter.toTPDB(fs, repMap, doc));
            } else {
                throw new NotExpressibleException("Symbol " + name + " occurs with different arities");
            }
        }
        e.appendChild(f);
        if (condRules != null) {
            f = doc.createElement("conditiontype");
            f.appendChild(doc.createTextNode("ORIENTED"));
            e.appendChild(f);
        }
        return e;
    }

    private static Element toTPDB(final Set<? extends GeneralizedRule> rules,
        final Set<FunctionSymbol> signature,
        final Set<FunctionSymbol> C,
        final Set<FunctionSymbol> AC,
        final Set<FunctionSymbol> A,
        final Document doc) {
        final Element e = doc.createElement("trs");
        Element f = doc.createElement("rules");
        for (final GeneralizedRule r : rules) {
            f.appendChild(TPDB_Exporter.toTPDB(r, doc));
        }
        e.appendChild(f);
        f = doc.createElement("signature");
        final Set<String> sig = new HashSet<String>();
        for (final FunctionSymbol fs : signature) {
            final String name = fs.getName();
            if (sig.add(name)) {
                f.appendChild(TPDB_Exporter.toTPDB(fs, C, AC, A, doc));
            } else {
                throw new NotExpressibleException("Symbol " + name + " occurs with different arities");
            }
        }
        e.appendChild(f);
        return e;
    }

    public static void toTPDB(final QTRSProblem qtrs, final Element e, final Document doc) {
        e.setAttribute("type", "termination");
        e.appendChild(TPDB_Exporter.toTPDB(qtrs.getR(), qtrs.getSignature(), doc));
        final QTermSet q = qtrs.getQ();
        Element f = doc.createElement("strategy");
        if (q.isEmpty()) {
            f.appendChild(doc.createTextNode("FULL"));
        } else if (qtrs.isExactlyInnermost()) {
            f.appendChild(doc.createTextNode("INNERMOST"));
        } else {
            throw new NotExpressibleException("Q is neither full nor innermost rewriting");
        }
        e.appendChild(f);
        f = doc.createElement("startterms");
        f.appendChild(doc.createTextNode("FULL"));
    }

    public static void toTPDB(final OTRSProblem otrs, final Element e, final Document doc) {
        e.setAttribute("type", "termination");
        e.appendChild(TPDB_Exporter.toTPDB(otrs.getR(), CollectionUtils.getFunctionSymbols(otrs.getR()), doc));
        Element f = doc.createElement("strategy");
        f.appendChild(doc.createTextNode("OUTERMOST"));
        e.appendChild(f);
        f = doc.createElement("startterms");
        f.appendChild(doc.createTextNode("FULL"));
    }

    public static void toTPDB(final GTRSProblem gtrs, final Element e, final Document doc) {
        e.setAttribute("type", "termination");
        e.appendChild(TPDB_Exporter.toTPDB(gtrs.getR(), CollectionUtils.getFunctionSymbols(gtrs.getR()), doc));
        Element f = doc.createElement("strategy");
        if (gtrs.getInnermost()) {
            f.appendChild(doc.createTextNode("INNERMOST"));
        } else {
            f.appendChild(doc.createTextNode("FULL"));
        }
        e.appendChild(f);
        f = doc.createElement("startterms");
        f.appendChild(doc.createTextNode("FULL"));
    }

    public static void toTPDB(final CSRProblem csr, final Element e, final Document doc) {
        e.setAttribute("type", "termination");
        e.appendChild(TPDB_Exporter.toTPDB(csr.getR(), null, null, csr.getSignature(), csr.getReplacementMap(), doc));
        Element f = doc.createElement("strategy");
        if (csr.getInnermost()) {
            f.appendChild(doc.createTextNode("INNERMOST"));
        } else {
            f.appendChild(doc.createTextNode("FULL"));
        }
        e.appendChild(f);
        f = doc.createElement("startterms");
        f.appendChild(doc.createTextNode("FULL"));
    }

    public static void toTPDB(final RelTRSProblem rel, final Element e, final Document doc) {
        e.setAttribute("type", "termination");
        e.appendChild(TPDB_Exporter.toTPDB(rel.getR(), rel.getS(), null, rel.getSignature(), null, doc));
        Element f = doc.createElement("strategy");
        f.appendChild(doc.createTextNode("FULL"));
        e.appendChild(f);
        f = doc.createElement("startterms");
        f.appendChild(doc.createTextNode("FULL"));
    }

    public static void toTPDB(final ETRSProblem etrs, final Element e, final Document doc) {
        e.setAttribute("type", "termination");
        if (!etrs.checkACandAandC()) {
            throw new NotExpressibleException("System is no C-A-AC-system, the equations are:\n " + etrs.getE());
        }
        e.appendChild(TPDB_Exporter.toTPDB(etrs.getR(), etrs.getSignature(), etrs.getCSymbols(), etrs.getACSymbols(),
            etrs.getASymbols(), doc));
        Element f = doc.createElement("strategy");
        f.appendChild(doc.createTextNode("FULL"));
        e.appendChild(f);
        f = doc.createElement("startterms");
        f.appendChild(doc.createTextNode("FULL"));
    }

    public static void toTPDB(final CTRSProblem ctrs, final Element e, final Document doc) {
        e.setAttribute("type", "termination");
        final Set<FunctionSymbol> sig = CollectionUtils.getFunctionSymbols(ctrs.getR());
        sig.addAll(CollectionUtils.getFunctionSymbols(ctrs.getC()));
        e.appendChild(TPDB_Exporter.toTPDB(ctrs.getR(), null, ctrs.getC(), sig, null, doc));
        Element f = doc.createElement("strategy");
        f.appendChild(doc.createTextNode("FULL"));
        e.appendChild(f);
        f = doc.createElement("startterms");
        f.appendChild(doc.createTextNode("FULL"));
    }

    public static void toTPDB(final ITRSProblem itrs, final Element e, final Document doc) {
        e.setAttribute("type", "termination");
        final Set<FunctionSymbol> sig = new LinkedHashSet<FunctionSymbol>(itrs.getRuleAnalysis().getFunctionSymbols());
        final IDPPredefinedMap predefinedMap = itrs.getPredefinedMap();
        final Set<FunctionSymbol> predefinedFunctions = new LinkedHashSet<FunctionSymbol>();
        // filter pre-defined function symbols
        for (final FunctionSymbol fs : itrs.getRuleAnalysis().getFunctionSymbols()) {
            if (predefinedMap.isPredefined(fs)) {
                predefinedFunctions.add(fs);
                sig.remove(fs);
            }
        }
        // create TRS-like problem
        final Element problem = TPDB_Exporter.toTPDB(itrs.getR(), sig, doc);
        e.appendChild(problem);

        // add pre-defined semantics
        // obtain signature node
        Node signature = null;
        for (int i = 0; i < problem.getChildNodes().getLength(); i++) {
            final Node el = problem.getChildNodes().item(i);
            if (el.getNodeName().equals("signature")) {
                signature = el;
                break;
            }
        }
        // append pre-defined semantics
        for (final FunctionSymbol fs : predefinedFunctions) {
            signature.appendChild(TPDB_Exporter.toTPDB(fs, predefinedMap, doc));
        }
        Element f = doc.createElement("strategy");
        f.appendChild(doc.createTextNode("INNERMOST"));
        e.appendChild(f);
        f = doc.createElement("startterms");
        f.appendChild(doc.createTextNode("FULL"));
    }

    /**
     * Computes, whether the obligation is representable in the TPDB XML Format.
     */
    // TODO isExportable and toXML should probably be moved to an interface
    public static boolean isExportable(final BasicObligation obl) {
        return obl instanceof QTRSProblem || obl instanceof RuntimeComplexityTrsProblem || obl instanceof OTRSProblem
            || obl instanceof GTRSProblem || obl instanceof CSRProblem || obl instanceof RelTRSProblem
            || obl instanceof ETRSProblem || obl instanceof CTRSProblem || obl instanceof ITRSProblem;
    }

    public static String toXMLString(final BasicObligation obl, final String filename) throws TransformerException,
            ParserConfigurationException {
        final Document doc = TPDB_Exporter.toXMLDocument(obl, filename);
        final TransformerFactory transformerFactory = TransformerFactory.newInstance();
        /* change this for indention */
        final boolean indent = true;
        if (indent) {
            transformerFactory.setAttribute("indent-number", 2);
        }
        final Transformer transformer = transformerFactory.newTransformer();
        if (indent) {
            transformer.setOutputProperty(OutputKeys.INDENT, "yes");
        } else {
            transformer.setOutputProperty(OutputKeys.INDENT, "no");
        }
        final DOMSource source = new DOMSource(doc);
        final StreamResult result = new StreamResult(new StringWriter());
        transformer.transform(source, result);
        return result.getWriter().toString();
    }

    /**
     * @return the name of the temporary file
     */
    public static File toTemporaryXMLFile(final BasicObligation obl) throws TransformerException,
            ParserConfigurationException, IOException {
        final Document doc = TPDB_Exporter.toXMLDocument(obl, null);
        final TransformerFactory transformerFactory = TransformerFactory.newInstance();
        /* change this for indention */
        final boolean indent = true;
        if (indent) {
            transformerFactory.setAttribute("indent-number", 2);
        }
        final Transformer transformer = transformerFactory.newTransformer();
        if (indent) {
            transformer.setOutputProperty(OutputKeys.INDENT, "yes");
        } else {
            transformer.setOutputProperty(OutputKeys.INDENT, "no");
        }
        final DOMSource source = new DOMSource(doc);
        final File tempFile = File.createTempFile("obl", ".xml");
        final FileWriter fw = new FileWriter(tempFile, false);
        final BufferedWriter bw = new BufferedWriter(fw);
        final StreamResult result = new StreamResult(bw);
        transformer.transform(source, result);
        return tempFile;
    }

    public static Document toXMLDocument(final BasicObligation obl, final String filename) throws TransformerException,
            ParserConfigurationException {
        final DocumentBuilderFactory docFact = DocumentBuilderFactory.newInstance();
        docFact.setNamespaceAware(true);
        final SchemaFactory sf = SchemaFactory.newInstance("http://www.w3.org/2001/XMLSchema");
        try {
            final URL url = TPDB_Exporter.class.getResource("/aprove/XML/XSDs/xtc.xsd");
            final Schema s = sf.newSchema(url);
            docFact.setSchema(s);
            docFact.setValidating(true);
        } catch (final SAXException e1) {
            e1.printStackTrace();
            throw new TransformerException("internal error in schema header");
            // } catch (MalformedURLException e) {
            //    throw new TransformerException("internal error in schema");
        }
        final Document doc = docFact.newDocumentBuilder().getDOMImplementation().createDocument("", "problem", null);
        final Element e = doc.getDocumentElement();
        if (obl instanceof QTRSProblem) {
            TPDB_Exporter.toTPDB((QTRSProblem) obl, e, doc);
        } else if (obl instanceof RuntimeComplexityTrsProblem) {
            TPDB_Exporter.toTPDB((RuntimeComplexityTrsProblem) obl, e, doc);
        } else if (obl instanceof OTRSProblem) {
            TPDB_Exporter.toTPDB((OTRSProblem) obl, e, doc);
        } else if (obl instanceof GTRSProblem) {
            TPDB_Exporter.toTPDB((GTRSProblem) obl, e, doc);
        } else if (obl instanceof CSRProblem) {
            TPDB_Exporter.toTPDB((CSRProblem) obl, e, doc);
        } else if (obl instanceof RelTRSProblem) {
            TPDB_Exporter.toTPDB((RelTRSProblem) obl, e, doc);
        } else if (obl instanceof ETRSProblem) {
            TPDB_Exporter.toTPDB((ETRSProblem) obl, e, doc);
        } else if (obl instanceof CTRSProblem) {
            TPDB_Exporter.toTPDB((CTRSProblem) obl, e, doc);
        } else if (obl instanceof ITRSProblem) {
            TPDB_Exporter.toTPDB((ITRSProblem) obl, e, doc);
        } else {
            throw new NotExpressibleException("Unsupported type for XML-translation: " + obl.getClass());
        }
        if (filename != null) {
            final Element f = doc.createElement("metainformation");
            final Element g = doc.createElement("originalfilename");
            g.appendChild(doc.createTextNode(filename));
            f.appendChild(g);
            e.appendChild(f);
        }
        e.setAttribute("xmlns:xsi", "http://www.w3.org/2001/XMLSchema-instance");
        e.setAttribute("xsi:noNamespaceSchemaLocation", "http://dev.aspsimon.org/xtc.xsd");

        return doc;
    }

    private static void toTPDB(final RuntimeComplexityTrsProblem obl, final Element e, final Document doc) {
        e.setAttribute("type", "complexity");
        e.appendChild(TPDB_Exporter.toTPDB(obl.getR(), obl.getSignature(), doc));
        Element f = doc.createElement("strategy");
        switch (obl.getRewriteStrategy()) {
        case INNERMOST:
            f.appendChild(doc.createTextNode("INNERMOST"));
            break;
        case FULL:
            f.appendChild(doc.createTextNode("FULL"));
            break;
        default:
            throw new NotYetHandledException("Don't know what to do with rewrite strategy "
                    + obl.getRewriteStrategy() + '!');
        }
        e.appendChild(f);
        f = doc.createElement("startterm");
        f.appendChild(doc.createElement("constructor-based"));
        e.appendChild(f);
    }

    static class NotExpressibleException extends RuntimeException {
        private static final long serialVersionUID = 2043431880282677269L;

        public NotExpressibleException(final String message) {
            super(message);
        }
    }
}
