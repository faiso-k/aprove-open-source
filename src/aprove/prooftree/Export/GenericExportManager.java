package aprove.prooftree.Export;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Created on 19.07.2005 by marmer
 *
 * @author Martin Mertens
 */

public class GenericExportManager extends ExportManager {
    private boolean pdflatex;

    public GenericExportManager(ObligationNode root, String fn, boolean pdflatex) {
        super(root, fn);
        this.pdflatex = pdflatex;
    }

    public GenericExportManager(ObligationAndStrategy pair, boolean pdflatex) {
        super(pair.getRoot(), pair.getPathName());
        this.pdflatex = pdflatex;
    }

    public String export(Export_Util o) {
        //System.out.print("Starting export...");
        StringBuilder result = new StringBuilder();
        result.append(this.generateHeader(o));
        result.append(o.linebreak());
        if(this.proofPurposeDescriptor != null){
            result.append(this.proofPurposeDescriptor.export(o));
            result.append(o.linebreak());
        }
        this.mainExport(o, result);

        result.append(o.linebreak());
        result.append(this.generateFooter(o));
        //System.out.println("finished.");
        //System.out.println(result.toString());
        return result.toString();
    }

    private void mainExport(Export_Util o, StringBuilder result) {
        this.recursiveMainExport(this.proofTreeRoot, o, "O", result);
    }

    private void recursiveMainExport(ObligationNode node, Export_Util o, String currentLabel, StringBuilder result) {
        if (node instanceof BasicObligationNode) {
            BasicObligationNode oblNode = (BasicObligationNode) node;
            BasicObligation obligation = oblNode.getBasicObligation();
            result.append(o.linebreak());
            if (o instanceof LaTeX_Util) {
                result.append("\\vspace*{15pt}");
            }
            this.generateTreeToNode(node, o, result);
            result.append(o.linebreak());
            result.append(obligation.export(o));

            result.append(o.linebreak());

            int counter = 1;
            for (ObligationNodeChild child : oblNode.getSuccessors()) {
                Proof proof = child.getProof();
                result.append(proof.export(o));
                result.append(o.linebreak());
                ObligationNode childObl = child.getNewObligation();
                String newlabel = currentLabel + (counter++) + "O";
                this.recursiveMainExport(childObl, o, newlabel, result);
            }
        } else if (node instanceof JunctorObligationNode) {
            int counter = 1;
            for (ObligationNode child : ((JunctorObligationNode) node).getChildren()) {
                result.append(o.linebreak());
                String newlabel = currentLabel + (counter++) + "O";
                this.recursiveMainExport(child, o, newlabel, result);
            }
        }

    }

    private void generateTreeToNode(ObligationNode model, Export_Util o, StringBuilder tree) {
        this.recursiveGenerateTreeToNode(this.proofTreeRoot, model, o, 0, tree);
    }

    private Boolean recursiveGenerateTreeToNode(
            ObligationNode current,
            ObligationNode goal,
            Export_Util o,
            int indent,
            StringBuilder result) {
        StringBuilder tree = new StringBuilder();
        this.generateRepresentation(current == goal, current.getRepresentation(), o, indent, tree);
        boolean isOnMainPath = false;
        if (current == goal) {
            isOnMainPath = true;
        }

        /*
         * If we have a basic obligation, check all successors if they are on
         * the main path and generate the proof tree overview for them at the
         * same time. Later, we choose the right output and append it.
         */
        if (current instanceof BasicObligationNode) {
            List<Triple<Boolean, ObligationNodeChild, StringBuilder>> childList =
                new ArrayList<Triple<Boolean, ObligationNodeChild, StringBuilder>>();
            BasicObligationNode basObl = (BasicObligationNode) current;

            for (ObligationNodeChild child : basObl.getSuccessors()) {
                ObligationNode newObl = child.getNewObligation();
                StringBuilder sb = new StringBuilder();
                boolean childLeadsToGoal = this.recursiveGenerateTreeToNode(newObl, goal, o, (indent + 2), sb);
                Triple<Boolean, ObligationNodeChild, StringBuilder> childTriple =
                    new Triple<Boolean, ObligationNodeChild, StringBuilder>(childLeadsToGoal, child, sb);
                childList.add(childTriple);
                if (childLeadsToGoal) {
                    isOnMainPath = true;
                }
            }

            /*
             * If we are on the main path, show something: If it's the proving
             * child we add the proof and the pre-computed result for the child.
             */
            if (isOnMainPath) {
                for (Triple<Boolean, ObligationNodeChild, StringBuilder> triple: childList) {
                    if (triple.x || current == goal) { //Is proving
                        this.generateRepresentation(
                                false,
                                triple.y.getProof().getName(NameLength.SHORT),
                                o,
                                (indent + 1),
                                tree);
                    }
                    if (triple.x) {
                        tree.append(triple.z);
                    }
                }
            }
        } else if (current instanceof JunctorObligationNode) {
            List<Triple<Boolean, ObligationNode, StringBuilder>> childList =
                new ArrayList<Triple<Boolean, ObligationNode, StringBuilder>>();
            JunctorObligationNode junctorObl = (JunctorObligationNode) current;
            for (ObligationNode child : junctorObl.getChildren()) {
                StringBuilder sb = new StringBuilder();
                boolean childLeadsToGoal = this.recursiveGenerateTreeToNode(child, goal, o, (indent + 1), sb);
                Triple<Boolean, ObligationNode, StringBuilder> childTriple =
                    new Triple<Boolean, ObligationNode, StringBuilder>(childLeadsToGoal, child, sb);
                childList.add(childTriple);
                if (childLeadsToGoal) {
                    isOnMainPath = true;
                }
            }

            /*
             * If we are on the main path, show something: If it's the proving
             * child we add the proof and the pre-computed result for the child.
             */
            if (isOnMainPath) {
                for (Triple<Boolean, ObligationNode, StringBuilder> triple: childList) {
                    this.generateRepresentation(
                            triple.y == goal,
                            triple.y.getRepresentation(),
                            o,
                            (indent + 1),
                            tree);
                    if (triple.x) { //Is proving
                        tree.append(triple.z);
                    }
                }
            }
        }
        result.append(tree);
        return isOnMainPath;
    }

    private void generateRepresentation(boolean important, String representation, Export_Util o, int indent, StringBuilder tree) {

        if (o instanceof LaTeX_Util) {
            tree.append("{\\footnotesize");
        }

        if (important) {
            representation = o.bold(representation);
            if (o instanceof LaTeX_Util) {
                representation = "\\underline{"+representation+"}";
            }
        }

        if (o instanceof HTML_Util) {
            String space = "";
            for (int i=0; i<indent; i++) {
                space += "  ";
            }
            tree.append("<pre>"+space+"&#8627; "+representation+"</pre>");
        } else if (o instanceof LaTeX_Util) {
            int i= indent*5;
            tree.append("\\hspace*{"+i+"pt}$\\hookrightarrow$\\texttt{"+representation+"}\\linebreak\n\\vspace*{-3pt}");

        } else if (o instanceof PLAIN_Util) {
            String space = "";
            for (int i=0; i<indent; i++) {
                space += "  ";
            }
            tree.append(space+"- "+representation+"\n");
        }

        if (o instanceof LaTeX_Util) {
            tree.append("}");
        }
    }


    private String generateHeader(Export_Util o){

        if (o instanceof HTML_Util) {
            String s = ExportTemplates.FRAME_HEAD_START;
            if (this.purpose != null){
                s += this.purpose + " ";
            }
            s += "proof of "+this.fileName+ExportTemplates.HEAD_END+ExportTemplates.BODY_OPEN;
            s += "\n<!-- " + this.getCommitDescription() + "-->\n";
            return s;
        } else if (o instanceof LaTeX_Util) {

            String s = "\\documentclass[a4paper,10pt]{article}\n\n";
            if (this.pdflatex) {
                s += "\n\n% ATTENTION: PLEASE COMPILE THIS DOCUMENT WITH PDFLATEX! \n";
            } else {
                s += "\n\n% ATTENTION: IF YOU USE  DVIPS PLEASE USE THE -R0 OPTION (dvips -R0 filename.dvi)! \n";
            }
                  s += "\n\n% ATTENTION: IF YOU USE  XDVI  PLEASE USE THE -allowshell OPTION (xdvi -allowshell filename.dvi)! \n";
            s += "\n\n% You should also compile this document with bibtex to get the references! \n\n\n\n";
            s += "\n% " + this.getCommitDescription() + "\n";
            // add new packages here!!!
            s += "\\usepackage{a4wide,amsfonts, amsmath, amssymb, latexsym, graphicx, isolatin1, color, longtable}\n";
            s += "\\usepackage[all]{xy}\n\n";
            // add new page layouts here!!!
            s += "\\parindent=0mm\n\n";
            s += "\\parskip=3mm";
            s += "\\newlength{\\scale}\\setlength{\\scale}{\\textwidth}\\addtolength{\\scale}{-\\leftmargin}\n\n";
            // alternative latex code instead of pdflatex
            if (!this.pdflatex) {
                s += "\\DeclareGraphicsRule{.dot}{eps}{*}{`dot -Tps #1 }\n\n";
            }
            // add newcommands here!!!
            s += "\\newcommand{\\R}[0]{\\mathcal{R}}\n";
            s += "\\newcommand{\\E}[0]{\\mathcal{E}}\n";
            s += "\\newcommand{\\aprove}[0]{\\textsf{AProVE}\\footnote{\\texttt{http://www-i2.informatik.rwth-aachen.de/AProVE}}}\n\n";
            s += "\\definecolor{lightgray}{gray}{0.8}\n";
            s += "\\newcommand{\\lightgray}{\\color{lightgray}}\n\n";

                // haskell commands
                s += "\\newlength{\\hssize}\n";
                s += "\\newlength{\\hssizeC}\n";
                s += "\\settoheight{\\hssizeC}{\\mbox{$\\mbox{P}$}}\n";
                s += "\\addtolength{\\hssizeC}{-0.72pt}\n";
                s += "\\newcommand{\\hsraise}[2]{\n";
                s += "\\settoheight{\\hssize}{$#2$}\n";
                s += "\\addtolength{\\hssize}{-\\hssizeC}\n";
                s += "\\raisebox{2\\hssize}{$#1$}\\raisebox{\\hssize}{$#2$}\n";
                s += "}\n";
                s += "\\newcommand{\\hslow}[1]{\n";
                s += "\\settoheight{\\hssize}{$#1$}\n";
                s += "\\addtolength{\\hssize}{-\\hssizeC}\n";
                s += "\\raisebox{-\\hssize}{$#1$}\n";
                s += "}\n";

            // begin of document
            s += "\\begin{document}\n\n";
            s += "% turn of parindent\n\n";
            s += "\\parindent = 0pt\n\n";
            // headline
            s += "\\section*{";
            if(this.purpose != null){
                s+=this.purpose + " ";
            }
            s+= "proof with \\aprove}\n\n";
            return s;
            } else if (o instanceof PLAIN_Util) {
                return "\n# " + this.getCommitDescription() + "\n";
            }
        return "";
      }

    private String generateFooter(Export_Util o) {
        if (o instanceof HTML_Util) {
            return ExportTemplates.RENDERDOT_SCRIPT + ExportTemplates.BODY_CLOSE + ExportTemplates.HTML_CLOSE;
        } else if (o instanceof LaTeX_Util) {
            return "\\end{document}";
        } else if (o instanceof PLAIN_Util) {

        }
        return "";
    }

}
