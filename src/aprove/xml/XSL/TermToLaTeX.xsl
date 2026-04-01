<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.0" >
  <xsl:output xmlns:xsl="http://www.w3.org/1999/XSL/Transform" method="text" />
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="/" ><![CDATA[\documentclass[a4paper,10pt]{article}
% ATTENTION: IF YOU USE  DVIPS PLEASE USE THE -R0 OPTION (dvips -R0 filename.dvi)!
% ATTENTION: IF YOU USE  XDVI  PLEASE USE THE -allowshell OPTION (xdvi -allowshell filename.dvi)!
% You should also compile this document with bibtex to get the references!
\usepackage{a4wide,amsfonts, amsmath, amssymb, latexsym, graphicx, isolatin1, color, longtable}
\usepackage[all]{xy}
\parindent=0mm
\newlength{\scale}\setlength{\scale}{\textwidth}\addtolength{\scale}{-\leftmargin}
\DeclareGraphicsRule{.dot}{eps}{*}{`dot -Tps #1 }
\newcommand{\R}[0]{\mathcal{R}}
\newcommand{\E}[0]{\mathcal{E}}	  
\newcommand{\aprove}[0]{\textsf{AProVE}\footnote{\texttt{http://www-i2.informatik.rwth-aachen.de/AProVE}}}
\definecolor{lightgray}{gray}{0.8}
\newcommand{\lightgray}{\color{lightgray}}
\begin{document}
% turn of parindent
\parindent = 0pt
$$]]><xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform"/><![CDATA[$$
\end{document}]]></xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Term" >
    <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="Varsym|Defsym|Conssym|Tuplesym" />
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Varsym" >
    <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="text()" />
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Defsym[@infix=&quot;yes&quot;]" >
    <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform">(</xsl:text>
    <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="../Term[1]" /><![CDATA[\mathsf{]]><xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="text()" /><![CDATA[}]]><xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="../Term[2]" />)
</xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Defsym[@infix=&quot;no&quot;]" ><![CDATA[\mathsf{]]><xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="text()" /><![CDATA[}]]><xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(../Term) > 0" >
      <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform">(</xsl:text>
      <xsl:for-each xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="../Term" >
        <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="Varsym|Defsym|Conssym" />
        <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="not(position() = last())" >
          <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform">, </xsl:text>
        </xsl:if>
      </xsl:for-each>
      <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform">)</xsl:text>
    </xsl:if>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Conssym[@infix=&quot;yes&quot;]" >
    <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform">(</xsl:text>
    <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="../Term[1]" /><![CDATA[\mathsf{]]><xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="text()" /><![CDATA[}]]><xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="../Term[2]" />)
</xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Conssym[@infix=&quot;no&quot;]" ><![CDATA[\mathsf{]]><xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="text()" /><![CDATA[}]]><xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(../Term) > 0" >
      <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform">(</xsl:text>
      <xsl:for-each xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="../Term" >
        <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="Varsym|Defsym|Conssym" />
        <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="not(position() = last())" >
          <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform">, </xsl:text>
        </xsl:if>
      </xsl:for-each>
      <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform">)</xsl:text>
    </xsl:if>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="text()" >
    <xsl:value-of xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="normalize-space()" />
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Tuplesym[@infix=&quot;yes&quot;]" >
    <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform">(</xsl:text>
    <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="../Term[1]" /><![CDATA[\mathsf{]]><xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="text()" /><![CDATA[}]]><xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="../Term[2]" />)
</xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Tuplesym[@infix=&quot;no&quot;]" ><![CDATA[\mathsf{]]><xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="text()" /><![CDATA[}]]><xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(../Term) > 0" >
      <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform">(</xsl:text>
      <xsl:for-each xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="../Term" >
        <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="Varsym|Defsym|Conssym|Tuplesym" />
        <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="not(position() = last())" >
          <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform">, </xsl:text>
        </xsl:if>
      </xsl:for-each>
      <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform">)</xsl:text>
    </xsl:if>
  </xsl:template>
</xsl:stylesheet>
