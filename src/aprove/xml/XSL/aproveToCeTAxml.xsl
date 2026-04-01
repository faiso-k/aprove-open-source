<?xml version="1.0" encoding="iso-8859-1"?>

<!-- Transforms XML proofs from AProVE into the Haskell format used by CeTA. -->

<!-- author: ulrichsg -->

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
               xmlns:exslt="http://exslt.org/common"
               exclude-result-prefixes="exslt"             
               version="1.0">

  <xsl:output method="xml" indent="yes" omit-xml-declaration="no"/>
  
  
  <!-- Starting point -->
  
  <xsl:template match="/">
    <xsl:element name="proof">
      <xsl:attribute name="xmlns">http://cl-informatik.uibk.ac.at/software/ceta</xsl:attribute>
      <xsl:apply-templates mode="trs" select="/proof-obligation/proposition/proof"/>
    </xsl:element>
  </xsl:template>
  
  
  <!-- *************************************************************************
       ***                            Proofs                                 ***
       ************************************************************************* -->
  
  <!-- After DPTrans, the variable $tuple-symbols has to be carried everywhere.
       Before DPTrans, it doesn't exist, so we need two types of proofs for these
       situations. We start with mode="trs", and the DPTrans proof automatically
       switches it off. --> 
  
  <xsl:template mode="trs" match="proof">
    <xsl:apply-templates mode="trs"/>
  </xsl:template>
  
  <xsl:template match="proof">
    <xsl:param name="tuple-symbols"/>
    <xsl:apply-templates>
      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
    </xsl:apply-templates>
  </xsl:template>
  
  
  <!-- Dependency pair transformation.
       Create $tuple-symbols variable and pass it to subsequent proofs,
       switch trs mode off. -->
  
  <xsl:template mode="trs" match="qtrs-dependency-pairs-proof">
    <xsl:variable name="tuple-symbols">
      <defined-to-tuple>
      <!-- we add some more structure with orig/tuple, than just using symbol[1/2] -->
        <xsl:for-each select="defined-to-tuple-entry">
          <entry>
            <orig><xsl:copy-of select="symbol[1]"/></orig>
            <tupled><xsl:copy-of select="symbol[2]"/></tupled>
          </entry>
        </xsl:for-each>
      </defined-to-tuple>
    </xsl:variable>
    <xsl:variable name="origPairs">
      <xsl:for-each select="rule-to-dps-entry">
        <xsl:for-each select="position-to-dp">
          <xsl:copy-of select="rule"/>
        </xsl:for-each>
      </xsl:for-each>
    </xsl:variable>
    <xsl:element name="dpTrans">      
      <xsl:element name="dps">
	<xsl:element name="rules">
	  <xsl:for-each select="exslt:node-set($origPairs)//rule">
	    <xsl:apply-templates select=".">
              <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
	    </xsl:apply-templates>	      
	  </xsl:for-each>
	</xsl:element>
      </xsl:element>
      
      <xsl:apply-templates select="../../proof-obligation/proposition/proof">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
    </xsl:element>
  </xsl:template>
  
  
  <!-- Non-termination proof -->
  
  <xsl:template mode="trs" match="qtrs-nontermination-proof">
    <xsl:apply-templates/> <!-- call loop -->
  </xsl:template>
  
  
  
  
  
  <!-- P-is-empty proof -->
  
  <xsl:template match="p-is-empty-proof">
    <xsl:param name="tuple-symbols"/>
    <xsl:element name="pIsEmpty"/>
  </xsl:template>
  
  
  <!-- Dependency graph proof -->
  
  <xsl:template match="qdp-dependency-graph-proof">
    <xsl:param name="tuple-symbols"/>
    <xsl:element name="depGraphProc">
      <xsl:choose>
        <xsl:when test="count(graph-scc) = 0"/>
        <xsl:when test="count(graph-scc) = 1">
          <xsl:call-template name="scc">
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            <xsl:with-param name="sccProposition" select="../../proof-obligation/proposition"/>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
          <xsl:call-template name="sccList">
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            <xsl:with-param name="proofTag" select="."/>
          </xsl:call-template>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:element>    
  </xsl:template>
  
  <xsl:template name="scc">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="sccProposition"/>
    <xsl:element name="component">
      <xsl:element name="dps">
	<xsl:element name="rules">
          <xsl:for-each select="$sccProposition/basic-obligation/qdp-termination-obligation/qdp/dps/rule">
            <xsl:apply-templates select=".">
              <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
	    </xsl:apply-templates>
          </xsl:for-each>
        </xsl:element>
      </xsl:element>
      <xsl:choose>
        <xsl:when test="count($sccProposition/proof/non-scc) = 0">
          <xsl:apply-templates select="$sccProposition/proof">
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          </xsl:apply-templates>
        </xsl:when>
      </xsl:choose>
    </xsl:element>
  </xsl:template>
  
  <xsl:template name="sccList">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="proofTag"/>
    <xsl:param name="i" select="count($proofTag/../../proof-obligation/conjunction/proof-obligation)"/>

    <xsl:variable name="num" select="count($proofTag/../../proof-obligation/conjunction/proof-obligation)"/>
    <xsl:call-template name="scc">
      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      <xsl:with-param name="sccProposition" select="$proofTag/../../proof-obligation/conjunction/proof-obligation[$i]/proposition"/>
    </xsl:call-template>
    <xsl:choose>
      <xsl:when test="$i &gt; 1">
        <xsl:call-template name="sccList">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          <xsl:with-param name="proofTag" select="$proofTag"/>
          <xsl:with-param name="i" select="$i - 1"/>
        </xsl:call-template>
      </xsl:when>
    </xsl:choose>      
  </xsl:template>
  
  
  <!-- Reduction pair proof -->
  
  <xsl:template match="qdp-reduction-pair-proof">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="signature"/>
    <xsl:element name="redPairProc">
      
      <xsl:element name="redPair">
	<xsl:apply-templates select="order">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          <xsl:with-param name="signature" select="$signature"/>
	</xsl:apply-templates>
      </xsl:element>
      
      <xsl:element name="dps">
	<xsl:apply-templates select="trs[3]">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
	</xsl:apply-templates>
      </xsl:element>
      
      <xsl:apply-templates select="../../proof-obligation/proposition/proof">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
    </xsl:element>
  </xsl:template>
  
  
  <!-- *************************************************************************
       ***                             Orders                                ***
       ************************************************************************* -->
  
  <xsl:template match="order">
    <xsl:param name="tuple-symbols"/>
    <xsl:apply-templates>
      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
    </xsl:apply-templates>
  </xsl:template>
  
  
  <xsl:template match="polynomial-order">
    <xsl:param name="tuple-symbols"/>
    <xsl:element name="interpretation">
      <xsl:element name="type">
	<xsl:element name="linearPolynomial"/>
      </xsl:element>
      <xsl:element name="domain">
	<xsl:element name="naturals"/>
      </xsl:element>

      <xsl:for-each select="polo-interpretation">
	<xsl:apply-templates select=".">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
	</xsl:apply-templates>
      </xsl:for-each>

    </xsl:element>
  </xsl:template>
  
  
  <xsl:template match="polo-interpretation">
    <xsl:param name="tuple-symbols"/>
    <xsl:element name="interpret">
      <xsl:apply-templates select="symbol">
	<xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
      <xsl:element name="arity">
	<xsl:value-of select="symbol/@arity"/>
      </xsl:element>
      <xsl:apply-templates select="polynomial"/>
    </xsl:element>
  </xsl:template>
  
  <xsl:template match="polynomial">
    <xsl:element name="function">
      <xsl:element name="linearPolynomial">
	<xsl:element name="constant">
	  <xsl:element name="number">
	    <xsl:choose>
              <xsl:when test="count(monomial[count(polo-factor) = 0]) &lt; 1">0</xsl:when>
              <xsl:otherwise>
		<xsl:value-of select="monomial[count(polo-factor) = 0]/integer/@value"/>
              </xsl:otherwise>
	    </xsl:choose>
	  </xsl:element>
	</xsl:element>
	<xsl:choose>
          <xsl:when test="../symbol/@arity &gt; 0">
            <xsl:call-template name="polo-coeffs">
              <xsl:with-param name="polynomial" select="."/>
            </xsl:call-template>
          </xsl:when>
	</xsl:choose>
      </xsl:element>
    </xsl:element>
  </xsl:template>
  
  <xsl:template name="monomial">
    <xsl:param name="polynomial"/>
    <xsl:param name="varIndex"/>
    <xsl:element name="coefficient">
      <xsl:element name="natural">
	<xsl:choose>
	  <xsl:when test="count($polynomial//variable[@name = concat('x_', $varIndex)]) = 0">0</xsl:when>
	  <xsl:otherwise>
            <xsl:apply-templates select="$polynomial/monomial[count(polo-factor/variable[@name = concat('x_', $varIndex)]) &gt; 0]/integer/@value"/>
	  </xsl:otherwise>
	</xsl:choose>
      </xsl:element>
    </xsl:element>
  </xsl:template>
  
  <xsl:template name="polo-coeffs">
    <xsl:param name="polynomial"/>
    <xsl:param name="i" select="1"/>
    <xsl:call-template name="monomial">
      <xsl:with-param name="polynomial" select="$polynomial"/>
      <xsl:with-param name="varIndex" select="$i"/>
    </xsl:call-template>
    <xsl:choose>
      <xsl:when test="$i &lt; $polynomial/../symbol/@arity">
        <xsl:call-template name="polo-coeffs">
          <xsl:with-param name="polynomial" select="$polynomial"/>
          <xsl:with-param name="i" select="$i + 1"/>
        </xsl:call-template>
      </xsl:when>
    </xsl:choose>
  </xsl:template>
  
  
  <!-- ******************************************************************************
       ***                       Term-related structures                          ***
       ****************************************************************************** -->
  
  <!-- Tuple symbols must have the same identifier as the function symbols they
       are derived from. -->
  <xsl:template match="symbol">
    <xsl:param name="tuple-symbols"/>
    <xsl:variable name="ar" select="@arity"/>
    <xsl:variable name="na" select="@name"/>
    <xsl:choose>
      <!-- use exslt:node-set to query generated node of tuple-symbols -->
      <xsl:when test="count(exslt:node-set($tuple-symbols)/defined-to-tuple/entry/tupled/symbol[@name = $na and @arity = $ar]) = 0"> 
        <xsl:element name="name">
          <xsl:value-of select="@name"/>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:element name="name">
          <xsl:attribute name="sharp">true</xsl:attribute>
          <xsl:value-of select="exslt:node-set($tuple-symbols)/defined-to-tuple/entry[count(tupled/symbol[@name = $na and @arity = $ar]) > 0]/orig/symbol/@name"/>              
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template match="variable">
    <xsl:param name="tuple-symbols"/>
    <xsl:element name="var">
      <xsl:value-of select="@name"/>
    </xsl:element>
  </xsl:template>
  
  <xsl:template match="term">
    <xsl:param name="tuple-symbols"/>
    <xsl:apply-templates>
      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
    </xsl:apply-templates>
  </xsl:template>
  
  <xsl:template match="fun-app">
    <xsl:param name="tuple-symbols"/>
    <xsl:element name="funapp">
      <xsl:apply-templates select="symbol">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>      
      <xsl:for-each select="term">
	<xsl:element name="arg">
	  <xsl:apply-templates>
	    <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
	  </xsl:apply-templates>
	</xsl:element>
      </xsl:for-each>
    </xsl:element>
  </xsl:template>
  
  <xsl:template name="arg-list">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="i" select="1"/>
    <xsl:element name="arg">
      <xsl:apply-templates select="term[$i]">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
    </xsl:element>
    <xsl:choose>
      <xsl:when test="$i &lt; count(term)">
        <xsl:variable name="rest-terms">
          <xsl:call-template name="arg-list">
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            <xsl:with-param name="i" select="$i + 1"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:value-of select="concat(', ', $rest-terms)"/>
      </xsl:when>
    </xsl:choose>
  </xsl:template>
  
  <!-- Rules -->
  
  <xsl:template match="rule">
    <xsl:param name="tuple-symbols"/>
    <xsl:element name="rule">
      <xsl:element name="lhs">
	<xsl:apply-templates select="term[1]">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
	</xsl:apply-templates>
      </xsl:element>
      <xsl:element name="rhs">
	<xsl:apply-templates select="term[2]">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
	</xsl:apply-templates>
      </xsl:element>
    </xsl:element>
  </xsl:template>
  
  
  <xsl:template match="trs">
    <xsl:param name="tuple-symbols"/>
    <xsl:element name="rules">
      <xsl:for-each select="rule">
        <xsl:apply-templates select=".">
	  <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        </xsl:apply-templates>
      </xsl:for-each>
    </xsl:element>
  </xsl:template>
  
  
  
  
</xsl:stylesheet>
