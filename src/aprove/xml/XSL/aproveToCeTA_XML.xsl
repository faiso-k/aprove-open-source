<?xml version="1.0" encoding="iso-8859-1"?>

<!-- Transforms XML proofs from AProVE into the XML format used by CeTA.
-->

<!-- author: ckuknat -->

<xsl:transform xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
               xmlns:exslt="http://exslt.org/common"
               exclude-result-prefixes="exslt"
               version="2.0">

  <xsl:output method="xml"/>


  <!-- Starting point -->

  <xsl:template match="/">
    <proof>
      <xsl:apply-templates mode="trs" select="/proof-obligation/proposition/proof"/>
    </proof>
  </xsl:template>


  <!-- *************************************************************************
       ***                            Proofs                                 ***
       *************************************************************************
-->

  <!-- After DPTrans, the variable $tuple-symbols has to be carried everywhere.
       Before DPTrans, it doesn't exist, so we need two types of proofs for these
       situations. We start with mode="trs", and the DPTrans proof automatically
       switches it off.
-->

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
       switch trs mode off.
-->

  <xsl:template mode="trs" match="qtrs-dependency-pairs-proof">
    <xsl:variable name="tuple-symbols">
      <defined-to-tuple>
      <!-- we add some more structure with orig/tuple, than just using symbol[1/2]
-->
        <xsl:for-each select="defined-to-tuple-entry">
          <entry>
            <orig><xsl:copy-of select="symbol[1]"/></orig>
            <tupled><xsl:copy-of select="symbol[2]"/></tupled>
          </entry>
        </xsl:for-each>
      </defined-to-tuple>
    </xsl:variable>
    <dpTrans>
      <xsl:variable name="origPairs">
        <xsl:for-each select="rule-to-dps-entry">
          <xsl:for-each select="position-to-dp">
            <xsl:copy-of select="rule"/>
          </xsl:for-each>
        </xsl:for-each>
      </xsl:variable>
      <dps>
        <rules>
          <xsl:call-template name="ruleset">
            <xsl:with-param name="rules" select="$origPairs"/>
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          </xsl:call-template>
        </rules>
      </dps>
      <xsl:apply-templates select="../../proof-obligation/proposition/proof">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
    </dpTrans>
  </xsl:template>


  <!-- Non-termination proof -->

  <xsl:template mode="trs" match="qtrs-nontermination-proof">
    <xsl:choose>
      <xsl:when test="count(loop)=0">
        <notWellFormed/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="loop">
    <loop>
      <xsl:apply-templates select="substitution"/>
      <xsl:apply-templates select="context"/>
      <xsl:call-template name="termList">
        <xsl:with-param name="parent" select="."/>
        <xsl:with-param name="stop" select="count(term) - 1"/>
      </xsl:call-template>
    </loop>
  </xsl:template>


  <!-- Converts a list of <term> elements that are found below a common parent.
       Params: $parent - parent element of the terms; $start - index of the first
       term to be included in the output; $stop - ditto for the last term
-->
  <xsl:template name="termList">
    <xsl:param name="parent"/>
    <xsl:param name="start" select="1"/>
    <xsl:param name="stop" select="count($parent/term)"/>
    <xsl:choose>
      <xsl:when test="$start &gt; $stop">
        <xsl:text/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates mode="nosharp" select="$parent/term[$start]"/>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:choose>
      <xsl:when test="$start &lt; $stop">
        <xsl:call-template name="termList">
          <xsl:with-param name="parent" select="$parent"/>
          <xsl:with-param name="start" select="$start + 1"/>
          <xsl:with-param name="stop" select="$stop"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- context = Hole | More symbol term* subcontext term* -->
  <xsl:template match="context">
    <xsl:choose>
      <xsl:when test="count(symbol) = 0">
        <box/>
      </xsl:when>
      <xsl:otherwise>
        <funContext>
          
          <!-- TODO verify that only the symbol (name) of the actual root is taken for the template  -->
	      <xsl:apply-templates mode="nosharp" select="./symbol"/>
          
          <xsl:variable name="numLeftTerms">
            <xsl:call-template name="countLeftTerms"/>
          </xsl:variable>	
          <before>     
            <xsl:choose>
	          <xsl:when test="$numLeftTerms = 0">
	            <xsl:text/>
	          </xsl:when>
	          <xsl:otherwise>
	            <xsl:call-template name="termList">
	              <xsl:with-param name="parent" select="."/>
	              <xsl:with-param name="stop" select="$numLeftTerms"/>
	            </xsl:call-template>
	          </xsl:otherwise>
	        </xsl:choose>
	      </before>
          <xsl:apply-templates select="context"/>
          <after>
	        <xsl:choose>
	          <xsl:when test="$numLeftTerms = symbol/@arity - count(context/box)">
	            <xsl:text/>
	          </xsl:when>
	          <xsl:otherwise>
	            <xsl:call-template name="termList">
	              <xsl:with-param name="parent" select="."/>
	              <xsl:with-param name="start" select="$numLeftTerms + 1"/>
	            </xsl:call-template>
	          </xsl:otherwise>
	        </xsl:choose>
	      </after>
        </funContext>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- Determines the number of <term> children in the current <context> element that come before
       the sub-<context>.
       Apparently, there is no easier way in XSLT to compute this.
-->
  <xsl:template name="countLeftTerms">
    <xsl:param name="i" select="1"/>
    <xsl:param name="total" select="0"/>
    <xsl:choose>
      <xsl:when test="*[$i]/local-name() = 'context'">
        <xsl:number value="$total"/>
      </xsl:when>
      <xsl:when test="*[$i]/local-name() = 'term'">
        <xsl:call-template name="countLeftTerms">
          <xsl:with-param name="i" select="$i+1"/>
          <xsl:with-param name="total" select="$total + 1"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="countLeftTerms">
          <xsl:with-param name="i" select="$i+1"/>
          <xsl:with-param name="total" select="$total"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="substitution">
    <substitution>
      <xsl:choose>
        <xsl:when test="count(substitute) &gt; 0">
          <xsl:call-template name="substitutes">
            <xsl:with-param name="parent" select="."/>
          </xsl:call-template>
        </xsl:when>
        <!-- No substitutions which could be generated -->
        <xsl:otherwise><xsl:text/></xsl:otherwise>
      </xsl:choose>
    </substitution>
  </xsl:template>

  <xsl:template name="substitutes">
    <xsl:param name="parent"/>
    <xsl:param name="i" select="1"/>
    <substEntry>
      <xsl:apply-templates mode="nosharp" select="$parent/substitute[$i]/variable"/>
      <xsl:apply-templates mode="nosharp" select="$parent/substitute[$i]/term"/>
    </substEntry>
    <xsl:choose>
      <xsl:when test="$i &lt; count($parent/substitute)">
	    <xsl:call-template name="substitutes">
	      <xsl:with-param name="parent" select="$parent"/>
	      <xsl:with-param name="i" select="$i + 1"/>
	    </xsl:call-template>
      </xsl:when>
      <!-- No more substitutes left -->
      <xsl:otherwise><xsl:text/></xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- R-is-empty -->

  <xsl:template mode="trs" match="r-is-empty-proof">
    <xsl:param name="tuple-symbols"/>
    <rIsEmpty/>
  </xsl:template>

  <!-- P-is-empty proof -->

  <xsl:template match="p-is-empty-proof">
    <xsl:param name="tuple-symbols"/>
    <pIsEmpty/>
  </xsl:template>

  <!-- Dependency graph proof -->
  
  <xsl:template match="qdp-dependency-graph-proof">
    <xsl:param name="tuple-symbols"/>
    <depGraphProc>
      <xsl:choose>
        <xsl:when test="count(graph-scc) = 0">
          <xsl:text/>
        </xsl:when>
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
    </depGraphProc>
  </xsl:template>
  
  <xsl:template name="scc">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="sccProposition"/>
    <component>
      <dps>
        <rules>
          <xsl:apply-templates select="$sccProposition/basic-obligation/qdp-termination-obligation/qdp/dps/rule">
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          </xsl:apply-templates>
        </rules>
      </dps>
       <xsl:choose>
        <xsl:when test="count($sccProposition/proof/non-scc) = 0">
          <xsl:apply-templates select="$sccProposition/proof">
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          </xsl:apply-templates>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text/>
        </xsl:otherwise>
      </xsl:choose>
    </component>
  </xsl:template>
  
  <xsl:template name="sccList">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="proofTag"/>
    <xsl:param name="i" select="1"/>
    <xsl:variable name="num" select="count($proofTag/../../proof-obligation/conjunction/proof-obligation)"/>
    <xsl:call-template name="scc">
      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      <xsl:with-param name="sccProposition" select="$proofTag/../../proof-obligation/conjunction/proof-obligation[$i]/proposition"/>
    </xsl:call-template>
    <xsl:choose>
      <xsl:when test="$i &lt; count($proofTag/../../proof-obligation/conjunction/proof-obligation)">
        <xsl:call-template name="sccList">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          <xsl:with-param name="proofTag" select="$proofTag"/>
          <xsl:with-param name="i" select="$i + 1"/>
        </xsl:call-template>        
      </xsl:when>
      <xsl:otherwise>
        <xsl:text/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- Reduction pair proof -->

  <xsl:template match="qdp-reduction-pair-proof">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="signature"/>
    <xsl:choose>
      <!-- Test if the set of usable rules is equal to the set of the qdp -->
      <xsl:when test="count(trs[1]/rule) &lt; count(../../basic-obligation/qdp-termination-obligation/qdp/trs/rule)">
        <redPairUrProc>
          <redPair>
            <xsl:apply-templates select="order">
              <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
              <xsl:with-param name="signature" select="$signature"/>
            </xsl:apply-templates>
          </redPair>
          <dps>
            <xsl:apply-templates select="trs[3]">
              <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            </xsl:apply-templates>
          </dps>
          <usableRules>
            <xsl:apply-templates select="trs[1]">
              <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            </xsl:apply-templates>
          </usableRules>
          <xsl:apply-templates select="../../proof-obligation/proposition/proof">
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          </xsl:apply-templates>
        </redPairUrProc>
      </xsl:when>
      <xsl:otherwise>
        <redPairProc>
          <redPair>
            <xsl:apply-templates select="order">
              <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
              <xsl:with-param name="signature" select="$signature"/>
            </xsl:apply-templates>
          </redPair>
          <dps>
            <xsl:apply-templates select="trs[3]">
              <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            </xsl:apply-templates>
          </dps>
          <xsl:apply-templates select="../../proof-obligation/proposition/proof">
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          </xsl:apply-templates>
        </redPairProc>  
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
 
  <!-- Rule removal proof -->
  
  <xsl:template mode="trs" match="qtrs-rule-removal-proof">
    <ruleRemoval>
      <redPair>
        <xsl:apply-templates mode="nosharp" select="order"/>
      </redPair>
      <trs>
        <!-- trs[2] are the REMAINING rules, that CeTA wants to have -->
        <xsl:apply-templates mode="nosharp" select="trs[2]"/>
      </trs>
      <xsl:apply-templates mode="trs" select="../../proof-obligation/proposition/proof"/>
    </ruleRemoval>  
  </xsl:template>


  <!-- *************************************************************************
       ***                             Orders                                ***
       *************************************************************************
-->

  <xsl:template match="order">
    <xsl:param name="tuple-symbols"/>
    <xsl:apply-templates>
      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
    </xsl:apply-templates>
  </xsl:template>
  
  <xsl:template mode="nosharp" match="order">
    <xsl:apply-templates mode="nosharp"/>
  </xsl:template>
  
  <xsl:template match="polynomial-order">
    <xsl:param name="tuple-symbols"/>
    <interpretation>
      <type>
        <linearPolynomial/>
      </type>
      <domain>
        <naturals/>
      </domain>
      <xsl:call-template name="polo-mappings">
        <xsl:with-param name="order" select="."/>
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:call-template>
    </interpretation>
  </xsl:template>

  <xsl:template mode="nosharp" match="polynomial-order">
    <interpretation>
      <type>
        <linearPolynomial/>
      </type>
      <domain>
        <naturals/>
      </domain>
      <xsl:call-template name="polo-mappings-nosharp">
        <xsl:with-param name="order" select="."/>
      </xsl:call-template>
    </interpretation>
  </xsl:template>
  
  <xsl:template name="polo-mappings">
    <xsl:param name="order"/>
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="i" select="1"/>
    <xsl:apply-templates select="$order/polo-interpretation[$i]">
      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
    </xsl:apply-templates>
    <xsl:choose>
      <xsl:when test="$i &lt; count($order/polo-interpretation)">
        <xsl:call-template name="polo-mappings">
          <xsl:with-param name="order" select="$order"/>
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          <xsl:with-param name="i" select="$i + 1"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template name="polo-mappings-nosharp">
    <xsl:param name="order"/>
    <xsl:param name="i" select="1"/>
    <xsl:apply-templates mode="nosharp" select="$order/polo-interpretation[$i]"/>
    <xsl:choose>
      <xsl:when test="$i &lt; count($order/polo-interpretation)">
        <xsl:call-template name="polo-mappings-nosharp">
          <xsl:with-param name="order" select="$order"/>
          <xsl:with-param name="i" select="$i + 1"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="polo-interpretation">
    <xsl:param name="tuple-symbols"/>
    <interpret>
      <xsl:apply-templates select="symbol">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
      <xsl:apply-templates select="polynomial"/>
    </interpret>
  </xsl:template>
  
  <xsl:template mode="nosharp" match="polo-interpretation">
    <interpret>
      <xsl:apply-templates mode="nosharp" select="symbol"/>
      <xsl:apply-templates select="polynomial"/>
    </interpret>
  </xsl:template>

  <xsl:template match="polynomial">
    <arity>
        <xsl:value-of select="../symbol/@arity"/>
      </arity>
    <xsl:call-template name="function"/>
  </xsl:template>
  
  <xsl:template name="function">
    <function>
      <linearPolynomial>
        <xsl:call-template name="constant"/>
        <xsl:choose>
          <xsl:when test="../symbol/@arity = 0">
            <xsl:text/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:call-template name="polo-coeffs">
              <xsl:with-param name="polynomial" select="."/>
            </xsl:call-template>
          </xsl:otherwise>
        </xsl:choose>
      </linearPolynomial>
    </function>
  </xsl:template>
  
  <xsl:template name="constant">
    <constant>
      <number>
        <xsl:choose>
          <xsl:when test="count(monomial[count(polo-factor) = 0]) &lt; 1">
            <xsl:text>0</xsl:text>
          </xsl:when>
          <xsl:otherwise>
            <xsl:apply-templates select="monomial[count(polo-factor) = 0]/integer"/>
          </xsl:otherwise>
        </xsl:choose>
      </number>
    </constant>  
  </xsl:template>

  <xsl:template name="polo-coeffs">
    <xsl:param name="polynomial"/>
    <xsl:param name="i" select="1"/>
    <xsl:if test="$i &lt;= $polynomial/../symbol/@arity">
      <coefficient>
        <natural>
          <xsl:call-template name="monomial">
            <xsl:with-param name="polynomial" select="$polynomial"/>
            <xsl:with-param name="varIndex" select="$i"/>
          </xsl:call-template>
        </natural>
      </coefficient>
    </xsl:if>
    <xsl:choose>
      <xsl:when test="$i &lt; $polynomial/../symbol/@arity">
        <xsl:call-template name="polo-coeffs">
          <xsl:with-param name="polynomial" select="$polynomial"/>
          <xsl:with-param name="i" select="$i + 1"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template name="monomial">
    <xsl:param name="polynomial"/>
    <xsl:param name="varIndex"/>
    <xsl:choose>
      <!-- Count if there are coefficients -->
      <xsl:when test="count($polynomial//variable[@name = concat('x_', $varIndex)]) = 0">
        <xsl:text>0</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates select="$polynomial/monomial[count(polo-factor/variable[@name = concat('x_', $varIndex)]) &gt; 0]/integer"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>


  <!-- ******************************************************************************
       ***                       Term-related structures                          ***
       ******************************************************************************
-->

  <!-- Tuple symbols must have the same identifier as the function symbols they
       are derived from.
-->
  <xsl:template  >
    <xsl:param name="tuple-symbols"/>
    <xsl:variable name="ar" select="@arity"/>
    <xsl:variable name="na" select="@name"/>
    <xsl:choose>
      <!-- use exslt:node-set to query generated node of tuple-symbols -->
      <xsl:when test="count(exslt:node-set($tuple-symbols)/defined-to-tuple/entry/tupled/symbol[@name = $na and @arity = $ar]) = 0">
        <name>
          <xsl:value-of select="@name"/>
        </name>
      </xsl:when>
      <xsl:otherwise>
        <name sharp="true">
          <xsl:value-of select="exslt:node-set($tuple-symbols)/defined-to-tuple/entry[count(tupled/symbol[@name = $na and @arity = $ar]) > 0]/orig/symbol/@name"/>
        </name>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template mode="nosharp" match="symbol">
    <name>
      <xsl:value-of select="@name"/>
    </name>
  </xsl:template>
  
  <xsl:template match="variable">
    <xsl:param name="tuple-symbols"/>
    <var>
      <xsl:value-of select="@name"/>
    </var>
  </xsl:template>
  
  <xsl:template mode="nosharp" match="variable">
    <var>
      <xsl:value-of select="@name"/>
    </var>
  </xsl:template>

  <xsl:template match="term">
    <xsl:param name="tuple-symbols"/>
    <xsl:apply-templates>
      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
    </xsl:apply-templates>
  </xsl:template>
  
  <xsl:template mode="nosharp" match="term">
    <xsl:apply-templates mode="nosharp"/>
  </xsl:template>

  <xsl:template match="fun-app">
    <xsl:param name="tuple-symbols"/>
    <funapp>
      <xsl:apply-templates select="symbol">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
      <xsl:call-template name="arg-list">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:call-template>
    </funapp>
  </xsl:template>
  
  <xsl:template mode="nosharp" match="fun-app">
    <funapp>
      <xsl:apply-templates mode="nosharp" select="symbol"/>
      <xsl:call-template name="arg-list-nosharp"/>
    </funapp>
  </xsl:template>

  <xsl:template name="arg-list">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="i" select="1"/>
    <xsl:if test="$i &lt;= count(term)">
      <arg>
        <xsl:apply-templates select="term[$i]">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        </xsl:apply-templates>
      </arg>
    </xsl:if>
    <xsl:choose>
      <xsl:when test="$i &lt; count(term)">
        <xsl:call-template name="arg-list">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          <xsl:with-param name="i" select="$i + 1"/>
        </xsl:call-template>
      </xsl:when>
      <!--No more arguments left-->
      <xsl:otherwise><xsl:text/></xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- A duplicated version of term and its dependencies for scenarios
       where tuple-symbols is not present (such as non-termination
       proofs, which operate on TRSs rather than QDPs)
-->

  <xsl:template name="arg-list-nosharp">
    <xsl:param name="i" select="1"/>
    <xsl:if test="$i &lt;= count(term)">
      <arg>
        <xsl:apply-templates mode="nosharp" select="term[$i]"/>
      </arg>
    </xsl:if>
    <xsl:choose>
      <xsl:when test="$i &lt; count(term)">
        <xsl:call-template name="arg-list-nosharp">
          <xsl:with-param name="i" select="$i + 1"/>
        </xsl:call-template>
      </xsl:when>
      <!--No more arguments left-->
      <xsl:otherwise><xsl:text/></xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- Rules -->

  <xsl:template match="rule">
    <xsl:param name="tuple-symbols"/>
    <rule>
      <lhs>
        <xsl:apply-templates select="term[1]">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        </xsl:apply-templates>
      </lhs>  
      <rhs>
        <xsl:apply-templates select="term[2]">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        </xsl:apply-templates>
      </rhs>
    </rule>
  </xsl:template>

  <xsl:template name="ruleset">
    <xsl:param name="rules"/>
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="i" select="1"/>
    <xsl:choose>
      <xsl:when test="$i &lt;= count($rules/rule)">
        <xsl:apply-templates select="$rules/rule[$i]">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        </xsl:apply-templates>
      </xsl:when>
    </xsl:choose>
    <xsl:choose>
      <xsl:when test="$i &lt; count($rules/rule)">
        <xsl:call-template name="ruleset">
          <xsl:with-param name="rules" select="$rules"/>
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          <xsl:with-param name="i" select="$i + 1"/>
        </xsl:call-template>
      </xsl:when>
      <!--  No more rules left -->
      <xsl:otherwise><xsl:text/></xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template mode="nosharp" match="rule">
    <rule>
      <lhs>
        <xsl:apply-templates mode="nosharp" select="term[1]"/>
      </lhs>  
      <rhs>
        <xsl:apply-templates mode="nosharp" select="term[2]"/>
      </rhs>
    </rule>
  </xsl:template>

  <xsl:template name="ruleset-nosharp">
    <xsl:param name="rules"/>
    <xsl:param name="i" select="1"/>
    <xsl:choose>
      <xsl:when test="$i &lt;= count($rules/rule)">
        <xsl:apply-templates mode="nosharp" select="$rules/rule[$i]"/>
      </xsl:when>
    </xsl:choose>
    <xsl:choose>
      <xsl:when test="$i &lt; count($rules/rule)">
        <xsl:call-template name="ruleset-nosharp">
          <xsl:with-param name="rules" select="$rules"/>
          <xsl:with-param name="i" select="$i + 1"/>
        </xsl:call-template>
      </xsl:when>
      <!--  No more rules left -->
      <xsl:otherwise><xsl:text/></xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <!-- A convenience template which just wraps <trs> around a ruleset -->
  <xsl:template match="trs">
    <xsl:param name="tuple-symbols"/>
      <rules>
        <xsl:call-template name="ruleset">
          <xsl:with-param name="rules" select="."/>
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        </xsl:call-template>
      </rules>
  </xsl:template>
  
  <xsl:template mode="nosharp" match="trs">
      <rules>
        <xsl:call-template name="ruleset-nosharp">
          <xsl:with-param name="rules" select="."/>
        </xsl:call-template>
      </rules>
  </xsl:template>

  <!-- *************************************************************************************
       ***                            Auxiliary functions                                ***
       *************************************************************************************
-->

  <!-- Transformation of natural numbers into CetaXML -->

  <xsl:template match="integer">
    <xsl:value-of select="@value"/>
  </xsl:template>

</xsl:transform>
