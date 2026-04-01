<?xml version="1.0" encoding="iso-8859-1"?>

<!-- Transforms XML proofs from AProVE into the Haskell format used by CeTA. -->

<!-- author: ulrichsg -->

<xsl:transform xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
               xmlns:exslt="http://exslt.org/common"
               exclude-result-prefixes="exslt"             
               version="2.0">

  <xsl:output method="text"/>
  
  
  <!-- Starting point -->
  
  <xsl:template match="/">
    <xsl:apply-templates mode="trs" select="/proof-obligation/proposition/proof"/>
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
    <xsl:variable name="pairs">
      <xsl:call-template name="ruleset">
        <xsl:with-param name="rules" select="$origPairs"/>
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:variable name="proof">
      <xsl:apply-templates select="../../proof-obligation/proposition/proof">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
    </xsl:variable>
    
    <xsl:value-of select="concat('DPTrans [', $pairs, '] (', $proof, ')')"/>
  </xsl:template>
  
  
  <!-- Non-termination proof -->
  
  <xsl:template mode="trs" match="qtrs-nontermination-proof">
    <xsl:apply-templates/> <!-- call loop -->
  </xsl:template>
  
  <xsl:template match="loop">
    <xsl:variable name="terms">
      <xsl:call-template name="loop2Terms">
        <xsl:with-param name="parent" select="."/>
        <xsl:with-param name="stop" select="count(step)"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:variable name="context">
      <xsl:apply-templates select="context"/>
    </xsl:variable>
    <xsl:variable name="substitution">
      <xsl:apply-templates select="substitution"/>
    </xsl:variable>
    
    <xsl:value-of select="concat('Loop ([', $terms, '], (', $context, ', ', $substitution, '))')"/>
  </xsl:template>
  
  
  <!-- Extracts a list of terms from a loop.
       Params: $parent - the loop element; $start - index of the first
       term to be included in the output; $stop - ditto for the last term -->
  <xsl:template name="loop2Terms">
    <xsl:param name="parent"/>
    <xsl:param name="start" select="1"/>
    <xsl:param name="stop" select="count($parent/step)"/>
    <xsl:variable name="currentTerm">
      <xsl:choose>
        <xsl:when test="$start &gt; $stop">
          <xsl:text/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:apply-templates mode="nosharp" select="$parent/step[$start]/term[1]"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="rest">
      <xsl:choose>
        <xsl:when test="$start &lt; $stop">
          <xsl:variable name="remainingTerms">
            <xsl:call-template name="loop2Terms">
              <xsl:with-param name="parent" select="$parent"/>
              <xsl:with-param name="start" select="$start + 1"/>
              <xsl:with-param name="stop" select="$stop"/>
            </xsl:call-template>
          </xsl:variable>
          <xsl:value-of select="concat(', ', $remainingTerms)"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    
    <xsl:value-of select="concat($currentTerm, $rest)"/>
  </xsl:template>
  
  
  <!-- Converts a list of <term> elements that are found below a common parent.
       Params: $parent - parent element of the terms; $start - index of the first
       term to be included in the output; $stop - ditto for the last term -->
  <xsl:template name="termList">
    <xsl:param name="parent"/>
    <xsl:param name="start" select="1"/>
    <xsl:param name="stop" select="count($parent/term)"/>
    <xsl:variable name="currentTerm">
      <xsl:choose>
        <xsl:when test="$start &gt; $stop">
          <xsl:text/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:apply-templates mode="nosharp" select="$parent/term[$start]"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="rest">
      <xsl:choose>
        <xsl:when test="$start &lt; $stop">
          <xsl:variable name="remainingTerms">
            <xsl:call-template name="termList">
              <xsl:with-param name="parent" select="$parent"/>
              <xsl:with-param name="start" select="$start + 1"/>
              <xsl:with-param name="stop" select="$stop"/>
            </xsl:call-template>
          </xsl:variable>
          <xsl:value-of select="concat(', ', $remainingTerms)"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    
    <xsl:value-of select="concat($currentTerm, $rest)"/>
  </xsl:template>
  
  <!-- context = Hole | More fsym term* subcontext term* -->
  <xsl:template match="context">
    <xsl:choose>
      <xsl:when test="count(symbol) = 0">
        <xsl:text>Hole</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:variable name="symbol">
          <xsl:apply-templates mode="nosharp" select="symbol"/>
        </xsl:variable>
        <xsl:variable name="subcontext">
          <xsl:apply-templates select="context"/>
        </xsl:variable>
        <xsl:variable name="numLeftTerms">
          <xsl:call-template name="countLeftTerms"/>
        </xsl:variable>
        <xsl:variable name="leftTerms">
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
        </xsl:variable>
        <xsl:variable name="rightTerms">
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
        </xsl:variable>
        
        <xsl:value-of select="concat('(More ', $symbol, ' [', $leftTerms, '] ', $subcontext, ' [', $rightTerms, '])')"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <!-- Determines the number of <term> children in the current <context> element that come before
       the sub-<context>.       
       Apparently, there is no easier way in XSLT to compute this. -->
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
    <xsl:choose>
      <xsl:when test="count(substitute) = 0">
        <xsl:text>[]</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:variable name="substitutes">
          <xsl:call-template name="substitutes">
            <xsl:with-param name="parent" select="."/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:value-of select="concat('[', $substitutes, ']')"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template name="substitutes">
    <xsl:param name="parent"/>
    <xsl:param name="i" select="1"/>
    <xsl:variable name="currentSubst">
      <xsl:variable name="var">
        <xsl:apply-templates mode="nosharp" select="$parent/substitute[$i]/variable"/>
      </xsl:variable>
      <xsl:variable name="term">
        <xsl:apply-templates mode="nosharp" select="$parent/substitute[$i]/term"/>
      </xsl:variable>
      
      <xsl:value-of select="concat('(', $var, ', ', $term, ')')"/>
    </xsl:variable>
    <xsl:variable name="rest">
      <xsl:choose>
        <xsl:when test="$i &lt; count($parent/substitute)">
          <xsl:variable name="remainingSubsts">
            <xsl:call-template name="substitutes">
              <xsl:with-param name="parent" select="$parent"/>
              <xsl:with-param name="i" select="$i + 1"/>
            </xsl:call-template>
          </xsl:variable>
          <xsl:value-of select="concat(', ', $remainingSubsts)"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    
    <xsl:value-of select="concat($currentSubst, $rest)"/>
  </xsl:template>
  
  
  <!-- P-is-empty proof -->
  
  <xsl:template match="p-is-empty-proof">
    <xsl:param name="tuple-symbols"/>
    <xsl:text>PisEmpty</xsl:text>
  </xsl:template>
  
  
  <!-- Dependency graph proof -->
  
  <xsl:template match="qdp-dependency-graph-proof">
    <xsl:param name="tuple-symbols"/>
    <xsl:variable name="components">
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
    </xsl:variable>
    
    <xsl:value-of select="concat('(DepGraphProc [', $components, '])')"/>
  </xsl:template>
  
  <xsl:template name="scc">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="sccProposition"/>
    <xsl:variable name="proof">
      <xsl:choose>
        <xsl:when test="count($sccProposition/proof/non-scc) = 0">
          <xsl:variable name="actualProof">
            <xsl:apply-templates select="$sccProposition/proof">
              <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            </xsl:apply-templates>
          </xsl:variable>
          
          <xsl:value-of select="concat('Just (', $actualProof, ')')"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>Nothing</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="rules">
      <xsl:variable name="pairs">
        <xsl:for-each select="$sccProposition/basic-obligation/qdp-termination-obligation/qdp/dps/rule">
          <xsl:copy-of select="."/>
        </xsl:for-each>
      </xsl:variable>
      <xsl:variable name="ruleset">
        <xsl:call-template name="ruleset">
          <xsl:with-param name="rules" select="exslt:node-set($pairs)"/>
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        </xsl:call-template>
      </xsl:variable>
      
      <xsl:value-of select="concat('[', $ruleset, ']')"/>
    </xsl:variable>
    
    <xsl:value-of select="concat('(', $proof, ', ', $rules, ')')"/>
  </xsl:template>
  
  <xsl:template name="sccList">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="proofTag"/>
    <xsl:param name="i" select="count($proofTag/../../proof-obligation/conjunction/proof-obligation)"/>
    <xsl:variable name="num" select="count($proofTag/../../proof-obligation/conjunction/proof-obligation)"/>
    <xsl:variable name="currentScc">
      <xsl:call-template name="scc">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        <xsl:with-param name="sccProposition" select="$proofTag/../../proof-obligation/conjunction/proof-obligation[$i]/proposition"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:variable name="rest">
      <xsl:choose>
        <xsl:when test="$i &gt; 1">
          <xsl:variable name="remainingSccs">
            <xsl:call-template name="sccList">
              <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
              <xsl:with-param name="proofTag" select="$proofTag"/>
              <xsl:with-param name="i" select="$i - 1"/>
            </xsl:call-template>
          </xsl:variable>
          
          <xsl:value-of select="concat(', ', $remainingSccs)"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    
    <xsl:value-of select="concat($currentScc, $rest)"/>
  </xsl:template>
  
  
  <!-- Reduction pair proof -->
  
  <xsl:template match="qdp-reduction-pair-proof">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="signature"/>
    <xsl:variable name="order">
      <xsl:apply-templates select="order">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        <xsl:with-param name="signature" select="$signature"/>
      </xsl:apply-templates>
    </xsl:variable>
    <xsl:variable name="remainingPairs">
      <xsl:apply-templates select="trs[3]">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
    </xsl:variable>
    <xsl:variable name="restProof">
      <xsl:apply-templates select="../../proof-obligation/proposition/proof">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
    </xsl:variable>
    
    <xsl:value-of select="concat('(RedPairProc (', $order, ') ', $remainingPairs, ' ', $restProof, ')')"/>
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
    <xsl:variable name="mappings">
      <xsl:call-template name="polo-mappings">
        <xsl:with-param name="order" select="."/>
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:call-template>
    </xsl:variable>
    
    <xsl:value-of select="concat('Polo [', $mappings, ']')"/>
  </xsl:template>
  
  <xsl:template name="polo-mappings">
    <xsl:param name="order"/>
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="i" select="1"/>
    <xsl:variable name="currentMapping">
      <xsl:apply-templates select="$order/polo-interpretation[$i]">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
    </xsl:variable>
    <xsl:variable name="rest">
      <xsl:choose>
        <xsl:when test="$i &lt; count($order/polo-interpretation)">
          <xsl:variable name="remainingMappings">
            <xsl:call-template name="polo-mappings">
              <xsl:with-param name="order" select="$order"/>
              <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
              <xsl:with-param name="i" select="$i + 1"/>
            </xsl:call-template>
          </xsl:variable>
          <xsl:value-of select="concat(', ', $remainingMappings)"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    
    <xsl:value-of select="concat($currentMapping, $rest)"/>
  </xsl:template>
  
  <xsl:template match="polo-interpretation">
    <xsl:param name="tuple-symbols"/>
    <xsl:variable name="fsym">
      <xsl:apply-templates select="symbol">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
    </xsl:variable>
    <xsl:variable name="polynomial">
      <xsl:apply-templates select="polynomial"/>
    </xsl:variable>
    
    <xsl:value-of select="concat('(', $fsym, ', ', $polynomial, ')')"/>
  </xsl:template>
  
  <xsl:template match="polynomial">
    <xsl:variable name="constant">
      <xsl:choose>
        <xsl:when test="count(monomial[count(polo-factor) = 0]) &lt; 1">
          <xsl:text>Zero_nat</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:apply-templates select="monomial[count(polo-factor) = 0]/integer"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="coeffs">
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
    </xsl:variable>
    
    <xsl:value-of select="concat('(', $constant, ', [', $coeffs, '])')"/>
  </xsl:template>
  
  <xsl:template name="monomial">
    <xsl:param name="polynomial"/>
    <xsl:param name="varIndex"/>
    <xsl:choose>
      <xsl:when test="count($polynomial//variable[@name = concat('x_', $varIndex)]) = 0">
        <xsl:text>Zero_nat</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates select="$polynomial/monomial[count(polo-factor/variable[@name = concat('x_', $varIndex)]) &gt; 0]/integer"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template name="polo-coeffs">
    <xsl:param name="polynomial"/>
    <xsl:param name="i" select="1"/>
    <xsl:variable name="currentCoeff">
      <xsl:call-template name="monomial">
        <xsl:with-param name="polynomial" select="$polynomial"/>
        <xsl:with-param name="varIndex" select="$i"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:variable name="rest">
      <xsl:choose>
        <xsl:when test="$i &lt; $polynomial/../symbol/@arity">
          <xsl:variable name="remainingCoeffs">
            <xsl:call-template name="polo-coeffs">
              <xsl:with-param name="polynomial" select="$polynomial"/>
              <xsl:with-param name="i" select="$i + 1"/>
            </xsl:call-template>
          </xsl:variable>
          <xsl:value-of select="concat(', ', $remainingCoeffs)"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    
    <xsl:value-of select="concat($currentCoeff, $rest)"/>
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
        <xsl:value-of select="concat('(Plain &quot;', @name, '&quot;)')"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:variable name="originalName">
          <xsl:value-of select="exslt:node-set($tuple-symbols)/defined-to-tuple/entry[count(tupled/symbol[@name = $na and @arity = $ar]) > 0]/orig/symbol/@name"/>
        </xsl:variable>
        <xsl:value-of select="concat('(Sharp &quot;', $originalName, '&quot;)')"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template match="variable">
    <xsl:param name="tuple-symbols"/>
    <xsl:value-of select="concat('Var &quot;', @name, '&quot;')"/>
  </xsl:template>
  
  <xsl:template match="term">
    <xsl:param name="tuple-symbols"/>
    <xsl:apply-templates>
      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
    </xsl:apply-templates>
  </xsl:template>
  
  <xsl:template match="fun-app">
    <xsl:param name="tuple-symbols"/>
    <xsl:variable name="symbol">
      <xsl:apply-templates select="symbol">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
    </xsl:variable>
    <xsl:variable name="arg-list">
      <xsl:call-template name="arg-list">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:call-template>
    </xsl:variable> 
    <xsl:value-of select="concat('Fun ', $symbol, ' [', $arg-list, ']')"/>
  </xsl:template>
  
  <xsl:template name="arg-list">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="i" select="1"/>
    <xsl:variable name="term">
      <xsl:apply-templates select="term[$i]">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
    </xsl:variable>
    <xsl:variable name="rest">
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
        <xsl:otherwise><xsl:text/></xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    
    <xsl:value-of select="concat($term, $rest)"/>
  </xsl:template>
  
  <!-- A duplicated version of term and its dependencies for scenarios
       where tuple-symbols is not present (such as non-termination
       proofs, which operate on TRSs rather than QDPs) -->
  
  <xsl:template mode="nosharp" match="symbol">
    <xsl:value-of select="concat('&quot;', @name, '&quot;')"/>
  </xsl:template>
  
  <xsl:template mode="nosharp" match="term">
    <xsl:apply-templates mode="nosharp"/>
  </xsl:template>
  
  <xsl:template mode="nosharp" match="variable">
    <xsl:value-of select="concat('Var &quot;', @name, '&quot;')"/>
  </xsl:template>
  
  <xsl:template mode="nosharp" match="fun-app">
    <xsl:variable name="symbol">
      <xsl:apply-templates mode="nosharp" select="symbol"/>
    </xsl:variable>
    <xsl:variable name="arg-list">
      <xsl:call-template name="arg-list-nosharp"/>
    </xsl:variable> 
    <xsl:value-of select="concat('Fun ', $symbol, ' [', $arg-list, ']')"/>
  </xsl:template>
  
  <xsl:template name="arg-list-nosharp">
    <xsl:param name="i" select="1"/>
    <xsl:variable name="term">
      <xsl:apply-templates mode="nosharp" select="term[$i]"/>
    </xsl:variable>
    <xsl:variable name="rest">
      <xsl:choose>
        <xsl:when test="$i &lt; count(term)">
          <xsl:variable name="rest-terms">
            <xsl:call-template name="arg-list-nosharp">
              <xsl:with-param name="i" select="$i + 1"/>
            </xsl:call-template>
          </xsl:variable>
          <xsl:value-of select="concat(', ', $rest-terms)"/>
        </xsl:when>
        <xsl:otherwise><xsl:text/></xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    
    <xsl:value-of select="concat($term, $rest)"/>
  </xsl:template>
  
  <!-- Rules -->
  
  <xsl:template match="rule">
    <xsl:param name="tuple-symbols"/>
    <xsl:variable name="left">
      <xsl:apply-templates select="term[1]">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
    </xsl:variable>
    <xsl:variable name="right">
      <xsl:apply-templates select="term[2]">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
    </xsl:variable>
    
    <xsl:value-of select="concat('(', $left, ', ', $right, ')')"/>
  </xsl:template>
  
  <xsl:template name="ruleset">
    <xsl:param name="rules"/>
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="i" select="1"/>
    <xsl:variable name="currentRule">
      <xsl:apply-templates select="$rules/rule[$i]">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
    </xsl:variable>
    <xsl:variable name="rest">
      <xsl:choose>
        <xsl:when test="$i &lt; count($rules/rule)">
          <xsl:variable name="remainingRules">
            <xsl:call-template name="ruleset">
              <xsl:with-param name="rules" select="$rules"/>
              <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
              <xsl:with-param name="i" select="$i + 1"/>
            </xsl:call-template>
          </xsl:variable>
          <xsl:value-of select="concat(', ', $remainingRules)"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    
    <xsl:value-of select="concat($currentRule, $rest)"/>
  </xsl:template>
  
  <!-- A convenience template which just wraps [] around a ruleset -->  
  <xsl:template match="trs">
    <xsl:param name="tuple-symbols"/>
    <xsl:variable name="rules">
      <xsl:call-template name="ruleset">
        <xsl:with-param name="rules" select="."/>
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:call-template>
    </xsl:variable>
    
    <xsl:value-of select="concat('[', $rules, ']')"/>
  </xsl:template>
  
  
  <!-- *************************************************************************************
       ***                            Auxiliary functions                                ***
       ************************************************************************************* -->
  
  <!-- Transformation of natural numbers into Haskell -->
  
  <xsl:template match="integer">
    <xsl:call-template name="make-integer">
      <xsl:with-param name="n" select="number(@value)"/>
    </xsl:call-template>
  </xsl:template>
  
  <xsl:template name="make-integer">
    <xsl:param name="n"/>
    <xsl:choose>
      <xsl:when test="$n &lt;= 0">Zero_nat</xsl:when>
      <xsl:otherwise>
        <xsl:variable name="recVal">
          <xsl:call-template name="make-integer">
            <xsl:with-param name="n" select="$n - 1"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:value-of select="concat('(Suc ', $recVal, ')')"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
</xsl:transform>