<?xml version="1.0" encoding="utf-8"?>

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
                version="1.0">

  <xsl:output method="html"/>

  <xsl:template match="proof-obligation">
    <xsl:value-of select="@identifier" />: <xsl:apply-templates />
  </xsl:template>

  <xsl:template match="p-is-empty-proof">
    There are no pairs in this DP-problem, hence, the DP-problem is trivially finite.
  </xsl:template>

  <xsl:template match="qtrs-locally-confluent-overlay-proof">
    <p>The system is a locally confluent overlay systems. Hence, we can switch to innermost termination.</p>
  </xsl:template>
  

  <xsl:template match="qtrs-dependency-pairs-proof">
    <p>We use the Dependency Pair criterion.</p>
    <p>We map the defined symbols to tuple symbols as follows.</p>
    <table>
      <xsl:attribute name="align">center</xsl:attribute>
      <xsl:for-each select="defined-to-tuple-entry">
        <TR>
          <TD><xsl:attribute name="align">right</xsl:attribute><xsl:apply-templates select="symbol[1]"/></TD>
          <TD><xsl:attribute name="align">center</xsl:attribute> &#8658;  </TD>
          <TD><xsl:attribute name="align">left</xsl:attribute><xsl:apply-templates select="symbol[2]"/></TD>
        </TR>           
      </xsl:for-each>
    </table>         
    <p>Then we obtain the following Dependency Pairs for the rules.</p>
    <table>
      <xsl:attribute name="align">center</xsl:attribute>
      <TR><TH>Rule</TH><TH>Position</TH><TH>Dependency Pair</TH></TR>
      <xsl:for-each select="rule-to-dps-entry">
        <xsl:for-each select="position-to-dp">
          <TR>
            <TD>
              <xsl:if test="position() = 1">
                <xsl:attribute name="align">right</xsl:attribute><xsl:apply-templates select="../rule"/>
              </xsl:if>
            </TD>  
            <TD><xsl:attribute name="align">center</xsl:attribute><xsl:apply-templates select="position"/></TD>
            <TD><xsl:attribute name="align">left</xsl:attribute><xsl:apply-templates select="rule"/></TD>
          </TR>           
        </xsl:for-each>
      </xsl:for-each>
    </table>             
  </xsl:template>

  <xsl:template match="qdp-usable-rules-proof">
    <p>As we are in the innermost case, we can replace the TRS by the usable rules.</p>
  </xsl:template>
  
  <xsl:template match="qdp-dependency-graph-proof">
    <p>We decompose the dependency graph into the following SCCs.</p>
    <UL>
      <xsl:for-each select="graph-scc">
        <LI> 
            {<xsl:for-each select="identifier">
                <xsl:if test="position() != 1">, </xsl:if>
                <xsl:apply-templates select="."/>
            </xsl:for-each>}
        </LI>
      </xsl:for-each>
    </UL>
  </xsl:template>

  <xsl:template match="identifier">
    <xsl:value-of select="@name"/>
  </xsl:template>


  <xsl:template match="qdp-edge-deletion-proof">
    <p>We delete the following edges between pairs s &#8594; t and u &#8594; v by the following reasons.</p>
    <UL>
      <xsl:for-each select="edge-deletion">
        <LI> 
        <xsl:apply-templates select="identifier[1]"/> 
        &#8594;
        <xsl:apply-templates select="identifier[2]"/>: 
        <xsl:apply-templates select="edge-del-reason"/>
        </LI>
      </xsl:for-each>
    </UL>
  </xsl:template>

  <xsl:template match="different-roots">
    The root symbol <xsl:apply-templates select="symbol[1]"/> of t is a constructor and is different from the root 
    symbol <xsl:apply-templates select="symbol[2]"/> of u.
  </xsl:template>

  <xsl:template match="capt-not-unifies-u">
    The term cap(t) = <xsl:apply-templates select="term[1]"/> does not unify
    with the term u = <xsl:apply-templates select="term[2]"/>.
  </xsl:template>

  <xsl:template match="capu-not-unifies-t">
    The term cap<sup>U(t)<sup>-1</sup></sup>(u) = <xsl:apply-templates select="term[1]"/> does not unify
    with the term t = <xsl:apply-templates select="term[2]"/>.
  </xsl:template>

  <xsl:template match="capu-t-mgu-not-normal">
    The mgu of cap<sup>U(t)<sup>-1</sup></sup>(u) = <xsl:apply-templates select="term[1]"/> and 
    t = <xsl:apply-templates select="term[2]"/> is &#963; = <xsl:apply-templates select="substitution"/>.
    Then 
    <xsl:choose>
      <xsl:when test="boolean/@value = 'true'">s</xsl:when>
      <xsl:otherwise>u</xsl:otherwise>
    </xsl:choose>&#963; 
    = <xsl:apply-templates select="term[3]"/> is not in normal form w.r.t. Q.    
  </xsl:template>

  <xsl:template match="capt-u-mgu-not-normal">
    The mgu of cap(t) = <xsl:apply-templates select="term[1]"/> and 
    u = <xsl:apply-templates select="term[2]"/> is &#963; = <xsl:apply-templates select="substitution"/>.
    Then 
    <xsl:choose>
      <xsl:when test="boolean/@value = 'true'">s</xsl:when>
      <xsl:otherwise>u</xsl:otherwise>
    </xsl:choose>&#963; 
    = <xsl:apply-templates select="term[3]"/> is not in normal form w.r.t. Q.    
  </xsl:template>

  <xsl:template match="qdp-reduction-pair-proof">
    <p>We use the reduction pair processor with the following order.</p>
    <xsl:apply-templates select="order"/>      
    <xsl:choose>
      <xsl:when test="count(trs[1]/rule) = 0">
        <p>There are no usable rules w.r.t. this order</p>
      </xsl:when>
      <xsl:otherwise>
    <p>With this order we obtained the following set of usable rules.</p>
    <xsl:apply-templates select="trs[1]"/>
      </xsl:otherwise>      
    </xsl:choose>
    <xsl:choose>
      <xsl:when test="count(trs[3]/rule) = 0">
        <p>All pairs have been strictly oriented.</p>
        <xsl:apply-templates select="trs[2]"/>
      </xsl:when>
      <xsl:otherwise>
        <p>The following pairs have been strictly oriented.</p>
        <xsl:apply-templates select="trs[2]"/>
        <p>The remaining pairs are at least weakly decreasing.</p>
        <xsl:apply-templates select="trs[3]"/>        
      </xsl:otherwise>
    </xsl:choose>
    <p>As a result we tranformed the input obligation DP-problem 
    <xsl:value-of select="../../../@identifier"/> into the
    new DP-problem <xsl:value-of select="../../proof-obligation/@identifier"/>.</p>
    <!--    <table border="1"><tr><td><xsl:apply-templates select="id(../../proof-obligation/@identifier)/proposition/basic-obligation"/></td></tr></table> -->
  </xsl:template>

  <xsl:template match="polo-factor">
    <xsl:apply-templates select="variable"/>
    <xsl:if test="integer/@value != 1">
      <sup><xsl:apply-templates select="integer"/></sup>
    </xsl:if>
  </xsl:template>


  <xsl:template match="monomial">
    <xsl:choose>
      <xsl:when test="count(polo-factor) = 0">
        <xsl:apply-templates select="integer"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:if test="integer/@value != 1"><xsl:apply-templates select="integer"/></xsl:if>
        <xsl:for-each select="polo-factor">
          <xsl:apply-templates select="."/>
        </xsl:for-each>
      </xsl:otherwise>
    </xsl:choose>
    
  </xsl:template>

  <xsl:template match="polynomial">
    <span style="color:grey">    
    <xsl:choose>
      <xsl:when test="count(monomial) = 0">
        0
      </xsl:when>
      <xsl:otherwise>
        <xsl:for-each select="monomial">
          <xsl:if test="position() != 1"> + </xsl:if>
          <xsl:apply-templates select="."/>
        </xsl:for-each>
      </xsl:otherwise>
    </xsl:choose>
    </span>
  </xsl:template>

  <xsl:template match="polynomial-order">
    The polynomial order has the following interpretation.
    <TABLE><xsl:attribute name="align">center</xsl:attribute>      
    <xsl:for-each select="polo-interpretation">
      <TR><TD><xsl:attribute name="align">right</xsl:attribute>Pol(<xsl:apply-templates select="symbol"/>)</TD>
          <TD><xsl:attribute name="align">center</xsl:attribute>=</TD>
          <TD><xsl:attribute name="align">left</xsl:attribute><xsl:apply-templates select="polynomial"/></TD>
      </TR>
    </xsl:for-each>
    </TABLE>
  </xsl:template>

  <xsl:template match="proposition">
    We analyze the following proposition.    
    <table border="1"><tr><td>
      <xsl:apply-templates select="basic-obligation"/>
    </td></tr></table>
    <xsl:choose>
      <xsl:when test="count(proof) = 0">
        <p>Unfortunately we got stuck at this point.</p>
      </xsl:when>
      <xsl:otherwise>
        <p>We use a(n) <xsl:value-of select="implication/@value"/> processor to transform this proposition
      into the new proof obligation <xsl:value-of select="proof-obligation/@identifier"/>. Here is the detailed
        proof.</p>
        <table border="1"><tr><td><xsl:apply-templates select="proof" /></td></tr></table>
        <ul><li><xsl:apply-templates select="proof-obligation" /></li></ul>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>



  <xsl:template match="conjunction">
    <xsl:choose>
    <xsl:when test="count(proof-obligation) = 0">
      TRUE
    </xsl:when>
    <xsl:otherwise>      
      We consider the conjunction 
      <xsl:for-each select="proof-obligation">
        <xsl:if test="position() != 1"> &#8743; </xsl:if>
        <xsl:value-of select="@identifier"/>
      </xsl:for-each>
      <ul>
      <xsl:for-each select="proof-obligation">
        <li>
        <xsl:apply-templates select="." />
        </li>
      </xsl:for-each>
      </ul>
    </xsl:otherwise>
    </xsl:choose>
  </xsl:template>




  <xsl:template match="qtrs-termination-obligation">
    Termination of the following Q-restricted rewrite system.
    <xsl:apply-templates select="qtrs" />
  </xsl:template>

  <xsl:template match="qdp-termination-obligation">
    Finiteness of the following QDP-problem.
    <xsl:apply-templates select="qdp" />
  </xsl:template>


  <xsl:template match="qtrs">
    <p>The Q-restricted rewrite system contains the following rules:</p>
    <xsl:apply-templates select="trs"/>      
    <xsl:choose>
      <xsl:when test="count(qtermset/term) = 0">
        <p>The set Q is empty, i.e. we consider full termination.</p>
      </xsl:when>
      <xsl:otherwise>
        <p>Here, the set Q consists of the following terms:</p>
        <xsl:apply-templates select="qtermset"/>        
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="dps">
    <xsl:call-template name="trsWithNumbers"/>
    <xsl:call-template name="edges"/>
  </xsl:template>

  <xsl:template match="qdp">
    <p>The QDP-problem contains the following pairs:</p>
    <xsl:apply-templates select="dps"/>    
    <p>The rewrite system contains the following rules:</p>
    <xsl:apply-templates select="trs"/>    
    <xsl:choose>
      <xsl:when test="count(qtermset/term) = 0">
        <p>The set Q is empty, i.e. we consider full termination.</p>
      </xsl:when>
      <xsl:otherwise>
        <p>Here, the set Q consists of the following terms:</p>
        <xsl:apply-templates select="qtermset"/>        
      </xsl:otherwise>
    </xsl:choose>
    <p>We have to consider all
    <xsl:if test="minimality-flag/boolean/@value = 'true'">minimal</xsl:if>
    chains.
    </p>
  </xsl:template>


  <!-- variables always in red -->
  <xsl:template match="variable">
    <span style="color:red"><xsl:value-of select="@name" /></span>
  </xsl:template>


  <!-- symbols always in blue -->
  <xsl:template match="symbol">
    <span style="color:blue"><xsl:value-of select="@name" />
    <!--
    <sub><span style="color:purple"><xsl:value-of select="@arity" /></span></sub>
    -->
    </span>
  </xsl:template>


  <xsl:template match="fun-app">
    <xsl:apply-templates select="symbol"/>
    <xsl:for-each select="term">
      <xsl:choose>
        <xsl:when test="position() = 1">(</xsl:when>
        <xsl:otherwise>, </xsl:otherwise>
      </xsl:choose>
      <xsl:apply-templates select="." />
      <xsl:if test="last() = position()">)</xsl:if>
    </xsl:for-each>
  </xsl:template>



  <xsl:template match="rule">
    <xsl:apply-templates select="term[1]"/> &#8594; 
    <xsl:apply-templates select="term[2]"/> 
  </xsl:template>


  <xsl:template match="substitution">
    <xsl:choose>
    <xsl:when test="count(substitute) = 0">
       [ ]
    </xsl:when>
    <xsl:otherwise>    
      [<xsl:for-each select="substitute">
        <xsl:apply-templates select="variable"/>/<xsl:apply-templates select="term"/>
        <xsl:if test="last() != position()">, </xsl:if>
      </xsl:for-each>]
    </xsl:otherwise>
    </xsl:choose>
  </xsl:template>


  <xsl:template name="trs" match="trs">
    <xsl:choose>
    <xsl:when test="count(rule) = 0">
      <p>none</p>
    </xsl:when>
    <xsl:otherwise>
        <table>
          <xsl:attribute name="align">center</xsl:attribute>
          <xsl:for-each select="rule">
          <TR>
            <TD><xsl:attribute name="align">right</xsl:attribute><xsl:apply-templates select="term[1]"/></TD>
            <TD><xsl:attribute name="align">center</xsl:attribute> &#8594; </TD>
            <TD><xsl:attribute name="align">left</xsl:attribute><xsl:apply-templates select="term[2]"/></TD>
          </TR>           
          </xsl:for-each>
        </table>          
    </xsl:otherwise>
    </xsl:choose>
  </xsl:template>


  <xsl:template name="trsWithNumbers">
    <xsl:choose>
    <xsl:when test="count(rule) = 0">
      <p>none</p>
    </xsl:when>
    <xsl:otherwise>
        <table>
          <xsl:attribute name="align">center</xsl:attribute>
          <xsl:for-each select="rule">
          <TR>
            <TD><xsl:attribute name="align">center</xsl:attribute><xsl:apply-templates select="@identifier"/>:</TD> 
            <TD><xsl:attribute name="align">right</xsl:attribute><xsl:apply-templates select="term[1]"/></TD>
            <TD><xsl:attribute name="align">center</xsl:attribute> &#8594; </TD>
            <TD><xsl:attribute name="align">left</xsl:attribute><xsl:apply-templates select="term[2]"/></TD>
          </TR>           
          </xsl:for-each>
        </table>          
    </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="edges">
    <xsl:choose>
    <xsl:when test="count(dp-edge) = 0">
      <p>There are no edges in the DP-graph.</p>
    </xsl:when>
    <xsl:otherwise>
      <p>We have the following edges in the DP-graph:</p>
      <p>
        <xsl:for-each select="dp-edge">
          <xsl:if test="position() != 1">, </xsl:if>
          <xsl:apply-templates select="@fr"/>  &#8594; 
          <xsl:apply-templates select="@to"/>
        </xsl:for-each>
      </p>
    </xsl:otherwise>
    </xsl:choose>
  </xsl:template>



  <xsl:template match="qtermset">
    <xsl:choose>
    <xsl:when test="count(term) = 0">
      <p>There are no terms in this set.</p>
    </xsl:when>
    <xsl:otherwise>
        <table>
          <xsl:attribute name="align">center</xsl:attribute>
          <xsl:for-each select="term">
          <TR>
            <TD><xsl:attribute name="align">center</xsl:attribute><xsl:apply-templates select="."/></TD>
          </TR>           
          </xsl:for-each>
        </table>          
    </xsl:otherwise>
    </xsl:choose>
  </xsl:template>


  <xsl:template match="position">
    <xsl:choose>
    <xsl:when test="count(integer) = 0">
      <p>&#949;</p>
    </xsl:when>
    <xsl:otherwise>
    <xsl:for-each select="integer">
      <xsl:if test="position() != 1">.</xsl:if>
      <xsl:apply-templates select="."/>
    </xsl:for-each>
    </xsl:otherwise>
    </xsl:choose>
  </xsl:template>


  <xsl:template match="integer"><xsl:value-of select="@value"/></xsl:template>

  <xsl:template match="/">
    <html>
      <head></head>
      <body bgcolor="#DFDFDF">
        <xsl:apply-templates />
      </body>
    </html>
  </xsl:template>

</xsl:stylesheet>
