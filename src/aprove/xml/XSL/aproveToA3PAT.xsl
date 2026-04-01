<?xml version="1.0" encoding="iso-8859-1"?>

<!-- This xsl-file transforms xml-proofs from AProVE into
     the format of the A3Pat project (Cime/Coccinelle)
-->

<!-- author: thiemann -->
<!-- version: 0.2 -->

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
               xmlns:exslt="http://exslt.org/common"
               xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
               exclude-result-prefixes="exslt xsi"             
               version="2.0">

  <xsl:output method="xml" indent="yes" omit-xml-declaration="no" />

  <xsl:variable name="nrDPproof" select="count(//qtrs-dependency-pairs-proof)"/>

  <xsl:variable name="defToTup">
    <xsl:choose>
      <xsl:when test="$nrDPproof = 0">
        <no_DPs/>
      </xsl:when>
      <xsl:when test="$nrDPproof = 1">
        <def_to_tup>
          <xsl:for-each select="//qtrs-dependency-pairs-proof[1]/defined-to-tuple-entry">
            <entry>
              <def><xsl:copy-of select="symbol[1]"/></def>
              <tup><xsl:copy-of select="symbol[2]"/></tup>
            </entry>
          </xsl:for-each>
        </def_to_tup>
      </xsl:when>      
    </xsl:choose>
  </xsl:variable>


<!-- **************************************************************************************** 
     **  starting point of the transformation, here the signature is extracted
     **  as signature of the root node in the proof!
     **************************************************************************************** -->
  <xsl:template match="/proof-obligation">
    <xsl:choose>
      <xsl:when test="$nrDPproof &gt; 1">
        <ERROR>multiple TRS-to-DP proofs detected</ERROR>
      </xsl:when>
      <xsl:otherwise>
        <PROOF>
          <xsl:variable name="signature">
            <xsl:apply-templates mode="sig_extract" select="proposition/basic-obligation/qtrs-termination-obligation/qtrs"/>
          </xsl:variable>
          <xsl:variable name="signature_variables">
            <xsl:apply-templates mode="sig_var_extract" select="proposition/basic-obligation/qtrs-termination-obligation/qtrs"/>
          </xsl:variable>
          <SIGNATURE>
            <SYMBOLLIST>
              <xsl:for-each select="exslt:node-set($signature)/signature/symbol">
                <xsl:apply-templates mode="as_element" select="."/>
              </xsl:for-each>
              <xsl:choose>
                <xsl:when test="$nrDPproof = 1">
                  <xsl:for-each select="exslt:node-set($defToTup)/def_to_tup/entry/tup/symbol">
                    <xsl:apply-templates mode="tupled" select="."/>
                  </xsl:for-each>
                </xsl:when>
              </xsl:choose>
            </SYMBOLLIST>
            <VARLIST>
              <xsl:for-each select="exslt:node-set($signature_variables)/signature/variable">
                <xsl:apply-templates mode="as_element" select="."/>
              </xsl:for-each>
            </VARLIST>
          </SIGNATURE>
          <xsl:apply-templates select="proposition"/>
        </PROOF>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  

<!-- **************************************************************************************** 
     **  General structure of the proof
     **************************************************************************************** -->
  <xsl:template match="proposition">
    <xsl:choose>
      <xsl:when test="count(proof/non-scc) &gt; 0"/>
      <xsl:otherwise>
        <xsl:element name="PROPERTY">
          <xsl:attribute name="prop">
            <xsl:apply-templates mode="getname" select="basic-obligation"/>       
          </xsl:attribute>
          <xsl:attribute name="criterion">
            <xsl:apply-templates mode="getname" select="proof"/>
          </xsl:attribute>
          <SYSTEM>
            <xsl:apply-templates select="basic-obligation"/>
          </SYSTEM>
          <xsl:apply-templates select="proof"/>
          <xsl:apply-templates select="proof-obligation"/>        
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template mode="getname" match="qtrs-termination-obligation">sntrs</xsl:template>
  <xsl:template mode="getname" match="qdp-termination-obligation">sndp</xsl:template>

<!-- **************************************************************************************** 
     **  TRS-to-DPs proof
     **  here is the point where the map from defined to tuple-symbols is generated
     **  this map has to be provided throughout the remaining proof
     **************************************************************************************** -->
  <xsl:template mode="getname" match="qtrs-dependency-pairs-proof">dp</xsl:template>
  <xsl:template match="qtrs-dependency-pairs-proof">
    <CRITERION/>
  </xsl:template>

<!-- **************************************************************************************** 
     **  For P-is-empty-proof just use SCC-decomposition
     **************************************************************************************** -->
  <xsl:template mode="getname" match="p-is-empty-proof">weakgraph</xsl:template>
  <xsl:template match="p-is-empty-proof">
    <CRITERION>
      <DAG approx="simpl">
        <CCLIST/>
      </DAG>
    </CRITERION>
  </xsl:template>



<!-- **************************************************************************************** 
     **  SCC-decomposition
     **  in the children one has to provide one pair of the SCCs for identification
     **  moreover, currently only root-symbols are compared for edge-deletion, here
     **  no information is necessary 
     **************************************************************************************** -->
  <xsl:template mode="getname" match="qdp-dependency-graph-proof">weakgraph</xsl:template>
  <xsl:template match="qdp-dependency-graph-proof">
    <CRITERION>
      <DAG approx="simpl">
        <xsl:variable name="cclist">
          <CCLIST>
            <xsl:apply-templates mode="numberSCCs" select=".">
              <xsl:with-param name="i" select="1"/>
            </xsl:apply-templates>
          </CCLIST>
        </xsl:variable>
        <xsl:copy-of select="$cclist"/>
        <!-- now use cclist to generate edges between cc's -->
        <xsl:apply-templates mode="cc-edges" select="exslt:node-set($cclist)">
          <xsl:with-param name="graph" select="../../basic-obligation/qdp-termination-obligation/qdp/dps"/>
        </xsl:apply-templates>
      </DAG>
    </CRITERION>
  </xsl:template>

  <!-- generate the numbers for SCC-decomposition proof and also produce A3Pat CCLIST -->
  <xsl:template mode="numberSCCs" match="qdp-dependency-graph-proof">
    <xsl:param name="i"/> <!-- i is nr of scc to visit -->
    <xsl:param name="num" select="1"/>
    <xsl:choose>
      <xsl:when test="$i &lt;= count(graph-scc)">
        <xsl:choose>
<!--  test="count(../..//proof-obligation/proposition[count(basic-obligation//rule[@identifier=current()/graph-scc[$i]/identifier/@name]) &gt; 0]/proof/non-scc) = 0"> -->
          <xsl:when test="count(current()/graph-scc[$i]/identifier) = 1 and count(../../basic-obligation/qdp-termination-obligation/qdp/dps/dp-edge[@fr=current()/graph-scc[$i]/identifier[1]/@name and @to=current()/graph-scc[$i]/identifier[1]/@name]) = 0">
            <xsl:element name="NONSCC">
              <xsl:attribute name="num"><xsl:value-of select="$num"/></xsl:attribute>
              <xsl:for-each select="graph-scc[$i]/identifier">
                <xsl:element name="NODE">
                  <xsl:attribute name="ref"><xsl:value-of select="@name"/></xsl:attribute>
                </xsl:element>
              </xsl:for-each>
            </xsl:element>
	  </xsl:when>
          <xsl:otherwise>
            <xsl:element name="SCC">
              <xsl:attribute name="num"><xsl:value-of select="$num"/></xsl:attribute>
              <xsl:for-each select="graph-scc[$i]/identifier">
                <xsl:element name="NODE">
                  <xsl:attribute name="ref"><xsl:value-of select="@name"/></xsl:attribute>
                </xsl:element>
              </xsl:for-each>
            </xsl:element>
	  </xsl:otherwise>
	</xsl:choose>
        <xsl:apply-templates mode="numberSCCs" select=".">
          <xsl:with-param name="i" select="$i + 1"/>
          <xsl:with-param name="num" select="$num + 1"/>
        </xsl:apply-templates>
      </xsl:when>
    </xsl:choose>
  </xsl:template>
    

  <!-- generate edges between components of graph -->
  <xsl:template mode="cc-edges" match="CCLIST">
    <xsl:param name="graph"/> <!-- the dp-graph -->
    <xsl:apply-templates mode="cc-edges2" select=".">
      <xsl:with-param name="i" select="1"/>
      <xsl:with-param name="j" select="1"/>
      <xsl:with-param name="n" select="count(./*)"/>
      <xsl:with-param name="graph" select="$graph"/>          
    </xsl:apply-templates>
  </xsl:template>


  <!-- generate edges between components of graph, walk through all components -->
  <xsl:template mode="cc-edges2" match="CCLIST">
    <xsl:param name="i"/> <!-- i is current component (as start) -->
    <xsl:param name="j"/> <!-- j is current component (as end) -->
    <xsl:param name="n"/> <!-- total number of components -->
    <xsl:param name="graph"/> <!-- the dp-graph -->
    <xsl:choose>
      <xsl:when test="$i &lt;= $n">
        <xsl:choose>
          <xsl:when test="$j &lt;= $n">
            <xsl:choose>
              <!-- if we have different components then check whether there
                   is an edge between them 
                   -->
              <xsl:when test="$i != $j">
                <xsl:apply-templates mode="cc-edges3" select=".">
                  <xsl:with-param name="i" select="$i"/>
                  <xsl:with-param name="j" select="$j"/>
                  <xsl:with-param name="ni" select="1"/>
                  <xsl:with-param name="nj" select="1"/>
                  <xsl:with-param name="numi" select="count(./*[$i]/NODE)"/>
                  <xsl:with-param name="numj" select="count(./*[$j]/NODE)"/>
                  <xsl:with-param name="graph" select="$graph"/>                        
                </xsl:apply-templates>
              </xsl:when>
            </xsl:choose>
            <xsl:apply-templates mode="cc-edges2" select=".">
              <xsl:with-param name="i" select="$i"/>
              <xsl:with-param name="j" select="$j + 1"/>
              <xsl:with-param name="n" select="$n"/>
              <xsl:with-param name="graph" select="$graph"/>          
            </xsl:apply-templates>            
          </xsl:when>                  
          <xsl:otherwise>
            <xsl:apply-templates mode="cc-edges2" select=".">
              <xsl:with-param name="i" select="$i + 1"/>
              <xsl:with-param name="j" select="1"/>
              <xsl:with-param name="n" select="$n"/>
              <xsl:with-param name="graph" select="$graph"/>          
            </xsl:apply-templates>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
    </xsl:choose> 
  </xsl:template>
    
  <!-- check whether cc-i has edge to cc-j -->
  <xsl:template mode="cc-edges3" match="CCLIST">
    <xsl:param name="i"/> <!-- i is current component (as start) -->
    <xsl:param name="j"/> <!-- j is current component (as end) -->
    <xsl:param name="ni"/> <!-- ni is node within component i -->
    <xsl:param name="nj"/> <!-- nj is node within component j -->
    <xsl:param name="numi"/> <!-- nr of nodes within component i -->
    <xsl:param name="numj"/> <!-- nr of nodes within component j -->
    <xsl:param name="graph"/> <!-- the dp-graph -->
    <xsl:variable name="inodes" select="./*[$i]"/>     
    <xsl:choose>
      <xsl:when test="$ni &lt;= $numi">
        <xsl:variable name="jnodes" select="./*[$j]"/>     
        <xsl:choose>
          <xsl:when test="$nj &lt;= $numj">
            <xsl:choose>
              <!-- check for edge between ni and nj -->
              <xsl:when test="count($graph/dp-edge[@fr = $inodes/NODE[$ni]/@ref and @to = $jnodes/NODE[$nj]/@ref]) != 0">
                <xsl:element name="EDGE">
                  <xsl:attribute name="start"><xsl:value-of select="$i"/></xsl:attribute>
                  <xsl:attribute name="end"><xsl:value-of select="$j"/></xsl:attribute>
                </xsl:element>
              </xsl:when>              
              <xsl:otherwise>
                <xsl:apply-templates mode="cc-edges3" select=".">
                  <xsl:with-param name="i" select="$i"/>
                  <xsl:with-param name="j" select="$j"/>
                  <xsl:with-param name="ni" select="$ni"/>
                  <xsl:with-param name="nj" select="$nj + 1"/>
                  <xsl:with-param name="numi" select="$numi"/>
                  <xsl:with-param name="numj" select="$numj"/>
                  <xsl:with-param name="graph" select="$graph"/>                        
                </xsl:apply-templates>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:when>
          <xsl:otherwise>
            <xsl:apply-templates mode="cc-edges3" select=".">
              <xsl:with-param name="i" select="$i"/>
              <xsl:with-param name="j" select="$j"/>
              <xsl:with-param name="ni" select="$ni + 1"/>
              <xsl:with-param name="nj" select="1"/>
              <xsl:with-param name="numi" select="$numi"/>
              <xsl:with-param name="numj" select="$numj"/>
              <xsl:with-param name="graph" select="$graph"/>                        
            </xsl:apply-templates>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
    </xsl:choose>
  </xsl:template>


<!-- **************************************************************************************** 
     **  Rule removal using extended monotone orders
     ** (Currently not supported by A3PAT!)
     **************************************************************************************** -->
  <xsl:template mode="getname" match="qtrs-rule-removal-proof">ordering</xsl:template>
  <xsl:template match="qtrs-rule-removal-proof">
    <CRITERION>
      <xsl:apply-templates select="order"/>
    </CRITERION>
  </xsl:template>


<!-- **************************************************************************************** 
     **  Remove DPs by reduction pair
     **  (no usable rules, no active, so we need just the order)
     **************************************************************************************** -->
  <xsl:template mode="getname" match="qdp-reduction-pair-proof">stronggraph</xsl:template>
  <xsl:template match="qdp-reduction-pair-proof">
    <CRITERION>
      <xsl:apply-templates select="order"/>
      <STRICTPAIRS>
        <DPLIST>
          <xsl:apply-templates mode="dp" select="trs[2]"/>          
        </DPLIST>
      </STRICTPAIRS>
    </CRITERION>
  </xsl:template>


<!-- **************************************************************************************** 
     **  Output a polynomial order for use in combination with DPs 
     **  signature is the signature of the original TRS (root-node in whole proof)
     **************************************************************************************** -->
  <xsl:template match="polynomial-order">
    <ORDERING>
      <xsl:attribute name="type">
        <xsl:choose>
          <xsl:when test="@type = 'arctic'">apoly</xsl:when>
          <xsl:otherwise>poly</xsl:otherwise>
        </xsl:choose>
      </xsl:attribute>
      <xsl:for-each select="polo-interpretation/symbol">        
        <POLYSYMB>
          <xsl:apply-templates select="."/>
          <xsl:apply-templates select="../polynomial"/>
        </POLYSYMB>
      </xsl:for-each>  
    </ORDERING>
  </xsl:template>



<!-- **************************************************************************************** 
     **  Polynomials
     **************************************************************************************** -->

  <xsl:template match="polynomial">
    <xsl:choose>
      <xsl:when test="count(monomial) &lt; 1">
        <POLYNOMIAL>
          <MONOME>
            <COEF>
              <INT>0</INT>
            </COEF>
          </MONOME>
        </POLYNOMIAL>
      </xsl:when>
      <xsl:when test="count(monomial) &gt; 1">
        <POLYNOMIAL>
          <SUMPOLY>
            <xsl:apply-templates/>
          </SUMPOLY>
        </POLYNOMIAL>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template match="monomial">
    <xsl:variable name="this" select="."/>
    <POLYNOMIAL>
      <xsl:choose>
        <xsl:when test="count(polo-factor/max) &gt; 0">
          <PRODPOLY>
            <xsl:for-each select="polo-factor[count(max) &gt; 0]">
              <POLYNOMIAL>
                <MAXPOLY>
                  <xsl:apply-templates select="max/polynomial"/>
                </MAXPOLY>
              </POLYNOMIAL>
            </xsl:for-each>
            <POLYNOMIAL>
              <xsl:call-template name="monomial-no-max">
                <xsl:with-param name="monomial" select="$this"/>
              </xsl:call-template>
            </POLYNOMIAL>
          </PRODPOLY>
        </xsl:when>
        <xsl:otherwise>
          <xsl:call-template name="monomial-no-max">
            <xsl:with-param name="monomial" select="$this"/>
          </xsl:call-template>
        </xsl:otherwise>
      </xsl:choose>
    </POLYNOMIAL>
  </xsl:template>
  
  <!-- Transform the given monomial into a MONOME element, ignoring all polo-factors containing max. -->
  <xsl:template name="monomial-no-max">
    <xsl:param name="monomial"/>
    <MONOME>
      <COEF>
         <xsl:apply-templates mode="with-tag" select="$monomial/*[local-name() != 'polo-factor']"/>
      </COEF>
      <xsl:for-each select="$monomial/polo-factor[count(max) = 0]">
        <xsl:element name="ARG">
          <xsl:attribute name="num">
            <!-- remove prefix x_ of aprove's format and adjust numbering (aprove counts from x_1,..., A3Pat from 0,...) -->
            <xsl:value-of select="number(substring(variable/@name,3))-1"/> 
          </xsl:attribute>
          <xsl:attribute name="degree">
            <xsl:apply-templates select="integer"/>
          </xsl:attribute>
        </xsl:element>
      </xsl:for-each>
    </MONOME>
  </xsl:template>


<!-- **************************************************************************************** 
     **  Matrix orders
     **************************************************************************************** -->

  <xsl:template match="matrix-order">
    <ORDERING numstrictcol="1">
      <xsl:attribute name="type">
        <xsl:choose>
          <xsl:when test="@type = 'arctic'">amatrix</xsl:when>
          <xsl:otherwise>matrix</xsl:otherwise>
        </xsl:choose>
      </xsl:attribute>
      <xsl:attribute name="size" select="@dimension"/>
      <xsl:for-each select="matrix-interpretation/symbol">        
        <POLYSYMB>
          <xsl:apply-templates select="."/>
          <xsl:apply-templates select="../mpolynomial"/>
        </POLYSYMB>
      </xsl:for-each>  
    </ORDERING>
  </xsl:template>
  
  <xsl:template match="mpolynomial">
    <POLYNOMIAL>
      <SUMPOLY>
        <xsl:apply-templates select="mmonomial[count(polo-factor) = 0]"/>
        <xsl:apply-templates select="mmonomial[count(polo-factor) &gt; 0]"/>
      </SUMPOLY>
    </POLYNOMIAL>
  </xsl:template>
  
  <xsl:template match="mmonomial">
    <POLYNOMIAL>
      <MONOME>
        <COEF>
          <xsl:choose>
            <xsl:when test="count(polo-factor) &lt; 1">
              <xsl:apply-templates select="matrix/mvect"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:apply-templates select="matrix"/>
            </xsl:otherwise>
          </xsl:choose>
        </COEF>
        <xsl:for-each select="polo-factor">
          <ARG>
            <xsl:attribute name="num">
              <!-- remove prefix x_ of aprove's format and adjust numbering (aprove counts from x_1,..., A3Pat from 0,...) -->
              <xsl:value-of select="number(substring(variable/@name,3))-1"/> 
            </xsl:attribute>
            <xsl:attribute name="degree">
              <xsl:apply-templates select="integer"/>
            </xsl:attribute>
          </ARG>
        </xsl:for-each>
      </MONOME>
    </POLYNOMIAL>
  </xsl:template>
  
  <xsl:template match="matrix">
    <MATRIX>
      <xsl:for-each select="mvect">
        <COLUMN>
          <xsl:for-each select="*">
            <xsl:apply-templates mode="with-tag" select="." />
          </xsl:for-each>
        </COLUMN>
      </xsl:for-each>
    </MATRIX>
  </xsl:template>
  
  <xsl:template match="mvect">
    <COLUMN>
      <xsl:apply-templates mode="with-tag"/>
    </COLUMN>
  </xsl:template>

<!-- **************************************************************************************** 
     **  Path orders
     **************************************************************************************** -->

  <xsl:template match="path-order">
    <xsl:variable name="signature">
      <xsl:copy-of select="../../../../basic-obligation//signature"/>
    </xsl:variable>
    <ORDERING type="rpo">
      <xsl:apply-templates select="afs"/>
      <xsl:apply-templates select="statusMap">
        <xsl:with-param name="signature" select="$signature"/>
      </xsl:apply-templates>
      <xsl:apply-templates select="precedence">
        <xsl:with-param name="signature" select="$signature"/>
      </xsl:apply-templates>
    </ORDERING>
  </xsl:template>
  
  <xsl:template match="afs">
    <AFS>
      <xsl:apply-templates/>
    </AFS>
  </xsl:template>
  
  <xsl:template match="filter">
    <xsl:choose>
      <xsl:when test="count(arg) = 0">
        <PROJCONST>
          <xsl:apply-templates select="symbol"/>
        </PROJCONST>
      </xsl:when>
      <xsl:when test="(count(arg) = 1) and (@collapse = 'true')">
        <PROJARG>
          <xsl:attribute name="num">
            <xsl:value-of select="number(arg[1]/text()) - 1"/>
          </xsl:attribute>
          <xsl:apply-templates select="symbol"/>
        </PROJARG>
      </xsl:when>
      <xsl:otherwise>
        <FILTERARG>
          <xsl:apply-templates select="symbol"/>
          <FILTER>
            <xsl:for-each select="arg">
              <INT><xsl:value-of select="number(text())-1"/></INT>
            </xsl:for-each>
          </FILTER>
          <xsl:variable name="symbol" select="symbol/@name"/>
          <xsl:if test="count(../../statusMap/status[symbol/@name = $symbol]/lex/integer) > 0">
            <PERMUT>
              <xsl:for-each select="../../statusMap/status[symbol/@name = $symbol]/lex/integer">
                <INT><xsl:value-of select="number(@value)-1"/></INT>
              </xsl:for-each>
            </PERMUT>
          </xsl:if>
        </FILTERARG>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template match="statusMap">
    <xsl:param name="signature"/>
    <STATUSLIST>
      <xsl:for-each select="status">
        <xsl:variable name="status">
          <xsl:choose>
            <xsl:when test="count(lex) > 0">lex</xsl:when>
            <xsl:otherwise>mult</xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <STATUS>
          <xsl:attribute name="status" select="$status"/>
          <xsl:apply-templates select="symbol"/>
        </STATUS>
      </xsl:for-each>
    </STATUSLIST>
  </xsl:template>
  
  <xsl:template match="precedence">
    <xsl:param name="signature"/>
    <PRECEDENCE>
      <xsl:apply-templates select="prec[@type='gt']"/>
    </PRECEDENCE>
    <EQUIVALENCE>
      <xsl:apply-templates select="prec[@type='eq']"/>
    </EQUIVALENCE>
  </xsl:template>
  
  <xsl:template match="prec">
    <xsl:choose>
      <xsl:when test="@type='gt'">
        <!-- For CiME, the precedence must be oriented right-to left,
             ie. the /greater/ symbol goes in the rhs! -->
        <PREC>
          <OLHS>
            <xsl:apply-templates select="rhs/symbol"/>
          </OLHS>
          <ORHS>
            <xsl:apply-templates select="lhs/symbol"/>
          </ORHS>
        </PREC>
      </xsl:when>
      <xsl:otherwise>
        <EQ>
          <OLHS>
            <xsl:apply-templates select="lhs/symbol"/>
          </OLHS>
          <ORHS>
            <xsl:apply-templates select="rhs/symbol"/>
          </ORHS>
        </EQ>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>


<!-- **************************************************************************************** 
     **   Term related data-structures                       
     **  (rules, terms, etc. are straightforward, only difficulty is to output symbols) 
     **************************************************************************************** -->


<!-- symbol - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -->
  <!-- no XML tags, symbol only -->
  <xsl:template match="symbol" mode="bare">
    <xsl:value-of select="@name"/>
  </xsl:template>

  <!-- output a symbol as simple element without attributes -->
  <xsl:template match="symbol">
    <!-- <xsl:apply-templates mode="tuple" select="."/> -->
    <SYMBOL>
      <NAME>
        <xsl:value-of select="@name"/>
      </NAME>
    </SYMBOL> 
  </xsl:template>

  <!-- output a symbol as element with arity ignoring the tuple-symbol entry -->
  <xsl:template mode="as_element" match="symbol">
    <xsl:element name="SYMBOL">
      <xsl:attribute name="arity">
        <xsl:value-of select="@arity"/>
      </xsl:attribute>
      <xsl:attribute name="unmarked"/>
      <NAME>
        <xsl:value-of select="@name"/>
      </NAME>
    </xsl:element>
  </xsl:template>

  <!-- output a symbol as element with corresponding unmarked symbol (if present) -->
  <xsl:template mode="tupled" match="symbol">
    <xsl:variable name="na" select="@name"/>
    <xsl:variable name="ar" select="@arity"/>
    <xsl:element name="SYMBOL">
      <xsl:attribute name="arity"><xsl:value-of select="@arity"/></xsl:attribute>
      <xsl:attribute name="unmarked"><xsl:apply-templates mode="bare" select="exslt:node-set($defToTup)/def_to_tup/entry/tup/symbol[@name = $na and @arity = $ar]/../../def/symbol"/></xsl:attribute>
      <NAME>
        <xsl:value-of select="@name"/>
      </NAME>
    </xsl:element>
  </xsl:template>


<!-- term: x - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -->
  <xsl:template match="variable">
    <xsl:value-of select="@name" />_<!-- 
         variables end in _ to be sure that they do not clash with function names
     --> 
  </xsl:template>

  <xsl:template mode="as_element" match="variable">
    <VAR>
      <xsl:apply-templates select="."/>
    </VAR>
  </xsl:template>

<!-- term: f(t_1,..,t_n) - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -->
  <xsl:template match="fun-app">
    <xsl:apply-templates select="symbol" mode="bare"/>
    <xsl:choose>
      <xsl:when test="count(term) != 0">
        <!-- -->(<!-- -->
        <xsl:for-each select="term">
          <xsl:choose>
            <xsl:when test="position() != 1">,</xsl:when>
          </xsl:choose>
          <xsl:apply-templates select="."/>
        </xsl:for-each>
        <!-- -->)<!-- -->        
      </xsl:when>
    </xsl:choose>
  </xsl:template>

  
<!-- rule - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -->
  <xsl:template match="rule">
    <LHS>
      <xsl:apply-templates select="term[1]"/>
    </LHS>
    <RHS>
      <xsl:apply-templates select="term[2]"/>
    </RHS>
  </xsl:template>

  <xsl:template mode="trs" match="rule">
    <RULE>
      <xsl:apply-templates select="."/>
    </RULE>
  </xsl:template>

  <xsl:template mode="dp" match="rule">
    <xsl:element name="DPRULE">
      <xsl:attribute name="num">
        <xsl:value-of select="@identifier"/>
      </xsl:attribute>
      <xsl:apply-templates select="."/>
    </xsl:element>
  </xsl:template>

  <xsl:template match="trs">
    <REWSYS>
      <xsl:apply-templates mode="trs" select="."/>
    </REWSYS>
  </xsl:template>

  <xsl:template match="dps">
    <DPLIST>
      <xsl:for-each select="rule">
        <xsl:apply-templates mode="dp" select="."/>
      </xsl:for-each>
    </DPLIST>
  </xsl:template>

  <xsl:template match="qdp">
    <DPSYS>
      <xsl:apply-templates select="trs"/>
      <xsl:apply-templates select="dps"/>
    </DPSYS>
  </xsl:template>

  <xsl:template match="qtrs">
    <xsl:apply-templates select="trs"/>
  </xsl:template>




<!-- **************************************************************************************** 
     **  Extract the signature of a TRS 
     **  (set of symbols, if signature is not already provided)
     **************************************************************************************** -->

  <xsl:template mode="sig_extract" match="qtrs">
    <!-- select whether given signature should be used or whether it should be generated -->
    <xsl:choose>
      <xsl:when test="count(signature) = 1">
        <xsl:copy-of select="signature"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates mode="sig_gen" select=".">
          <xsl:with-param name="i" select="1"/>
          <xsl:with-param name="sig">
            <signature/>
          </xsl:with-param>
        </xsl:apply-templates>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  

  <xsl:template mode="sig_gen" match="qtrs">
    <xsl:param name="sig"/>
    <xsl:param name="i"/>
    <xsl:choose>
      <!-- the above choose is a loop over all symbols -->
      <!-- the case below states that we have one more symbol to visit -->
       <xsl:when test="count(.//symbol) &gt;= $i">
           <xsl:variable name="sym" select="(.//symbol)[$i]"/>
           <xsl:variable name="ar" select="$sym/@arity"/>
           <xsl:variable name="na" select="$sym/@name"/>
           <xsl:choose>
             <!-- is it a new symbol, then extend the signature -->
             <xsl:when test="count(exslt:node-set($sig)/signature/symbol[@name = $na and @arity = $ar]) = 0"> 
               <xsl:apply-templates mode="sig_gen" select=".">
                  <xsl:with-param name="i" select="$i + 1"/>
                  <xsl:with-param name="sig">
	           <signature>
                     <xsl:for-each select="exslt:node-set($sig)/signature/symbol">
                       <xsl:copy-of select="."/>
                     </xsl:for-each>
                     <xsl:copy-of select="$sym"/>
	           </signature>
                  </xsl:with-param>
               </xsl:apply-templates>
	   </xsl:when>
             <xsl:otherwise>
               <xsl:apply-templates mode="sig_gen" select=".">
                  <xsl:with-param name="i" select="$i + 1"/>
                  <xsl:with-param name="sig" select="$sig"/>
               </xsl:apply-templates>
             </xsl:otherwise>
            </xsl:choose>
        </xsl:when>
        <xsl:otherwise>
          <xsl:copy-of select="$sig"/>
        </xsl:otherwise>
     </xsl:choose>
  </xsl:template>

  <xsl:template mode="sig_var_extract" match="qtrs">
    <xsl:apply-templates mode="sig_var_gen" select=".">
      <xsl:with-param name="i" select="1"/>
      <xsl:with-param name="sig_var">
        <signature/>
      </xsl:with-param>
    </xsl:apply-templates>
  </xsl:template>

  <xsl:template mode="sig_var_gen" match="qtrs">
    <xsl:param name="sig_var"/>
    <xsl:param name="i"/>
    <xsl:choose>
      <!-- the above choose is a loop over all variables -->
      <!-- the case below states that we have more variable to visit -->
      <xsl:when test="count(.//variable) &gt;= $i">
        <xsl:variable name="var" select="(.//variable)[$i]"/>
        <xsl:variable name="na" select="$var/@name"/>
        <xsl:choose>
          <!-- is it a new variable, then extend the signature -->
          <xsl:when test="count(exslt:node-set($sig_var)/signature/variable[@name = $na]) = 0"> 
            <xsl:apply-templates mode="sig_var_gen" select=".">
              <xsl:with-param name="i" select="$i + 1"/>
              <xsl:with-param name="sig_var">
                <signature>
                  <xsl:for-each select="exslt:node-set($sig_var)/signature/variable">
                    <xsl:copy-of select="."/>
                  </xsl:for-each>
                  <xsl:copy-of select="$var"/>
                </signature>
              </xsl:with-param>
            </xsl:apply-templates>
          </xsl:when>
          <xsl:otherwise>
            <xsl:apply-templates mode="sig_var_gen" select=".">
              <xsl:with-param name="i" select="$i + 1"/>
              <xsl:with-param name="sig_var" select="$sig_var"/>
            </xsl:apply-templates>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <xsl:copy-of select="$sig_var"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>


  <!-- *********** various ********* -->

  <xsl:template match="integer"><xsl:value-of select="@value"/></xsl:template>
  
  <xsl:template mode="with-tag" match="integer">
    <INT><xsl:value-of select="@value"/></INT>
  </xsl:template>
  
  <xsl:template mode="with-tag" match="arctic-int">
    <xsl:choose>
      <xsl:when test="@infinite = 'true'">
        <INFTY/>
      </xsl:when>
      <xsl:otherwise>
        <INT><xsl:value-of select="@value"/></INT>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>


</xsl:stylesheet>
