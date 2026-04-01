<?xml version="1.0" encoding="iso-8859-1"?>

<!-- Transforms XML proofs from AProVE into the certification problem format.
-->

<!-- author: ckuknat -->

<xsl:transform xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
               xmlns:exslt="http://exslt.org/common"
               xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" 
               exclude-result-prefixes="exslt"
               version="2.0">

  <xsl:output method="xml"/>
  <xsl:output method="xml" indent="yes" name="xml"/>
  

  <!-- Starting point -->

  <xsl:template match="/">
    <xsl:choose> 
      <xsl:when test="proof-obligation/@partial = 'true'">
        <xsl:for-each select="//proof-obligation">
          <xsl:if test="count(proposition) &gt; 0"> <!-- ignore conjunction and proved -->
            <xsl:if test="count(proposition/proof/non-scc) &lt; 1">
              <xsl:variable name="filename" select="concat('partialProof-', @identifier , '.xml')" />
              <xsl:result-document href="partialProofsFolder/{$filename}" format="xml">
                <xsl:call-template name="the-proof">
                  <xsl:with-param name="proof-obligation" select="."/>
                </xsl:call-template>
              </xsl:result-document>
            </xsl:if>
          </xsl:if>
        </xsl:for-each>    
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="the-proof">
          <xsl:with-param name="proof-obligation" select="proof-obligation"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template name="the-proof">
  <xsl:param name="proof-obligation" />
    <xsl:processing-instruction name="xml-stylesheet">type="text/xsl" href="cpfHTML.xsl"</xsl:processing-instruction>
    <certificationProblem xsi:noNamespaceSchemaLocation="cpf.xsd">
      <input>
        <xsl:call-template name="input">
          <xsl:with-param name="proof-obligation" select="$proof-obligation"/>
        </xsl:call-template>
      </input>
      <cpfVersion>2.1</cpfVersion>
      <xsl:call-template name="proof">
        <xsl:with-param name="proof-obligation" select="$proof-obligation"/>
      </xsl:call-template>
      <xsl:call-template name="origin">
        <xsl:with-param name="proof-obligation" select="$proof-obligation"/>
      </xsl:call-template>
    </certificationProblem>
  </xsl:template>

  <xsl:template name="proof">
  <xsl:param name="proof-obligation" />
    <proof>
      <xsl:choose>
        <xsl:when test="count(//qtrs-nontermination-proof) &gt; 0">
          <xsl:apply-templates mode="nonTerm"
            select="$proof-obligation/proposition/proof" />
        </xsl:when>
        <xsl:when test="count(//qsrs-nontermination-proof) &gt; 0">
          <xsl:apply-templates mode="nonTerm"
            select="$proof-obligation/proposition/proof" />
        </xsl:when>
        <xsl:when test="count(//reltrs-nontermination-proof) &gt; 0">
          <xsl:apply-templates mode="nonTerm"
            select="$proof-obligation/proposition/proof" />
        </xsl:when>
        <xsl:when test="count(//relsrs-nontermination-proof) &gt; 0">
          <xsl:apply-templates mode="nonTerm"
            select="$proof-obligation/proposition/proof" />
        </xsl:when>
        <xsl:when test="count(//gtrs-crit-rule-proof) &gt; 0">
          <xsl:apply-templates mode="nonTerm"
            select="$proof-obligation/proposition/proof" />
        </xsl:when>
        <xsl:when test="count(//qdp-nontermination-proof) &gt; 0">
          <xsl:apply-templates mode="nonTerm"
            select="$proof-obligation/proposition/proof" />
        </xsl:when>
        <xsl:when test="count(//qdp-nonloop-proof) &gt; 0">
          <xsl:apply-templates mode="nonTerm"
            select="$proof-obligation/proposition/proof" />
        </xsl:when>
        <xsl:otherwise>
          <xsl:apply-templates select="$proof-obligation/proposition/proof" />
        </xsl:otherwise>
      </xsl:choose>
    </proof>
  </xsl:template>
  
  <xsl:template name="input">
  <xsl:param name="proof-obligation" />
  <xsl:param name="dpT" select="false()"/>
    <xsl:choose>
      <xsl:when test="count($proof-obligation/proposition/basic-obligation/reltrs-termination-obligation) &gt; 0">
        <trsInput>
          <trs>
            <xsl:apply-templates select="$proof-obligation/proposition/basic-obligation/reltrs-termination-obligation/reltrs/trs[1]" />
          </trs>
          <relativeRules>
            <rules>
              <xsl:call-template name="ruleset">
                <xsl:with-param name="rules" select="$proof-obligation/proposition/basic-obligation/reltrs-termination-obligation/reltrs/trs[2]" />
              </xsl:call-template>
            </rules>
          </relativeRules>
        </trsInput>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="count($proof-obligation/proposition/basic-obligation/gtrs-termination-obligation/gtrs/trs)">
            <trsInput>
              <trs>
                <xsl:apply-templates select="$proof-obligation/proposition/basic-obligation/gtrs-termination-obligation/gtrs/trs" />
              </trs>              
              <xsl:if test="$proof-obligation/proposition/basic-obligation/gtrs-termination-obligation/gtrs/innermost">
                <strategy><innermost/></strategy>    
              </xsl:if>                            
            </trsInput>
          </xsl:when>
          <xsl:otherwise>
            <xsl:choose>
              <xsl:when test="count($proof-obligation/proposition/basic-obligation/qtrs-termination-obligation) &gt; 0">
                <trsInput>
                  <trs>
                    <xsl:apply-templates select="$proof-obligation/proposition/basic-obligation/qtrs-termination-obligation/qtrs/trs" />
                  </trs>
                  <xsl:if test="count($proof-obligation/proposition/basic-obligation/qtrs-termination-obligation/qtrs/innermost) &gt; 0">
                    <strategy>
                      <xsl:choose>
                        <xsl:when test="$proof-obligation/proposition/basic-obligation/qtrs-termination-obligation/qtrs/innermost/@exactly = 'true'">
                          <innermost/>
                        </xsl:when>
                        <xsl:otherwise>
                          <innermostLhss>
                            <xsl:apply-templates select="$proof-obligation/proposition/basic-obligation/qtrs-termination-obligation/qtrs/qtermset"/>
                          </innermostLhss>
                        </xsl:otherwise>
                      </xsl:choose>
                    </strategy>
                  </xsl:if>
                </trsInput>
              </xsl:when>
              <xsl:otherwise>
                <dpInput>
                  <trs>
                    <xsl:apply-templates select="$proof-obligation/proposition/basic-obligation/qdp-termination-obligation/qdp/trs" />
                  </trs>
                  <dps>
                    <rules>
                      <xsl:apply-templates select="$proof-obligation/proposition/basic-obligation/qdp-termination-obligation/qdp/dps" />
                    </rules>
                  </dps>
                  <xsl:if test="count($proof-obligation/proposition/basic-obligation/qdp-termination-obligation/qdp/innermost) &gt; 0">
                    <strategy>
                      <!-- I would'nt change the following again, if something new comes up, DO IT AGAIN!!! -->
                      <xsl:choose>
                        <xsl:when test="$proof-obligation/proposition/basic-obligation/qdp-termination-obligation/qdp/innermost/@exactly = 'true'">
                          <innermost/>
                        </xsl:when>
                        <xsl:otherwise>
                          <xsl:choose>
                            <xsl:when test="$dpT">
                              <xsl:choose>
                                <xsl:when test="count($proof-obligation/../proof/qtrs-dependency-pairs-proof) &gt; 0">
                                  <xsl:if test="count($proof-obligation/../basic-obligation/qtrs-termination-obligation/qtrs/innermost) &gt; 0">
                                    <xsl:choose>
                                      <xsl:when test="$proof-obligation/../basic-obligation/qtrs-termination-obligation/qtrs/innermost/@exactly = 'true'">
                                        <innermost/>
                                      </xsl:when>
                                      <xsl:otherwise>
                                        <innermostLhss>
                                          <xsl:apply-templates select="$proof-obligation/proposition/basic-obligation/qdp-termination-obligation/qdp/qtermset"/>
                                        </innermostLhss>
                                      </xsl:otherwise>
                                    </xsl:choose>
                                  </xsl:if>
                                </xsl:when>
                                <xsl:otherwise>
                                  <innermostLhss>
                                    <xsl:apply-templates select="$proof-obligation/proposition/basic-obligation/qdp-termination-obligation/qdp/qtermset"/>
                                  </innermostLhss>
                                </xsl:otherwise>
                              </xsl:choose>
                            </xsl:when>
                            <xsl:otherwise>
                              <innermostLhss>
                                <xsl:apply-templates select="$proof-obligation/proposition/basic-obligation/qdp-termination-obligation/qdp/qtermset"/>
                              </innermostLhss>
                            </xsl:otherwise>
                          </xsl:choose>
                        </xsl:otherwise>
                      </xsl:choose>
                    </strategy>
                  </xsl:if>
                  <xsl:choose>
                    <xsl:when test="$proof-obligation/proposition/basic-obligation/qdp-termination-obligation/qdp/minimality-flag/boolean/@value = 'true'">
                      <minimal>true</minimal>
                    </xsl:when>
                    <xsl:otherwise>
                      <minimal>false</minimal>
                    </xsl:otherwise>
                  </xsl:choose>
                </dpInput>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="origin">
  <xsl:param name="proof-obligation" />
    <origin>
      <proofOrigin>
        <tool>
          <name>
            AProVE
          </name>
          <version>
            <xsl:value-of select="$proof-obligation/@commit-id" />
          </version>
          <url>
            http://aprove.informatik.rwth-aachen.de/
          </url>
        </tool>
        <toolUser>
          <firstName>
            John
          </firstName>
          <lastName>
            Doe
          </lastName>
        </toolUser>
      </proofOrigin>
      <inputOrigin>
        <!-- input origin -->
      </inputOrigin>
    </origin>
  </xsl:template>

  <!-- *************************************************************************
       ***                            Proofs                                 ***
       *************************************************************************
-->

  <xsl:template match="proof">    
    <xsl:apply-templates/>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="proof">
      <xsl:apply-templates mode="nonTerm"/>
  </xsl:template>

  <xsl:template name="trsProofOrAssumption">
  <xsl:param name="proofObligation"/>
    <xsl:if test="count($proofObligation/proved) = 0">
      <xsl:choose>
        <xsl:when test="$proofObligation/@partial = 'true'">
          <trsTerminationProof>
            <terminationAssumption>
              <xsl:call-template name="input">
                <xsl:with-param name="proof-obligation" select="$proofObligation"/>
              </xsl:call-template>
            </terminationAssumption>
          </trsTerminationProof>
        </xsl:when>
        <xsl:otherwise>
          <xsl:apply-templates select="$proofObligation/proposition/proof"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:if>
  </xsl:template>
  
  <xsl:template name="trsNontermProofOrAssumption">
  <xsl:param name="proofObligation"/>
    <xsl:choose>
      <xsl:when test="$proofObligation/@partial = 'true'">
        <trsNonterminationProof>
          <nonterminationAssumption>
            <xsl:call-template name="input">
              <xsl:with-param name="proof-obligation" select="$proofObligation"/>
            </xsl:call-template>
          </nonterminationAssumption>
        </trsNonterminationProof>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates mode="nonTerm" select="$proofObligation/proposition/proof"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template name="reltrsProofOrAssumption">
  <xsl:param name="proofObligation"/>
    <xsl:if test="count($proofObligation/proved) = 0">
      <xsl:choose>
        <xsl:when test="$proofObligation/@partial = 'true'">
          <relativeTerminationProof>
            <relativeTerminationAssumption>
              <xsl:call-template name="input">
                <xsl:with-param name="proof-obligation" select="$proofObligation"/>
              </xsl:call-template>
            </relativeTerminationAssumption>
          </relativeTerminationProof>
        </xsl:when>
        <xsl:otherwise>
          <xsl:apply-templates select="$proofObligation/proposition/proof"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:if>
  </xsl:template>
  
  <xsl:template name="reltrsNontermProofOrAssumption">
  <xsl:param name="proofObligation"/>
    <xsl:choose>
      <xsl:when test="$proofObligation/@partial = 'true'">
        <relativeNonterminationProof>
          <relativeNonterminationAssumption>
            <xsl:call-template name="input">
              <xsl:with-param name="proof-obligation" select="$proofObligation"/>
            </xsl:call-template>
          </relativeNonterminationAssumption>
        </relativeNonterminationProof>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates mode="nonTerm" select="$proofObligation/proposition/proof"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template name="dpsProofOrAssumption">
  <xsl:param name="proofObligation"/>
  <xsl:param name="dpT" select="false()"/>
    <xsl:if test="count($proofObligation/proved) = 0">
      <xsl:choose>
        <xsl:when test="$proofObligation/@partial = 'true'">
          <dpProof>
            <finitenessAssumption>
              <xsl:call-template name="input">
                <xsl:with-param name="proof-obligation" select="$proofObligation"/>
                <xsl:with-param name="dpT" select="$dpT"/>
              </xsl:call-template>
            </finitenessAssumption>
          </dpProof>
        </xsl:when>
        <xsl:otherwise>
          <xsl:apply-templates select="$proofObligation/proposition/proof"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:if>
  </xsl:template>
  
  <xsl:template name="dpsNontermProofOrAssumption">
  <xsl:param name="proofObligation"/>
    <xsl:choose>
      <xsl:when test="$proofObligation/@partial = 'true'">
        <dpNonterminationProof>
          <infinitenessAssumption>
            <xsl:call-template name="input">
              <xsl:with-param name="proof-obligation" select="$proofObligation"/>
            </xsl:call-template>
          </infinitenessAssumption>
        </dpNonterminationProof>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates mode="nonTerm" select="$proofObligation/proposition/proof"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- 
-->
  <!--
    *************************************************************************
    *** Dependency pair transformation. ***
    *************************************************************************
  -->

  <xsl:template match="qtrs-dependency-pairs-proof">
    <trsTerminationProof>
      <dpTrans>
        <dps>
          <rules>
            <xsl:apply-templates select="dps/rule" />
          </rules>
        </dps>
        <markedSymbols>
          <xsl:text>true</xsl:text>
        </markedSymbols>
        <xsl:call-template name="dpsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
          <xsl:with-param name="dpT" select="true()"/>
        </xsl:call-template>
      </dpTrans>
    </trsTerminationProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qtrs-dependency-pairs-proof">
    <trsNonterminationProof>
      <dpTrans>
        <dps>
          <rules>
            <xsl:apply-templates select="dps/rule" />
          </rules>
        </dps>
        <markedSymbols>
          <xsl:text>true</xsl:text>
        </markedSymbols>
        <xsl:call-template name="dpsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </dpTrans>
    </trsNonterminationProof>
  </xsl:template>

  <!--
    *************************************************************************
    *** srs-as-trs-proof ***
    *************************************************************************
  -->

  <xsl:template match="srs-as-trs-proof">
    <trsTerminationProof>
      <xsl:call-template name="trsProofOrAssumption">
        <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
      </xsl:call-template>      
    </trsTerminationProof>
  </xsl:template>

  <xsl:template mode="nonTerm" match="srs-as-trs-proof">
    <trsNonterminationProof>
      <xsl:call-template name="trsNontermProofOrAssumption">
        <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
      </xsl:call-template>      
    </trsNonterminationProof>
  </xsl:template>

  <!--
    *************************************************************************
    *** srs-reverse-proof ***
    *************************************************************************
  -->

  <xsl:template match="qtrs-reverse-proof">
    <trsTerminationProof>
      <stringReversal>
        <trs>
          <xsl:apply-templates select="trs" />
        </trs>
        <xsl:call-template name="trsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>        
      </stringReversal>
    </trsTerminationProof>
  </xsl:template>

  <xsl:template mode="nonTerm" match="qtrs-reverse-proof">
    <trsNonterminationProof>
      <stringReversal>
        <trs>
          <xsl:apply-templates select="trs" />
        </trs>
        <xsl:call-template name="trsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </stringReversal>
    </trsNonterminationProof>
  </xsl:template>

  <xsl:template match="reltrs-reverse-proof">
    <relativeTerminationProof>
      <trs>
        <xsl:apply-templates select="trs" />
      </trs>
      <stringReversal>
        <xsl:call-template name="reltrsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </stringReversal>
    </relativeTerminationProof>
  </xsl:template>

  <xsl:template mode="nonTerm" match="reltrs-reverse-proof">
    <relativeNonterminationProof>
      <trs>
        <xsl:apply-templates select="trs" />
      </trs>
      <srsReversal>
        <xsl:call-template name="reltrsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </srsReversal>
    </relativeNonterminationProof>
  </xsl:template>

  <!-- *************************************************************************
       ***                   Non- termination- proof                        ***
       *************************************************************************-->
       
<!-- *************************************************************************
       ***                   Looping                        ***
       *************************************************************************-->       

  <xsl:template mode="nonTerm" match="qdp-nontermination-proof">
    <dpNonterminationProof>
      <loop>
        <rewriteSequence>
          <xsl:apply-templates select="qdp-rewrite-sequence"/>
        </rewriteSequence>
        <xsl:apply-templates select="substitution"/>
        <xsl:apply-templates select="context"/>
      </loop>
    </dpNonterminationProof>
  </xsl:template>
  
  <xsl:template match="qdp-rewrite-sequence"> 
    <startTerm>
      <xsl:apply-templates select="term"/>
    </startTerm>
    <xsl:apply-templates mode="nonTerm" select="step"/>
  </xsl:template>
  
  <xsl:template mode="positionInTerm" match="position">
    <positionInTerm>
      <xsl:if test="count(integer) &gt; 0">
        <xsl:call-template name="positionList">
          <xsl:with-param name="node" select="."/>
          <xsl:with-param name="stop" select="count(integer)"/>
        </xsl:call-template>
      </xsl:if>
    </positionInTerm>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="step">
    <rewriteStep>
      <xsl:if test="count(position) = 0">
        <positionInTerm/>
      </xsl:if>
      <xsl:apply-templates mode="positionInTerm" select="position"/>
      <xsl:apply-templates select="rule"/>
      <xsl:if test="count(relative-step) &gt; 0">
        <relative/>
      </xsl:if>
      <xsl:apply-templates select="term"/>
    </rewriteStep>
  </xsl:template>

  <xsl:template mode="nonTerm" match="gtrs-crit-rule-proof">
    <trsNonterminationProof>
      <variableConditionViolated />
    </trsNonterminationProof>
  </xsl:template>

  <xsl:template mode="nonTerm" match="qtrs-nontermination-proof">
    <trsNonterminationProof>
      <xsl:choose>
        <xsl:when test="count(loop)=0">
          <variableConditionViolated />
        </xsl:when>
       <xsl:otherwise>
          <xsl:apply-templates />
        </xsl:otherwise>
      </xsl:choose>
    </trsNonterminationProof>
  </xsl:template>

  <xsl:template mode="nonTerm" match="reltrs-nontermination-proof">
    <relativeNonterminationProof>
      <xsl:choose>
        <xsl:when test="count(loop)=0">
          <variableConditionViolated />
        </xsl:when>
        <xsl:otherwise>
          <xsl:apply-templates />
        </xsl:otherwise>
      </xsl:choose>
    </relativeNonterminationProof>
  </xsl:template>

  <xsl:template match="relative-loop">
    <loop>
      <rewriteSequence>
        <startTerm>
          <xsl:apply-templates select="relative-step/s-steps/step[1]/term[1]"/>
        </startTerm>
        <xsl:apply-templates mode="reltrs" select="s-steps/step"/>
        <xsl:apply-templates select="step"/>
      </rewriteSequence>
      <xsl:apply-templates select="substitution"/>
      <xsl:apply-templates select="context"/>
    </loop>
  </xsl:template>
  
  <xsl:template match="step">
    <rewriteStep>
      <positionInTerm>
        <xsl:if test="count(position/integer) &gt; 0">
          <xsl:call-template name="positionList">
            <xsl:with-param name="node" select="position"/>
            <xsl:with-param name="stop" select="count(position/integer)"/>
          </xsl:call-template>
        </xsl:if>
      </positionInTerm>
      <xsl:apply-templates select="rule"/>
      <xsl:apply-templates select="term[2]"/>
    </rewriteStep>
  </xsl:template>
  
  <xsl:template match="relative-step">
    <xsl:apply-templates mode="reltrs" select="s-steps/step"/>
    <xsl:apply-templates select="step"/>    
  </xsl:template>
  
  <xsl:template mode="reltrs" match="step">
    <rewriteStep>
      <positionInTerm>
        <xsl:if test="count(position/integer) &gt; 0">
          <xsl:call-template name="positionList">
            <xsl:with-param name="node" select="position"/>
            <xsl:with-param name="stop" select="count(position/integer)"/>
          </xsl:call-template>
        </xsl:if>
      </positionInTerm>
      <xsl:apply-templates select="rule"/>
      <relative/>
      <xsl:apply-templates select="term[2]"/>
    </rewriteStep>
  </xsl:template>
  
  <xsl:template match="loop">
    <loop>
      <rewriteSequence>
        <startTerm>
          <xsl:choose>
            <xsl:when test="count(relative-step) &gt; 0">
              <xsl:choose>
                <xsl:when test="count(relative-step/s-steps) &gt; 0">
                  <xsl:apply-templates select="relative-step[1]/s-steps/step[1]/term[1]"/>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:apply-templates select="relative-step[1]/step[1]/term[1]"/>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:when>
            <xsl:otherwise>
              <xsl:apply-templates select="step[1]/term[1]"/>
            </xsl:otherwise>
          </xsl:choose>
        </startTerm>
        <xsl:choose>
            <xsl:when test="count(relative-step) &gt; 0">
              <xsl:apply-templates select="relative-step"/>              
            </xsl:when>
            <xsl:otherwise>
              <xsl:apply-templates select="step"/>
            </xsl:otherwise>
          </xsl:choose>
      </rewriteSequence>
      <xsl:apply-templates select="substitution"/>
      <xsl:apply-templates select="context"/>
    </loop>
  </xsl:template>

  <xsl:template name="positionList">
    <xsl:param name="node"/>
    <xsl:param name="start" select="1"/>
    <xsl:param name="stop" select="count($node/integer)"/>
    <xsl:choose>
      <xsl:when test="$start &gt; $stop">
        <xsl:text/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:if test="count($node/integer) &gt; 0">
          <position>
            <xsl:value-of select="$node/integer[$start]/@value"/>
          </position>
        </xsl:if>
        <xsl:call-template name="positionList">
          <xsl:with-param name="node" select="$node"/>
          <xsl:with-param name="start" select="$start+1"/>
          <xsl:with-param name="stop" select="$stop"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- Converts a list of <term> elements that are found below a common parent.
       Params: $parent - parent element of the terms; $start - index of the first
       term to be included in the output; $stop - dito for the last term
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
        <xsl:apply-templates select="$parent/term[$start]"/>
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
      <xsl:when test="count(symbol) = 0 and count(labeledSymbol) = 0">
        <box/>
      </xsl:when>
      <xsl:otherwise>
        <funContext>
        <xsl:apply-templates select="./symbol"/>
        <xsl:apply-templates select="./labeledSymbol"/>
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
            <xsl:when test="count(labeledSymbol) = 0">
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
            </xsl:when>
            <xsl:otherwise>
              <xsl:choose>
                  <xsl:when test="$numLeftTerms = labeledSymbol/@arity - count(context/box)">
                  <xsl:text/>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:call-template name="termList">
                    <xsl:with-param name="parent" select="."/>
                    <xsl:with-param name="start" select="$numLeftTerms + 1"/>
                  </xsl:call-template>
                  </xsl:otherwise>
                </xsl:choose>
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
      <xsl:apply-templates select="$parent/substitute[$i]/variable"/>
      <xsl:apply-templates select="$parent/substitute[$i]/term"/>
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
  
  <!-- *************************************************************************
       ***                   Non - Looping                                   ***
       *************************************************************************-->
       
  <xsl:template mode="nonTerm" match="qdp-nonloop-proof">
    <dpNonterminationProof>
    <nonLoop>
      <xsl:apply-templates select="proofed-rule"/>
      <xsl:apply-templates select="substitution[1]"/>
      <xsl:apply-templates select="substitution[2]"/>
      <natural>
        <xsl:value-of select="integer[1]/@value" />
      </natural>
      <natural>
        <xsl:value-of select="integer[2]/@value" />
      </natural>
      <xsl:apply-templates mode="positionInTerm" select="position"/>
    </nonLoop>
    </dpNonterminationProof>
  </xsl:template>
  
  <xsl:template match="proofed-rule">
    <patternRule>
      <xsl:apply-templates select="original-rule/pattern-rule"/>
      <xsl:apply-templates select="initial-pumping/pattern-rule"/>
      <xsl:apply-templates select="initial-pumping-context/pattern-rule"/>
      <xsl:apply-templates select="equivalence/pattern-rule"/>
      <xsl:apply-templates select="narrowing/pattern-rule"/>
      <xsl:apply-templates select="instantiation/pattern-rule"/>
      <xsl:apply-templates select="rewriting/pattern-rule"/>
      <xsl:apply-templates select="original-rule"/>
      <xsl:apply-templates select="initial-pumping"/>
      <xsl:apply-templates select="initial-pumping-context"/>
      <xsl:apply-templates select="equivalence"/>
      <xsl:apply-templates select="narrowing"/>
      <xsl:apply-templates select="instantiation"/>
      <xsl:apply-templates select="rewriting"/>
    </patternRule>
  </xsl:template>
  
  <xsl:template match="pattern-rule">
    <xsl:apply-templates select="pattern-term[1]"/>
    <xsl:apply-templates select="pattern-term[2]"/>
  </xsl:template>
  
  <xsl:template match="pattern-term">
    <patternTerm>
      <xsl:apply-templates select="term"/>
      <xsl:apply-templates select="substitution[1]"/>
      <xsl:apply-templates select="substitution[2]"/>
    </patternTerm>
  </xsl:template>
  
  <xsl:template match="original-rule">
    <originalRule>
      <xsl:apply-templates select="rule"/>
      <isPair>
        <xsl:value-of select="boolean/@value"/>
      </isPair>
    </originalRule>
  </xsl:template>
  
  <xsl:template match="equivalence">
    <equivalence>  
      <xsl:apply-templates select="proofed-rule"/>
      <xsl:choose>
        <xsl:when test="count(left) &gt; 0">
          <left/>
        </xsl:when>
        <xsl:otherwise>
          <right/>
        </xsl:otherwise>
      </xsl:choose>
      <xsl:apply-templates select="pattern-equivalence"/>
    </equivalence>    
  </xsl:template>
  
  <xsl:template match="pattern-equivalence">
    <patternEquivalence>
      <xsl:apply-templates select="domain-renaming"/>
      <xsl:apply-templates select="irrelevant"/>
      <xsl:apply-templates select="simplification"/>
    </patternEquivalence>
  </xsl:template>
  
  <xsl:template match="domain-renaming">
    <domainRenaming>
      <xsl:apply-templates select="substitution"/>
    </domainRenaming>
  </xsl:template>
  
  <xsl:template match="irrelevant">
    <irrelevant>
      <xsl:apply-templates select="substitution[1]"/>
      <xsl:apply-templates select="substitution[2]"/>
    </irrelevant>
  </xsl:template>
  
  <xsl:template match="simplification">
    <simplification>
      <xsl:apply-templates select="substitution[1]"/>
      <xsl:apply-templates select="substitution[2]"/>
    </simplification>
  </xsl:template>
  
  <xsl:template match="instantiation">
    <instantiation>
      <xsl:apply-templates select="proofed-rule"/>
      <xsl:apply-templates select="substitution"/>
      <xsl:apply-templates select="base"/>
      <xsl:apply-templates select="pumping"/>
      <xsl:apply-templates select="closing"/>
    </instantiation>
  </xsl:template>
  
  <xsl:template match="base">
    <base/>
  </xsl:template>
  
  <xsl:template match="pumping">
    <pumping>
      <xsl:apply-templates select="variable"/>
    </pumping>
  </xsl:template>
  
  <xsl:template match="closing">
    <closing>
      <xsl:apply-templates select="variable"/>
    </closing>
  </xsl:template>
  
  <xsl:template match="initial-pumping">
    <!-- TODO I need an example to test this here, also implement -->
    <initialPumping>
      <xsl:apply-templates select="proofed-rule"/>
      <xsl:apply-templates select="substitution[1]"/>
      <xsl:apply-templates select="substitution[2]"/>
    </initialPumping>
  </xsl:template>
  
  <xsl:template match="initial-pumping-context">
    <!-- TODO I need an example to test this here, also implement -->
    <initialPumpingContext>
      <xsl:apply-templates select="proofed-rule"/>
      <xsl:apply-templates select="substitution"/>
      <xsl:apply-templates mode="positionInTerm" select="position"/>
      <xsl:apply-templates select="variable"/>
    </initialPumpingContext>
  </xsl:template>
  
  <xsl:template match="narrowing">
    <!-- TODO I need an example to test this here, also implement -->
    <narrowing>
      <xsl:apply-templates select="proofed-rule[1]"/>
      <xsl:apply-templates select="proofed-rule[2]"/>
      <xsl:apply-templates mode="positionInTerm" select="position"/>
    </narrowing>
  </xsl:template>
  
  <xsl:template match="rewriting">
    <!-- TODO I need an example to test this here, also implement -->
    <rewriting>
      <xsl:apply-templates select="proofed-rule"/>
      <xsl:apply-templates mode="nonloop" select="rewrite-sequence"/>
      <rewriteSequence>
        <startTerm>
          <xsl:apply-templates select="term"/>
        </startTerm>
        <xsl:apply-templates mode="nonloop" select="step"/>
      </rewriteSequence>
      <xsl:apply-templates select="base"/>
      <xsl:apply-templates select="pumping"/>
      <xsl:apply-templates select="closing"/>
      <!-- 
      -->
    </rewriting>
  </xsl:template>
  
  <xsl:template mode="nonloop" match="step">
    <rewriteStep>
      <xsl:apply-templates mode="positionInTerm" select="position"/>
      <xsl:apply-templates select="rule"/>
      <xsl:apply-templates select="term"/>
    </rewriteStep>
  </xsl:template>

  <!-- ****************************************************************************************
       **  R-is-empty proof
       ****************************************************************************************
-->

  <xsl:template match="rel-r-is-empty-proof">
      <relativeTerminationProof>
          <rIsEmpty/>
      </relativeTerminationProof>
  </xsl:template>
  
  <xsl:template match="r-is-empty-proof">
    <trsTerminationProof>
      <rIsEmpty/>
    </trsTerminationProof>
  </xsl:template>

  <!--
    ****************************************************************************************
    ** P-is-empty proof
    ****************************************************************************************
  -->

  <xsl:template match="p-is-empty-proof">
    
    <dpProof>
      <pIsEmpty />
    </dpProof>
  </xsl:template>

  <!-- ****************************************************************************************
       **  Root Labeling
       ****************************************************************************************
-->

  <xsl:template match="qtrs-root-labeling-proof">  
    <trsTerminationProof>
      <semlab>
        <model>
          <rootLabeling/>
        </model>
        <trs>
          <xsl:apply-templates select="trs" />
        </trs>
        <xsl:call-template name="trsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </semlab>
    </trsTerminationProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qtrs-root-labeling-proof">  
    <trsNonterminationProof>
      <semlab>
        <model>
          <rootLabeling/>
        </model>
        <trs>
          <xsl:apply-templates select="trs" />
        </trs>
        <xsl:call-template name="trsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </semlab>
    </trsNonterminationProof>
  </xsl:template>
  
    <!-- ****************************************************************************************
       **  Uncurrying
       ****************************************************************************************
-->

  <xsl:template match="qdp-uncurrying-proof">  
    <dpProof>
      <uncurryProc>
        <xsl:if test="count(applicative-top)">
            <applicativeTop>
                <xsl:value-of select="applicative-top/@arity"/>
            </applicativeTop>
        </xsl:if>
        <xsl:apply-templates select="uncurry-information"/>
        <dps>
          <rules>
            <xsl:apply-templates select="qdp"/>
          </rules>
        </dps>
        <trs>
          <xsl:apply-templates select="trs" />
        </trs>
        <xsl:call-template name="dpsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>        
      </uncurryProc>
    </dpProof>
  </xsl:template>
  
  <xsl:template match="uncurry-information">
    <uncurryInformation>
      <xsl:apply-templates select="symbol"/>
      <uncurriedSymbols>
        <xsl:apply-templates select="uncurry-information-entry"/>
      </uncurriedSymbols>
      <uncurryRules>
        <rules>
          <xsl:apply-templates select="trs[1]/rule"/>
        </rules>
      </uncurryRules>
      <etaRules>
        <rules>
          <xsl:apply-templates select="trs[2]/rule"/>
        </rules>
      </etaRules>
    </uncurryInformation>
  </xsl:template>
  
  <xsl:template match="uncurry-information-entry">
    <uncurriedSymbolEntry>
      <xsl:apply-templates select="symbol"/>
      <arity>
        <xsl:value-of select="@arity"/>
      </arity>
      <xsl:choose>
        <xsl:when test="count(symbol-entries/symbol) = 0">
          <xsl:apply-templates select="symbol"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:apply-templates select="symbol-entries"/>
        </xsl:otherwise>
      </xsl:choose>
    </uncurriedSymbolEntry>
  </xsl:template> 
  
  <xsl:template match="symbol-entries">
    <xsl:apply-templates select="symbol"/>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qdp-uncurrying-proof">  
    <dpNonterminationProof>
      <dps>
        <rules>
          <xsl:apply-templates select="qdp"/>
        </rules>
      </dps>
      <trs>
        <xsl:apply-templates select="trs" />
      </trs>
      <xsl:call-template name="dpsNontermProofOrAssumption">
        <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
      </xsl:call-template>
    </dpNonterminationProof>
  </xsl:template>
  
    <!-- ****************************************************************************************
       **  Root Labeling FC 1
       ****************************************************************************************
-->

  <xsl:template mode="nonTerm" match="qdp-root-labeling-fc1-proof">
    <dpNonterminationProof>
      <xsl:choose>
        <xsl:when test="count(qdp-flat-cc-proof/flat-context/context) = 0">
          <dpRuleRemoval>
            <dps>
              <rules>
                <xsl:apply-templates select="qdp" />
              </rules>
            </dps>
            <trs>
              <xsl:apply-templates select="trs" />
            </trs>
            <xsl:call-template name="dpsNontermProofOrAssumption">
              <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
            </xsl:call-template>            
          </dpRuleRemoval>
        </xsl:when>
        <xsl:otherwise>
          <dpRuleRemoval>
            <dps>
              <rules>
                <xsl:apply-templates select="qdp-flat-cc-proof/qdp" />
               </rules>
            </dps>
            <trs>
              <xsl:apply-templates select="qdp-flat-cc-proof/trs" />
            </trs>
            <dpNonterminationProof>
              <dpRuleRemoval>
                <dps>
                  <rules>
                    <xsl:apply-templates select="qdp" />
                  </rules>
                </dps>
                <trs>
                  <xsl:apply-templates select="trs" />
                </trs>
                <xsl:call-template name="dpsNontermProofOrAssumption">
                  <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
                </xsl:call-template>
              </dpRuleRemoval>
            </dpNonterminationProof>
          </dpRuleRemoval>
        </xsl:otherwise>
      </xsl:choose>
    </dpNonterminationProof>
  </xsl:template>
  
  <xsl:template match="qdp-root-labeling-fc1-proof">
    <dpProof>
      <xsl:choose>
        <xsl:when test="count(qdp-flat-cc-proof/flat-context/context) = 0">
          <semlabProc>
            <model>
              <rootLabeling/>
            </model>
            <dps>
              <rules>
                <xsl:apply-templates select="qdp" />
              </rules>
            </dps>
            <trs>
              <xsl:apply-templates select="trs" />
            </trs>
            <xsl:call-template name="dpsProofOrAssumption">
              <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
            </xsl:call-template>
          </semlabProc>
        </xsl:when>
        <xsl:otherwise>
          <flatContextClosureProc>
            <freshSymbol>
              <xsl:apply-templates select="qdp-flat-cc-proof/symbol"/>
            </freshSymbol>
            <flatContexts>
              <xsl:apply-templates select="qdp-flat-cc-proof/flat-context/context" />
            </flatContexts>
            <dps>
              <rules>
                <xsl:apply-templates select="qdp-flat-cc-proof/qdp" />
               </rules>
            </dps>
            <trs>
              <xsl:apply-templates select="qdp-flat-cc-proof/trs" />
            </trs>
            <dpProof>
              <semlabProc>
                <model>
                  <rootLabeling>
                    <xsl:apply-templates select="qdp-flat-cc-proof/symbol"/>
                  </rootLabeling>
                </model>
                <dps>
                  <rules>
                    <xsl:apply-templates select="qdp" />
                  </rules>
                </dps>
                <trs>
                  <xsl:apply-templates select="trs" />
                </trs>
                <xsl:call-template name="dpsProofOrAssumption">
                  <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
                </xsl:call-template>
              </semlabProc>
            </dpProof>
          </flatContextClosureProc>
        </xsl:otherwise>
      </xsl:choose>
    </dpProof>
  </xsl:template>
  
   <!-- ****************************************************************************************
       **  Bounding
       ****************************************************************************************
-->

  <xsl:template match="qtrs-bound-proof">
    <trsTerminationProof>
      <bounds>
        <type>
          <xsl:choose>
            <xsl:when test="bound-type/@match = 'true'">
              <match/>
            </xsl:when>
            <xsl:otherwise>
              <roof/>
            </xsl:otherwise>
          </xsl:choose>
        </type>
        <bound>
          <xsl:value-of select="./@bound"/> 
        </bound>
        <finalStates>
          <xsl:apply-templates select="tree-automaton/final-states/state"/>
        </finalStates>
        <treeAutomaton>
          <finalStates>
            <xsl:apply-templates select="tree-automaton/final-states/state"/>
          </finalStates>
          <transitions>
            <xsl:apply-templates select="tree-automaton/transition"/>
          </transitions>
        </treeAutomaton>
        <xsl:call-template name="trsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </bounds>
    </trsTerminationProof>
  </xsl:template>
  
  <xsl:template match="state"> 
    <state>
      <xsl:value-of select="./@value"/>
    </state>
  </xsl:template>
  
  <xsl:template match="transition">
    <transition>
      <lhs>
        <xsl:apply-templates select="transition-lhs/symbol"/>
        <xsl:if test="count(transition-lhs/height) &gt; 0">
          <height>
            <xsl:value-of select="transition-lhs/height/@value"/>        
          </height>
        </xsl:if>
        <xsl:apply-templates select="transition-lhs/state"/>
      </lhs>
      <rhs>
        <xsl:apply-templates select="transition-rhs/state"/>
      </rhs>
    </transition>
  </xsl:template>

  <!-- ****************************************************************************************
    **  Split
    ****************************************************************************************
  -->
  <xsl:template match="qdp-split-proof">    
    <dpProof>
      <splitProc>
        <dps>
          <rules>
            <xsl:apply-templates select="dps" />
          </rules>
        </dps>
        <trs>                     
           <xsl:apply-templates select="trs" />          
        </trs>
        <xsl:for-each select="../../proof-obligation/conjunction/proof-obligation">
          <xsl:call-template name="dpsProofOrAssumption">
            <xsl:with-param name="proofObligation" select="."/>
          </xsl:call-template>
        </xsl:for-each>
      </splitProc>
    </dpProof>
  </xsl:template>
        

    <!-- ****************************************************************************************
       **  Semantic Labeling
       ****************************************************************************************
-->

  <xsl:template match="qtrs-semantic-labeling-proof">
    <trsTerminationProof>
      <semlab>
        <model>
          <xsl:apply-templates select="model"/>
        </model>
        <trs>
          <xsl:apply-templates select="trs" />
        </trs>        
        <xsl:call-template name="trsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>        
      </semlab>
    </trsTerminationProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qtrs-semantic-labeling-proof">
    <trsNonterminationProof>
      <semlab>
        <model>
          <xsl:apply-templates select="model"/>
        </model>
        <trs>
          <xsl:apply-templates select="trs" />
        </trs>
        <xsl:call-template name="trsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </semlab>
    </trsNonterminationProof>
  </xsl:template>

  <xsl:template match="qdp-semantic-labeling-proof">
    <dpProof>
      <semlabProc>
        <model>
          <xsl:apply-templates select="model"/>
        </model>
        <dps>
          <xsl:apply-templates select="trs[2]" />
        </dps>
        <trs>
          <xsl:apply-templates select="trs[1]" />
        </trs>
        <xsl:if test="count(qtermset) &gt; 0">
          <innermostLhss>
            <xsl:apply-templates select="qtermset"/>
          </innermostLhss>
        </xsl:if>
        <xsl:call-template name="dpsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </semlabProc>
    </dpProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qdp-semantic-labeling-proof">
    <dpNonterminationProof>
      <dpRuleRemoval>
        <dps>
          <xsl:apply-templates select="trs[2]" />
        </dps>
        <trs>
          <xsl:apply-templates select="trs[1]" />
        </trs>
        <xsl:call-template name="dpsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </dpRuleRemoval>
    </dpNonterminationProof>
  </xsl:template>
  
  <xsl:template match="qdp-semantic-labeling-proof2">
    <dpProof>
      <semlabProc>
        <model>
          <xsl:apply-templates select="model"/>
        </model>
        <dps>
          <xsl:apply-templates select="trs[2]" />
        </dps>
        <trs>
          <xsl:apply-templates select="trs[1]" />
        </trs>
        <!-- Please don't let it happen that semlab2 appers 2 times nested -->
        <xsl:call-template name="dpsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
        <!-- Here calling unlabeling should be stupid as we did nothing but labeling the problem -->
      </semlabProc>
    </dpProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qdp-semantic-labeling-proof2">
    <dpNonterminationProof>
      <dpRuleRemoval>
        <dps>
          <xsl:apply-templates select="trs[2]" />
        </dps>
        <trs>
          <xsl:apply-templates select="trs[1]" />
        </trs>
        <!-- Please don't let it happen that semlab2 appers 2 times nested -->
        <xsl:call-template name="dpsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
        <!-- Here calling unlabeling should be stupid as we did nothing but labeling the problem -->
      </dpRuleRemoval>
    </dpNonterminationProof>
  </xsl:template>
    
  <xsl:template match="model">
    <finiteModel>
      <carrierSize>
        <xsl:value-of select="../carrier-size/integer/@value"/> 
      </carrierSize>
      <xsl:if test="../@quasi = 'true'">
        <tupleOrder>
          <pointWise/>
        </tupleOrder>
      </xsl:if>
      <xsl:apply-templates select="interpret"/>
    </finiteModel>
  </xsl:template>
  
  <xsl:template match="interpret">
    <interpret>
      <xsl:apply-templates select="symbol"/>
      <xsl:apply-templates select="labeledSymbol"/>
      <arity>
        <xsl:choose>
          <xsl:when test="count(labeledSymbol) = 0">
            <xsl:value-of select="symbol/@arity"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:value-of select="labeledSymbol/@arity"/>
          </xsl:otherwise>
        </xsl:choose>
      </arity>
      <!-- Here all arith functions can be plugged in -->
      <xsl:apply-templates mode="semlab" select="polynomial"/>
    </interpret>
  </xsl:template>

  <xsl:template mode="semlab" match="polynomial">
    <xsl:choose>
      <xsl:when test="count(monomial) = 0">
        <arithFunction>
          <natural>
            <xsl:value-of select="integer/@value" />
          </natural>
        </arithFunction>
      </xsl:when>
      <xsl:when test="count(monomial) = 1">
        <xsl:apply-templates mode="semlab" select="monomial"/>
      </xsl:when>
      <xsl:otherwise>
        <arithFunction>
          <sum>
            <xsl:apply-templates mode="semlab" select="monomial"/>
          </sum>
        </arithFunction>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template mode="semlab" match="monomial">
    <xsl:choose>
      <xsl:when test="count(polo-factor) = 0">
        <arithFunction>
          <natural>
            <xsl:value-of select="integer/@value" />
          </natural>
        </arithFunction>
      </xsl:when>
      <xsl:when test="count(polo-factor) = 1">
        <xsl:choose>
          <xsl:when test="integer/@value &gt; 1">
            <arithFunction>
              <product>
                <!-- just the one polo factor with natural before -->
                <xsl:apply-templates mode="semlab"
                  select="." />
              </product>
            </arithFunction>
          </xsl:when>
          <xsl:otherwise>
            <!-- just the one polo factor and no natural before -->
            <xsl:call-template name="polo-factors-semlab">
              <xsl:with-param name="monom" select="." />
            </xsl:call-template>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <arithFunction>
          <product>
            <!-- more than 1 polo factor -->
            <xsl:choose>
              <xsl:when test="integer/@value &gt; 1">
                <arithFunction>
                  <natural>
                    <xsl:value-of select="integer/@value" />
                  </natural>
                </arithFunction>
                <xsl:call-template name="polo-factors-semlab">
                  <xsl:with-param name="monom" select="." />
                </xsl:call-template>
              </xsl:when>
              <xsl:otherwise>
                <xsl:call-template name="polo-factors-semlab">
                  <xsl:with-param name="monom" select="." />
                </xsl:call-template>
              </xsl:otherwise>
            </xsl:choose>
          </product>
        </arithFunction>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template name="polo-factors-semlab">
    <xsl:param name="monom"/>
    <xsl:param name="factorIndex" select="1"/>
    <xsl:call-template name="factor-semlab">
      <xsl:with-param name="var" select="$monom/polo-factor[$factorIndex]/variable"/>
    </xsl:call-template>
    <xsl:if test="count($monom/polo-factor) &gt; $factorIndex">
      <xsl:call-template name="polo-factors-semlab">
        <xsl:with-param name="monom" select="."/>
        <xsl:with-param name="factorIndex" select="$factorIndex + 1"/>
      </xsl:call-template>
    </xsl:if>
  </xsl:template>
  
  <xsl:template name="factor-semlab">
    <xsl:param name="var"/>
    <xsl:param name="index" select="0"/>
    <xsl:choose>
      <xsl:when test="concat('x_', $index) = $var/@name">
        <xsl:choose>
          <xsl:when test="count($var/../integer/@value) = 0">
            <xsl:call-template name="variable-semlab">
              <xsl:with-param name="iteration" select="1"/>
              <xsl:with-param name="index" select="$index"/>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:call-template name="variable-semlab">
              <xsl:with-param name="iteration" select="$var/../integer/@value"/>
              <xsl:with-param name="index" select="$index"/>
            </xsl:call-template>
          </xsl:otherwise>
        </xsl:choose>      
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="factor-semlab">
          <xsl:with-param name="var" select="$var"/>
          <xsl:with-param name="index" select="$index + 1"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template name="variable-semlab">
    <xsl:param name="iteration" select="1"/>
    <xsl:param name="index"/>
    <xsl:if test="$iteration &gt; 0">
      <arithFunction>
        <variable>
          <xsl:value-of select="$index + 1"/>
        </variable>
      </arithFunction>
      <xsl:call-template name="variable-semlab">
        <xsl:with-param name="iteration" select="$iteration - 1"/>
        <xsl:with-param name="index" select="$index"/>
      </xsl:call-template>
    </xsl:if>  
  </xsl:template>

  <!--
    ****************************************************************************************
    ** Flat Context Closure
    ****************************************************************************************
  -->

  <xsl:template match="qtrs-flat-cc-proof">
    <trsTerminationProof>
      <xsl:choose>
        <xsl:when test="count(flat-context/context) = 0">
          <xsl:call-template name="trsProofOrAssumption">
            <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
          <flatContextClosure>
            <flatContexts>
              <xsl:apply-templates select="flat-context/context" />
            </flatContexts>
            <trs>
              <xsl:apply-templates select="trs" />
            </trs>
            <xsl:call-template name="trsProofOrAssumption">
              <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
            </xsl:call-template>
          </flatContextClosure>
        </xsl:otherwise>
      </xsl:choose>
    </trsTerminationProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qtrs-flat-cc-proof">
    <trsNonterminationProof>
      <xsl:choose>
        <xsl:when test="count(flat-context/context) = 0">
          <xsl:call-template name="trsNontermProofOrAssumption">
            <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
          <flatContextClosure>
            <flatContexts>
              <xsl:apply-templates select="flat-context/context" />
            </flatContexts>
            <trs>
              <xsl:apply-templates select="trs" />
            </trs>
            <xsl:call-template name="trsNontermProofOrAssumption">
              <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
            </xsl:call-template>
          </flatContextClosure>
        </xsl:otherwise>
      </xsl:choose>
    </trsNonterminationProof>
  </xsl:template>

  <!-- ****************************************************************************************
       **  Path Order
       ****************************************************************************************
-->

  <xsl:template match="path-order">
    <pathOrder>
      <statusPrecedence>
        <xsl:apply-templates select="statusMap/status"/>
      </statusPrecedence>
      <xsl:apply-templates select="afs"/>
    </pathOrder>
  </xsl:template>

  <xsl:template match="status">
    <statusPrecedenceEntry>
      <xsl:apply-templates select="symbol"/>
      <xsl:apply-templates select="labeledSymbol"/>
      <arity>
        <xsl:choose>
          <xsl:when test="count(labeledSymbol) = 0">
            <xsl:value-of select="symbol/@arity"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:value-of select="labeledSymbol/@arity"/>
          </xsl:otherwise>
        </xsl:choose>
      </arity>
      <precedence>
        <xsl:value-of select="prec/integer/@value"/>
      </precedence>
      <xsl:choose>
        <xsl:when test="count(multiset) = 1">
          <mul/>
        </xsl:when>
        <xsl:otherwise><lex/></xsl:otherwise>
      </xsl:choose>
    </statusPrecedenceEntry>
  </xsl:template>

  <xsl:template match="afs">
    <argumentFilter>
      <xsl:apply-templates select="filter"/>
    </argumentFilter>
  </xsl:template>

  <xsl:template match="filter">
  <argumentFilterEntry>
    <xsl:apply-templates select="symbol"/>
    <xsl:apply-templates select="labeledSymbol"/>
    <arity>
        <xsl:choose>
          <xsl:when test="count(labeledSymbol) = 0">
            <xsl:value-of select="symbol/@arity"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:value-of select="labeledSymbol/@arity"/>
          </xsl:otherwise>
        </xsl:choose>
      </arity>
    <xsl:choose>
        <xsl:when test="@collapse = 'true'">
          <collapsing>
            <xsl:value-of select="collapse/integer/@value"/>
          </collapsing>
        </xsl:when>
        <xsl:otherwise>
          <nonCollapsing>
            <xsl:apply-templates select="arg"/>
          </nonCollapsing>
        </xsl:otherwise>
      </xsl:choose>
    </argumentFilterEntry>
  </xsl:template>
  
  <xsl:template match="arg">
    <position>
      <xsl:apply-templates/>
    </position>
  </xsl:template>

  <xsl:template match="position">
    <xsl:choose>
      <xsl:when test="@value='true'">
        <xsl:text>true</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>false</xsl:text>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <!-- ****************************************************************************************
       **  EMB order as path order
       ****************************************************************************************
-->
       
  <xsl:template match="emb-order">
    <pathOrder>
      <statusPrecedence>
        <xsl:call-template name="symbolsToPrec">
          <xsl:with-param name="list" select="function-symbols"/>
          <xsl:with-param name="count" select="count(function-symbols/symbol)"/>
        </xsl:call-template>
      </statusPrecedence>
      <xsl:apply-templates select="afs"/>
    </pathOrder>
  </xsl:template>
  
  <xsl:template name="symbolsToPrec">
    <xsl:param name="list"/>
    <xsl:param name="count"/>
    <xsl:param name="i" select="1"/>
    <xsl:if test="$i &lt;= $count">
      <statusPrecedenceEntry>
        <xsl:apply-templates select="$list/symbol[$i]"/>
        <xsl:apply-templates select="$list/labeledSymbol[$i]"/>
        <arity>
          <xsl:choose>
            <xsl:when test="count($list/labeledSymbol[$i]) = 0">
              <xsl:value-of select="$list/symbol[$i]/@arity"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:value-of select="$list/labeledSymbol[$i]/@arity"/>
            </xsl:otherwise>
          </xsl:choose>
        </arity>
        <precedence>0</precedence>
        <lex/>
      </statusPrecedenceEntry>      
      <xsl:call-template name="symbolsToPrec">
        <xsl:with-param name="list" select="$list"/>
        <xsl:with-param name="count" select="$count"/>
        <xsl:with-param name="i" select="$i+1"/>
      </xsl:call-template>
    </xsl:if>
  </xsl:template>

  <!-- ****************************************************************************************
       **  Dependency graph proof
       ****************************************************************************************
-->

  <xsl:template match="qdp-dependency-graph-proof">
    <!-- We try to avoid depGraph after semlab yet, so don't regard it here
     -->
    <dpProof>
      <depGraphProc>
        <xsl:choose>
          <xsl:when test="count(graph-scc) = 0">
            <xsl:text />
          </xsl:when>
          <xsl:when test="count(graph-scc) = 1">
            <xsl:call-template name="scc">
              <xsl:with-param name="sccProposition"
                select="../../proof-obligation/proposition" />
              <xsl:with-param name="graph-scc" select="graph-scc" />
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:call-template name="sccList">
              <xsl:with-param name="proofTag" select="." />
            </xsl:call-template>
          </xsl:otherwise>
        </xsl:choose>
      </depGraphProc>
    </dpProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qdp-dependency-graph-proof">
    <!-- We try to avoid depGraph after semlab yet, so don't regard it here
    -->
    <xsl:choose>
      <xsl:when test = "count(../../proof-obligation/proposition) &gt; 0">
        <dpNonterminationProof>
          <dpRuleRemoval>
            <dps>
              <rules>
                <xsl:apply-templates select="../../proof-obligation/proposition/basic-obligation/qdp-termination-obligation/qdp/dps"/>
              </rules>
            </dps>
            <xsl:call-template name="dpsNontermProofOrAssumption">
              <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
            </xsl:call-template>
          </dpRuleRemoval>
        </dpNonterminationProof>      
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="findOneNontermProof">
          <xsl:with-param name="conjuncture" select="../../proof-obligation/conjunction"/>
          <xsl:with-param name="index" select="1"/>
        </xsl:call-template>
        <xsl:call-template name="dpsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <!-- Okay, the reason for having a rule removal proof whilst having a conjunction is, 
       that the dpgraph is more or less nothing more than a rule removal technique 
       for non terminating systems, thus we have to find the one non terminating proof 
       and use only the needed dps for the proof itself -->
  <xsl:template name="findOneNontermProof">
    <xsl:param name="conjuncture"/>
    <xsl:param name="index"/>
     <xsl:choose>
       <xsl:when test="count($conjuncture/proof-obligation[$index]//qdp-nontermination-proof) &gt; 0">
         <dpNonterminationProof>
           <dpRuleRemoval>
             <dps>
               <rules>
                 <xsl:apply-templates select="$conjuncture/proof-obligation[$index]/proposition/basic-obligation//dps"/>
               </rules>               
             </dps>
             <xsl:call-template name="dpsNontermProofOrAssumption">
               <xsl:with-param name="proofObligation" select="$conjuncture/proof-obligation[$index]"/>
             </xsl:call-template>             
           </dpRuleRemoval>
         </dpNonterminationProof>               
      </xsl:when>
      <xsl:when test="count($conjuncture/proof-obligation[$index]//qdp-nonloop-proof) &gt; 0">
        <xsl:call-template name="dpsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="$conjuncture/proof-obligation[$index]"/>
        </xsl:call-template>             
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="findOneNontermProof">
          <xsl:with-param name="conjuncture" select="$conjuncture"/>
          <xsl:with-param name="index" select="$index + 1"/>
        </xsl:call-template>    
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="scc">
    <xsl:param name="sccProposition"/>
    <xsl:param name="graph-scc"/>
    <xsl:param name="nonterm" select="false()"/>
    <component>
      <dps>
        <rules>
          <xsl:apply-templates select="$sccProposition/basic-obligation/qdp-termination-obligation/qdp/dps/rule"/>
        </rules>
      </dps>
      <realScc>
        <xsl:text>true</xsl:text>
      </realScc>
      <xsl:if test="count($graph-scc/identifier) &gt; 0">
        <arcs>
          <xsl:call-template name="forwardArcs">
            <xsl:with-param name="scc" select="$graph-scc"/>
            <xsl:with-param name="index" select="1"/>
          </xsl:call-template>
        </arcs>
      </xsl:if>
      <xsl:choose>
        <xsl:when test="$nonterm">
          <xsl:apply-templates mode="nonTerm" select="$sccProposition/proof"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:apply-templates select="$sccProposition/proof"/>            
        </xsl:otherwise>
      </xsl:choose>
    </component>
  </xsl:template>
  
  <xsl:template name="forwardArcs">
    <xsl:param name="scc"/>
    <xsl:param name="index" select="1"/>
    <forwardArc>
      <xsl:value-of select="$scc/identifier[$index]/@name"/>
    </forwardArc>
    <xsl:if test="count($scc/identifier) &gt; $index">
      <xsl:call-template name="forwardArcs">
        <xsl:with-param name="scc" select="$scc"/>
        <xsl:with-param name="index" select="$index + 1"/>
      </xsl:call-template>
    </xsl:if>
  </xsl:template>

  <!-- if the scc's have to be in an order other way round 
  <xsl:template name="sccList">
    <xsl:param name="proofTag"/>
    <xsl:param name="i" select="1"/>
    <xsl:param name="nonterm" select="false()"/>
    <xsl:call-template name="scc">
      <xsl:with-param name="sccProposition" select="$proofTag/../../proof-obligation/conjunction/proof-obligation[$i]/proposition"/>
      <xsl:with-param name="graph-scc" select="$proofTag/graph-scc[$i]"/>
      <xsl:with-param name="nonterm" select="$nonterm"/>
    </xsl:call-template>
    <xsl:choose>
      <xsl:when test="$i &lt; count($proofTag/../../proof-obligation/conjunction/proof-obligation)">
        <xsl:call-template name="sccList">
          <xsl:with-param name="proofTag" select="$proofTag"/>
          <xsl:with-param name="i" select="$i + 1"/>
          <xsl:with-param name="nonterm" select="$nonterm"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  -->

  <xsl:template name="sccList">
    <xsl:param name="proofTag"/>
    <xsl:param name="i" select="count($proofTag/graph-scc)"/>
    <xsl:param name="nonterm" select="false()"/>
    <xsl:param name="seenNonSCCs" select="0"/>
    <xsl:variable name="howMany" select="$proofTag/non-scc/@value"/>
    <xsl:choose>
      <xsl:when test="count($proofTag/graph-scc[$i]/non-scc) &gt; 0">
        <component>
          <dps>
            <rules>
              <xsl:apply-templates select="$proofTag/graph-scc[$i]/rule"/>
            </rules>
          </dps>
          <realScc>
            <xsl:text>false</xsl:text>
          </realScc>
          <xsl:if test="count($proofTag/graph-scc[$i]/identifier) &gt; 0">
            <arcs>
              <xsl:call-template name="forwardArcs">
                <xsl:with-param name="scc" select="$proofTag/graph-scc[$i]"/>
                <xsl:with-param name="index" select="1"/>
              </xsl:call-template>
            </arcs>
          </xsl:if>
        </component>
        <xsl:if test="$i &gt; 1">
          <xsl:call-template name="sccList">
            <xsl:with-param name="proofTag" select="$proofTag"/>
            <xsl:with-param name="i" select="$i - 1"/>
            <xsl:with-param name="nonterm" select="$nonterm"/>
            <xsl:with-param name="seenNonSCCs" select="$seenNonSCCs + 1"/>
          </xsl:call-template>
        </xsl:if>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="count($proofTag/../../proof-obligation/conjunction) &gt; 0">
            <xsl:call-template name="scc">
              <xsl:with-param name="sccProposition" select="$proofTag/../../proof-obligation/conjunction/proof-obligation[$i - $howMany + $seenNonSCCs]/proposition"/>
              <xsl:with-param name="graph-scc" select="$proofTag/graph-scc[$i]"/>
              <xsl:with-param name="nonterm" select="$nonterm"/>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:call-template name="scc">
              <xsl:with-param name="sccProposition" select="$proofTag/../../proof-obligation/proposition"/>
              <xsl:with-param name="graph-scc" select="$proofTag/graph-scc[$i]"/>
              <xsl:with-param name="nonterm" select="$nonterm"/>
            </xsl:call-template>
          </xsl:otherwise>
        </xsl:choose>
        <xsl:if test="$i &gt; 1">
          <xsl:call-template name="sccList">
            <xsl:with-param name="proofTag" select="$proofTag"/>
            <xsl:with-param name="i" select="$i - 1"/>
            <xsl:with-param name="nonterm" select="$nonterm"/>
            <xsl:with-param name="seenNonSCCs" select="$seenNonSCCs"/>
          </xsl:call-template>
        </xsl:if>
      </xsl:otherwise>    
    </xsl:choose>
  </xsl:template>

  <!-- ****************************************************************************************
    **  Q-Reduction Proof
    ****************************************************************************************
  -->
  
  <xsl:template match="qdp-q-reduction-proof">
    <dpProof>
      <innermostLhssRemovalProc>
        <innermostLhss>
          <xsl:apply-templates select="qtermset" />
        </innermostLhss>
        <xsl:call-template name="dpsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </innermostLhssRemovalProc>
    </dpProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qdp-q-reduction-proof">
    <dpNonterminationProof>
      <innermostLhssRemovalProc>
        <innermostLhss>
          <xsl:apply-templates select="qtermset" />
        </innermostLhss>
        <xsl:call-template name="dpsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </innermostLhssRemovalProc>
    </dpNonterminationProof>
  </xsl:template>
  

  <!-- ****************************************************************************************
    **  Subterm proof
    ****************************************************************************************
-->

  <xsl:template match="qdp-subterm-proof">
    <dpProof>
      <subtermProc>
        <xsl:apply-templates select="afs" />
        <dps>
          <xsl:apply-templates select="trs[2]" />
        </dps>
        <xsl:call-template name="dpsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </subtermProc>
    </dpProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qdp-subterm-proof">
    <dpNonterminationProof>
      <dpRuleRemoval>
        <dps>
          <xsl:apply-templates select="trs[2]" />
        </dps>
        <xsl:call-template name="dpsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </dpRuleRemoval>
    </dpNonterminationProof>
  </xsl:template>
  
  <!-- ****************************************************************************************
    **  SizeChange proof 
    ****************************************************************************************
-->

  <xsl:template match="qdp-size-change-proof">
    <dpProof>
      <sizeChangeProc>
        <xsl:choose>
          <xsl:when test="count(subterm-criterion) &gt; 0">
            <subtermCriterion />
          </xsl:when>
          <xsl:otherwise>
            <reductionPair>
              <orderingConstraintProof>
                <redPair>
                  <xsl:apply-templates select="qdp-reduction-pair-proof/order" />
                </redPair>
              </orderingConstraintProof>
              <usableRules>
                <xsl:apply-templates select="qdp-reduction-pair-proof/trs[1]" />
              </usableRules>
            </reductionPair>
          </xsl:otherwise>
        </xsl:choose>
        <xsl:call-template name="sizeChangeGraphs">
          <xsl:with-param name="scTag" select="." />
        </xsl:call-template>
      </sizeChangeProc>
    </dpProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qdp-size-change-proof">
    <dpNonterminationProof>
      <ruleRemoval>
        <notYetSupported/>
      </ruleRemoval>
    </dpNonterminationProof>
  </xsl:template>
  
  <xsl:template name="sizeChangeGraphs">
    <xsl:param name="scTag"/>
    <xsl:param name="i" select="1"/>
    <xsl:if test="count($scTag/qdp-size-change-graph) &gt;= $i">
      <xsl:call-template name="sizeChangeGraph">
        <xsl:with-param name="graph" select="$scTag/qdp-size-change-graph[$i]"/>
      </xsl:call-template>
      <xsl:call-template name="sizeChangeGraphs">
        <xsl:with-param name="scTag" select="$scTag"/>
        <xsl:with-param name="i" select="$i+1"/>        
      </xsl:call-template>
    </xsl:if>
  </xsl:template>
  
  <xsl:template name="sizeChangeGraph">
    <xsl:param name="graph"/>
    <sizeChangeGraph>
      <xsl:apply-templates select="$graph/rule"/>
      <xsl:call-template name="sizeChangeEdges">
        <xsl:with-param name="graph" select="$graph"/>
      </xsl:call-template>
    </sizeChangeGraph>
  </xsl:template>
  
  <xsl:template name="sizeChangeEdges">
    <xsl:param name="graph"/>
    <xsl:param name="i" select="1"/>
    <xsl:if test="count($graph/edge) &gt;= $i">
      <edge>
        <position>
          <xsl:value-of select="$graph/edge[$i]/position[1]/@value"/>
        </position>
        <strict>
          <xsl:choose>
            <xsl:when test="$graph/edge[$i]/@strict='true'">true</xsl:when>
            <xsl:otherwise>false</xsl:otherwise>
          </xsl:choose>
        </strict>
        <position>
          <xsl:value-of select="$graph/edge[$i]/position[2]/@value"/>
        </position>
      </edge>
      <xsl:call-template name="sizeChangeEdges">
        <xsl:with-param name="graph" select="$graph"/>
        <xsl:with-param name="i" select="$i+1"/>
      </xsl:call-template>
    </xsl:if> 
  </xsl:template>
  
  <!-- ****************************************************************************************
    **  SCNP
    ****************************************************************************************
-->
  <xsl:template match="scnp-status">
    <status>
      <xsl:if test="@type='MAX'">
        <max/>
      </xsl:if>
      <xsl:if test="@type='MIN'">
        <min/>
      </xsl:if>
      <xsl:if test="@type='MS'">
        <ms/>
      </xsl:if>
      <xsl:if test="@type='DMS'">
        <dms/>
      </xsl:if>
    </status>
  </xsl:template>
  
  <xsl:template match="scnp-level-mapping">
    <levelMapping>
      <xsl:apply-templates select="level-mapping-entry"/>
    </levelMapping>
  </xsl:template>
  
  <xsl:template match="level-mapping-entry">
    <levelMappingEntry>
      <xsl:apply-templates select="symbol"/>
      <xsl:apply-templates select="labeledSymbol"/>
      <arity>
        <xsl:choose>
          <xsl:when test="count(labeledSymbol) = 0">
            <xsl:value-of select="symbol/@arity"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:value-of select="labeledSymbol/@arity"/>
          </xsl:otherwise>
        </xsl:choose>
      </arity>
      <xsl:apply-templates select="position-level-entry"/>
    </levelMappingEntry>
  </xsl:template>
  
  <xsl:template match="position-level-entry">
    <positionLevelEntry>
      <position>
        <xsl:value-of select="position/@value"/>
      </position>
      <level>
        <xsl:value-of select="level/@value"/>
      </level>
    </positionLevelEntry>
  </xsl:template>
  

  <!-- ****************************************************************************************
    **  text-proof
    ****************************************************************************************
  -->  
  <xsl:template match="text-proof">
    <dpProof>
      <!--
      <unknownProof>
        <text>
          <xsl:apply-templates />
        </text>
        <xsl:apply-templates select="../../proof-obligation/proposition/proof" />        
        </unknownProof> -->
      <pIsEmpty/>
    </dpProof>    
  </xsl:template>

  <!-- ****************************************************************************************
    **  narrowing processor
    ****************************************************************************************
  -->  
  <xsl:template match="narrowing-proof">
    <dpProof>
      <narrowingProc>
        <xsl:apply-templates select="rule"/>
        <xsl:apply-templates mode="positionInTerm" select="position"/>
        <narrowings>
          <rules>
            <xsl:apply-templates select="dps" />
           </rules>
        </narrowings>
        <xsl:call-template name="dpsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </narrowingProc>
    </dpProof>
  </xsl:template>

  <xsl:template mode="nonTerm" match="narrowing-proof">
    <dpNonterminationProof>
      <narrowingProc>
        <xsl:apply-templates select="rule"/>
        <xsl:apply-templates mode="positionInTerm" select="position"/>
        <narrowings>
          <rules>
            <xsl:apply-templates select="dps" />
          </rules>
        </narrowings>
        <xsl:call-template name="dpsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </narrowingProc>
    </dpNonterminationProof>
  </xsl:template>
  
  <!-- ****************************************************************************************
    **  instantiation processor
    ****************************************************************************************
  -->  
  <xsl:template match="instantiation-proof">
    <dpProof>
      <instantiationProc>
        <xsl:apply-templates select="rule"/>
        <instantiations>
          <rules>
            <xsl:apply-templates select="dps[1]" />
          </rules>
        </instantiations>
        <xsl:call-template name="dpsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </instantiationProc>
    </dpProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="instantiation-proof">
    <dpNonterminationProof>
      <instantiationProc>
        <dps>
          <rules>
            <xsl:apply-templates select="dps[2]" />
          </rules>
        </dps>
        <xsl:call-template name="dpsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </instantiationProc>
    </dpNonterminationProof>
  </xsl:template>

  <!-- ****************************************************************************************
    **  forward instantiation processor
    ****************************************************************************************
  -->  
  <xsl:template match="forward-instantiation-proof">
    <dpProof>
      <forwardInstantiationProc>
        <xsl:apply-templates select="rule"/>
        <instantiations>
          <rules>
            <xsl:apply-templates select="dps[1]" />
          </rules>
        </instantiations>
        <xsl:if test="trs">
          <usableRules>
            <xsl:apply-templates select="trs" />
          </usableRules>  
        </xsl:if>
        <xsl:call-template name="dpsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </forwardInstantiationProc>
    </dpProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="forward-instantiation-proof">
    <dpNonterminationProof>
      <instantiationProc>
        <dps>
          <rules>
            <xsl:apply-templates select="dps[2]" />
          </rules>
        </dps>
        <xsl:call-template name="dpsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </instantiationProc>
    </dpNonterminationProof>
  </xsl:template>
  

  <!-- ****************************************************************************************
    **  rewriting processor
    ****************************************************************************************
  -->  
  <xsl:template match="rewriting-proof">
    <dpProof>
      <rewritingProc>
        <xsl:apply-templates select="rule[1]"/>
        <rewriteStep>
          <xsl:apply-templates mode="positionInTerm" select="position"/>
          <xsl:apply-templates select="rule[2]"/>
          <xsl:apply-templates select="dps[1]/rule/term[2]"/>
        </rewriteStep>
        <xsl:apply-templates select="dps[2]/rule"/>
        <usableRules>
            <xsl:apply-templates select="trs" />
        </usableRules>  
        <xsl:call-template name="dpsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </rewritingProc>
    </dpProof>
  </xsl:template>

  <xsl:template mode="nonTerm" match="rewriting-proof">
    <dpNonterminationProof>
      <rewritingProc>
        <xsl:apply-templates select="rule[1]"/>
        <rewriteStep>
          <xsl:apply-templates mode="positionInTerm" select="position"/>
          <xsl:apply-templates select="rule[2]"/>
          <xsl:apply-templates select="dps[1]/rule/term[2]"/>
        </rewriteStep>
        <xsl:apply-templates select="dps[2]/rule"/>
        <usableRules>
          <xsl:apply-templates select="trs" />
        </usableRules>  
        <xsl:call-template name="dpsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </rewritingProc>
    </dpNonterminationProof>
  </xsl:template>
  
  <!-- ****************************************************************************************
    **  Complex Constant Removal processor
    ****************************************************************************************
  -->  
  <xsl:template match="qdp-complex-constant-removal-proof">
    <dpProof>
      <complexConstantRemovalProc>        
        <xsl:apply-templates select="*[1]" />
        <ruleMap>
          <xsl:for-each select="ruleMap/ruleMapEntry">
            <ruleMapEntry>
              <xsl:apply-templates select="*[1]"/>
              <xsl:apply-templates select="*[2]"/>
            </ruleMapEntry>
          </xsl:for-each>
        </ruleMap>
        <xsl:call-template name="dpsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </complexConstantRemovalProc>
    </dpProof>
  </xsl:template>
  
  
  <!-- ****************************************************************************************
    **  Usable rules processor
    ****************************************************************************************
  -->  
  <xsl:template match="qdp-usable-rules-proof">
    <dpProof>
      <usableRulesProc>
        <usableRules>
          <xsl:apply-templates select="trs[1]" />
        </usableRules>
        <xsl:call-template name="dpsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </usableRulesProc>
    </dpProof>
  </xsl:template>

  <xsl:template match="qdp-usable-rules-proof" mode="nonTerm">
    <dpNonterminationProof>
      <dpRuleRemoval>
        <xsl:choose>
          <xsl:when test="count(trs/rule) &gt; 0">
            <trs>
              <xsl:apply-templates select="trs[1]" />
            </trs>
          </xsl:when>
          <xsl:otherwise>
            <trs>
              <rules/>
            </trs>
          </xsl:otherwise>
        </xsl:choose>
        <xsl:call-template name="dpsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>        
      </dpRuleRemoval>    
    </dpNonterminationProof>
  </xsl:template>
  
  <!-- ****************************************************************************************
    **  Monotonic reduction pair with usable rules proof
    ****************************************************************************************
-->

  <xsl:template match="qdp-mono-reduction-pair-ur-proof">
    <dpProof>
      <monoRedPairUrProc>
        <orderingConstraintProof>
          <redPair>
            <xsl:apply-templates select="*[4]" />
          </redPair>
        </orderingConstraintProof>
        <dps>
          <xsl:apply-templates select="trs[1]" />
        </dps>
        <trs>
          <xsl:apply-templates select="trs[2]" />
        </trs>
        <usableRules>
          <xsl:apply-templates select="trs[3]" />
        </usableRules>
        <xsl:call-template name="dpsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </monoRedPairUrProc>
    </dpProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qdp-mono-reduction-pair-ur-proof">
    <dpNonterminationProof>
      <dpRuleRemoval>
        <dps>
          <xsl:apply-templates select="trs[1]" />
        </dps>
        <trs>
          <xsl:apply-templates select="trs[2]" />
        </trs>
        <xsl:call-template name="dpsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </dpRuleRemoval>
    </dpNonterminationProof>
  </xsl:template>
  
  <!-- ****************************************************************************************
       **  Reduction pair proof
       ****************************************************************************************
-->

  <xsl:template match="qdp-reduction-pair-proof">
    <dpProof>
      <xsl:choose>
        <!-- Test if the set of usable rules is equal to the set of the qdp -->
        <xsl:when
          test="count(trs[1]/rule) &lt; count(../../basic-obligation/qdp-termination-obligation/qdp/trs/rule)">
          <redPairUrProc>
            <orderingConstraintProof>
              <redPair>
                <xsl:choose>
                  <xsl:when test="count(scnp-order) &gt; 0">
                    <scnp>
                      <xsl:apply-templates select="scnp-order/scnp-status"/>
                      <xsl:apply-templates select="scnp-order/scnp-level-mapping"/>
                      <redPair>
                        <xsl:apply-templates select="order" />  
                      </redPair>
                    </scnp>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:apply-templates select="order" />
                  </xsl:otherwise>
                </xsl:choose>
              </redPair>
            </orderingConstraintProof>
            <dps>
              <xsl:apply-templates select="trs[3]" />
            </dps>
            <usableRules>
              <xsl:apply-templates select="trs[1]" />
            </usableRules>
            <xsl:call-template name="dpsProofOrAssumption">
              <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
            </xsl:call-template>
          </redPairUrProc>
        </xsl:when>
        <xsl:otherwise>
          <redPairProc>
            <orderingConstraintProof>
              <redPair>
                <xsl:choose>
                  <xsl:when test="count(scnp-order) &gt; 0">
                    <scnp>
                      <xsl:apply-templates select="scnp-order/scnp-status"/>
                      <xsl:apply-templates select="scnp-order/scnp-level-mapping"/>
                      <redPair>
                        <xsl:apply-templates select="order" />  
                      </redPair>
                    </scnp>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:apply-templates select="order" />
                  </xsl:otherwise>
                </xsl:choose>
              </redPair>
            </orderingConstraintProof>
            <dps>
              <xsl:apply-templates select="trs[3]" />
            </dps>
            <xsl:call-template name="dpsProofOrAssumption">
              <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
            </xsl:call-template>
          </redPairProc>
        </xsl:otherwise>
      </xsl:choose>
    </dpProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qdp-reduction-pair-proof">
    <dpNonterminationProof>
      <dpRuleRemoval>
        <dps>
          <xsl:apply-templates select="trs[3]"/>
        </dps>
        <xsl:call-template name="dpsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </dpRuleRemoval>
    </dpNonterminationProof>
  </xsl:template>  

  <xsl:template match="qdp-mono-reduction-pair-proof">
    <dpProof>
      <monoRedPairProc>
        <orderingConstraintProof>
          <redPair>
            <xsl:apply-templates select="order" />
          </redPair>
        </orderingConstraintProof>
        <dps>
          <xsl:apply-templates select="trs[1]" />
        </dps>
        <trs>
          <xsl:apply-templates select="trs[2]" />
        </trs>
        <xsl:call-template name="dpsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </monoRedPairProc>
    </dpProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qdp-mono-reduction-pair-proof">
    <dpNonterminationProof>
      <dpRuleRemoval>
        <dps>
          <xsl:apply-templates select="trs[1]" />
        </dps>
        <trs>
          <xsl:apply-templates select="trs[2]" />
        </trs>
        <xsl:call-template name="dpsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </dpRuleRemoval>
    </dpNonterminationProof>
  </xsl:template>
  
  <xsl:template match="qdp-bounded-increase-proof">
    <dpProof>
          <generalRedPairProc>
            <orderingConstraintProof>
              <redPair>
                  <xsl:apply-templates select="order" />
              </redPair>
            </orderingConstraintProof>
            <strict>
              <rules>
                <xsl:apply-templates select="dps[1]" />
              </rules>
            </strict>
            <bound>
              <rules>
                <xsl:apply-templates select="dps[2]" />
              </rules>
            </bound>
            <xsl:apply-templates select="bounded-increase-proof"/>
            <xsl:choose>
              <xsl:when test="../../proof-obligation/proposition/basic-obligation">
                <!-- 1 sub problem -->
                <xsl:call-template name="dpsProofOrAssumption">
                  <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
                </xsl:call-template>
              </xsl:when>
              <xsl:otherwise>
                <!-- two sub problems -->
                <xsl:call-template name="dpsProofOrAssumption">
                  <xsl:with-param name="proofObligation" select="../../proof-obligation/conjunction/proof-obligation"/>
                </xsl:call-template>                
              </xsl:otherwise>
            </xsl:choose>
          </generalRedPairProc>
    </dpProof>
  </xsl:template>
  
  <xsl:template match="bounded-increase-proof">
    <condRedPairProof>
      <xsl:apply-templates select="symbol"/>
      <before>
        <xsl:apply-templates select="before/text()"/>
      </before>
      <after>
        <xsl:apply-templates select="after/text()"/>
      </after>
      <conditions>
        <xsl:for-each select="conditions/condition">
          <condition>
            <xsl:apply-templates select="conditionalConstraint"/>
            <dpSequence>
              <rules>
                <xsl:apply-templates select="dps/*"/>
              </rules>
            </dpSequence>            
            <xsl:apply-templates select="conditionalConstraintProof"/>
          </condition>
        </xsl:for-each>
      </conditions>          
    </condRedPairProof>
  </xsl:template>
  
  <xsl:template match="conditionalConstraint">
    <conditionalConstraint>
      <xsl:apply-templates mode="cc"/>
    </conditionalConstraint>
  </xsl:template>
  
  <xsl:template match="conditionalConstraintProof">
    <conditionalConstraintProof>
      <xsl:apply-templates mode="cc"/>
    </conditionalConstraintProof>
  </xsl:template>
  
  <xsl:template match="final" mode="cc">
    <final/>
  </xsl:template>
  
  <xsl:template match="differentConstructor" mode="cc">
    <differentConstructor>
      <xsl:apply-templates/>
    </differentConstructor>
  </xsl:template>
  
  <xsl:template match="sameConstructor" mode="cc">
    <sameConstructor>
      <xsl:apply-templates/>
    </sameConstructor>
  </xsl:template>
  
  <xsl:template match="deleteCondition" mode="cc">
    <deleteCondition>
      <xsl:apply-templates/>
    </deleteCondition>
  </xsl:template>
  
  <xsl:template match="variableEquation" mode="cc">
    <variableEquation>
      <xsl:apply-templates/>
    </variableEquation>
  </xsl:template>
  
  <xsl:template match="simplifyCondition" mode="cc">
    <simplifyCondition>
      <xsl:apply-templates/>
    </simplifyCondition>
  </xsl:template>
  
  <xsl:template match="funargIntoVar" mode="cc">
    <funargIntoVar>
      <xsl:apply-templates select="*[1]"/>
      <position>
        <xsl:value-of select="position/text()"/>
      </position>
      <xsl:apply-templates select="*[3]"/>
      <xsl:apply-templates select="*[4]"/>
      <xsl:apply-templates select="*[5]"/>
    </funargIntoVar>
  </xsl:template>
  
  <xsl:template match="induction" mode="cc">
    <induction>
      <xsl:apply-templates select="*[1]"/>
      <conjuncts>
        <xsl:apply-templates select="conjuncts/*"/>
      </conjuncts>
      <ruleConstraintProofs>
        <xsl:for-each select="ruleConstraintProofs/*">
          <ruleConstraintProof>
            <xsl:apply-templates select="rule"/>
            <subtermVarEntries>
              <xsl:for-each select="subtermVarEntries/subtermVarEntry">
                <subtermVarEntry>
                  <xsl:apply-templates/>
                </subtermVarEntry>
              </xsl:for-each>
            </subtermVarEntries>
            <xsl:apply-templates select="conditionalConstraint"/>
            <xsl:apply-templates select="conditionalConstraintProof"/>
          </ruleConstraintProof>
        </xsl:for-each>        
      </ruleConstraintProofs>      
    </induction>
  </xsl:template>
  
  <xsl:template match="constraint" mode="cc">
    <constraint>
      <xsl:apply-templates select="*[1]"/>
      <xsl:copy-of select="*[2]" exclude-result-prefixes="#all"/>
      <xsl:apply-templates select="*[3]"/>
    </constraint>
  </xsl:template>
  
  <xsl:template mode="cc" match="implication">
    <implication>
      <xsl:apply-templates/>
    </implication>
  </xsl:template>

  <xsl:template mode="cc" match="all">
    <all>
      <xsl:apply-templates/>
    </all>
  </xsl:template>
  
  <!-- ****************************************************************************************
    **  Innermost switch proofs
    ****************************************************************************************
  -->
  
  <xsl:template match="qtrs-locally-confluent-overlay-proof">
    <trsTerminationProof>
      <switchInnermost>
        <wcrProof>
          <joinableCriticalPairsAuto/>
        </wcrProof>
        <xsl:call-template name="trsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </switchInnermost>
    </trsTerminationProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qtrs-locally-confluent-overlay-proof">
    <trsNonterminationProof>
      <innermostLhssIncrease>
        <innermostLhss>
          <xsl:apply-templates select="qtermset" />
        </innermostLhss>
        <xsl:call-template name="trsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </innermostLhssIncrease>
    </trsNonterminationProof>
  </xsl:template>
  
  <xsl:template match="qdp-mnoc-proof">
    <dpProof>
      <switchInnermostProc>
        <wcrProof>
          <joinableCriticalPairsAuto/>
        </wcrProof>
        <xsl:call-template name="dpsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
      </xsl:call-template>
      </switchInnermostProc>
    </dpProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qdp-mnoc-proof">
    <dpNonterminationProof>
      <innermostLhssIncreaseProc>
        <innermostLhss>
          <xsl:apply-templates select="qtermset" />
        </innermostLhss>        
        <xsl:call-template name="dpsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </innermostLhssIncreaseProc>
    </dpNonterminationProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qdp-reverse-mnoc-proof">
    <dpNonterminationProof>
      <switchFullStrategyProc>
        <wcrProof>
          <joinableCriticalPairsBFS><xsl:value-of select="text()"></xsl:value-of></joinableCriticalPairsBFS>
        </wcrProof>
        <xsl:call-template name="dpsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </switchFullStrategyProc>
    </dpNonterminationProof>
  </xsl:template>
  
  <!-- ****************************************************************************************
    **  S-is-empty proof
    ****************************************************************************************
  -->
  
  <xsl:template match="reltrs-empty-s-proof">
    <relativeTerminationProof>
      <sIsEmpty>
        <xsl:call-template name="trsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </sIsEmpty>
    </relativeTerminationProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="reltrs-empty-s-proof">
    <relativeNonterminationProof>      
      <xsl:call-template name="trsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>      
    </relativeNonterminationProof>
  </xsl:template>

  <!-- ****************************************************************************************
    **  clean S proof
    ****************************************************************************************
  -->
  
  <xsl:template match="reltrs-clean-proof">
    <relativeTerminationProof>
      <equalityRemoval>
        <xsl:call-template name="reltrsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </equalityRemoval>
    </relativeTerminationProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="reltrs-clean-proof">
    <relativeNonterminationProof>
      <ruleRemoval>
        <trs>          
          <xsl:apply-templates select="trs[1]"/>
        </trs>
        <trs>          
          <xsl:apply-templates select="trs[2]"/>
        </trs>        
        <xsl:call-template name="reltrsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </ruleRemoval>            
    </relativeNonterminationProof>
  </xsl:template>
  
  
  
  
  <!-- ****************************************************************************************
       **  Rule removal proof
       ****************************************************************************************
-->

  <xsl:template match="qtrs-rule-removal-proof">
    <trsTerminationProof>
      <ruleRemoval>
        <orderingConstraintProof>
          <redPair>
            <xsl:apply-templates select="order" />
          </redPair>
        </orderingConstraintProof>
        <trs>
          <!-- trs[2] are the REMAINING rules, that CPF wants to have -->
          <xsl:apply-templates select="trs[2]" />
        </trs>
        <xsl:call-template name="trsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </ruleRemoval>
    </trsTerminationProof>
  </xsl:template>
  
  <xsl:template match="qtrs-q-rule-removal-proof">
    <trsTerminationProof>
      <removeNonApplicableRules>
        <trs>
          <!-- trs[2] are the DELETED rules, that CPF wants to have -->
          <xsl:apply-templates select="trs[2]" />
        </trs>
        <xsl:call-template name="trsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </removeNonApplicableRules>
    </trsTerminationProof>
  </xsl:template>


  <xsl:template match="reltrs-rule-removal-proof">
    <relativeTerminationProof>
      <ruleRemoval>
        <orderingConstraintProof>
          <redPair>
            <xsl:apply-templates select="order" />
          </redPair>
        </orderingConstraintProof>
        <trs>
          <!-- trs[1] are the REMAINING R-rules, that CPF wants to have -->
          <xsl:apply-templates select="trs[1]" />
        </trs>
        <trs>
          <!-- trs[2] are the REMAINING S-rules, that CPF wants to have -->
          <xsl:apply-templates select="trs[2]" />
        </trs>
        <xsl:call-template name="reltrsProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </ruleRemoval>
    </relativeTerminationProof>
  </xsl:template>
  
  
    
  <xsl:template mode="nonTerm" match="qtrs-rule-removal-proof">
    <trsNonterminationProof>
      <ruleRemoval>
        <trs>
          <xsl:apply-templates select="trs[2]"/>
        </trs>
        <xsl:call-template name="trsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </ruleRemoval>
    </trsNonterminationProof>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qtrs-q-rule-removal-proof">
    <trsNonterminationProof>
      <ruleRemoval>
        <trs> <!-- trs[1] are remaining rules -->
          <xsl:apply-templates select="trs[1]"/>
        </trs>
        <xsl:call-template name="trsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </ruleRemoval>
    </trsNonterminationProof>
  </xsl:template>
  
  
  <xsl:template mode="nonTerm" match="reltrs-rule-removal-proof">
    <relativeNonterminationProof>
      <ruleRemoval>
        <trs>
          <xsl:apply-templates select="trs[1]"/>
        </trs>
        <trs>
          <xsl:apply-templates select="trs[2]"/>
        </trs>
        <xsl:call-template name="reltrsNontermProofOrAssumption">
          <xsl:with-param name="proofObligation" select="../../proof-obligation"/>
        </xsl:call-template>
      </ruleRemoval>
    </relativeNonterminationProof>
  </xsl:template>

  <!-- ****************************************************************************************
       **  Orders
       ****************************************************************************************
-->

  <xsl:template match="order">
    <xsl:apply-templates/>
  </xsl:template>

  <!-- ****************************************************************************************
       **  Polynomial Order
       ****************************************************************************************
-->

  <xsl:template match="polynomial-order">
    <interpretation>
      <type>
        <polynomial>
          <domain>
            <xsl:choose>
              <xsl:when test="count(polo-interpretation/polynomial/monomial/rational) &gt; 0">
                <rationals>
                  <delta>
                    <rational>
                      <numerator>
                        <xsl:value-of select="delta/rational/numerator/@value"/>
                      </numerator>
                      <denominator>
                        <xsl:value-of select="delta/rational/denominator/@value"/>
                      </denominator>
                    </rational>
                  </delta>
                </rationals>
              </xsl:when>
              <xsl:when test="count(../../../qdp-bounded-increase-proof) &gt; 0">
                <integers/>
              </xsl:when>
              <xsl:otherwise>
                <naturals/>
              </xsl:otherwise>
            </xsl:choose>
          </domain>
          <degree>
            <xsl:choose>
              <xsl:when test="count(degree) &gt; 0">
                <xsl:value-of select="degree/integer/@value" />              
              </xsl:when>
              <xsl:otherwise>
                <xsl:text>1</xsl:text>
              </xsl:otherwise>
            </xsl:choose>
          </degree>
        </polynomial>
      </type>
      <xsl:call-template name="polo-mappings">
        <xsl:with-param name="order" select="."/>
      </xsl:call-template>
    </interpretation>
  </xsl:template>

  <xsl:template match="neg-polynomial-order">
    <interpretation>
      <type>
        <polynomial>
          <domain>
            <xsl:choose>
              <xsl:when test="count(polo-interpretation/polynomial/monomial/rational) &gt; 0">
                <rationals>
                  <delta>
                    <rational>
                      <numerator>
                        <xsl:value-of select="delta/rational/numerator/@value"/>
                      </numerator>
                      <denominator>
                        <xsl:value-of select="delta/rational/denominator/@value"/>
                      </denominator>
                    </rational>
                  </delta>
                </rationals>
              </xsl:when>
              <xsl:otherwise>
                <naturals/>
              </xsl:otherwise>
            </xsl:choose>
          </domain>
          <degree>
            <xsl:choose>
              <xsl:when test="count(degree) &gt; 0">
                <xsl:value-of select="degree/integer/@value" />              
              </xsl:when>
              <xsl:otherwise>
                <xsl:text>1</xsl:text>
              </xsl:otherwise>
            </xsl:choose>
          </degree>
        </polynomial>
      </type>
      <xsl:call-template name="polo-mappings">
        <xsl:with-param name="order" select="."/>
      </xsl:call-template>
    </interpretation>
  </xsl:template>

  <xsl:template name="polo-mappings">
    <xsl:param name="order"/>
    <xsl:param name="i" select="1"/>
    <xsl:apply-templates select="$order/polo-interpretation[$i]"/>
    <xsl:choose>
      <xsl:when test="$i &lt; count($order/polo-interpretation)">
        <xsl:call-template name="polo-mappings">
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
    <interpret>
      <xsl:apply-templates select="symbol"/>
      <xsl:apply-templates select="labeledSymbol"/>
      <arity>
        <xsl:choose>
          <xsl:when test="count(labeledSymbol) = 0">
            <xsl:value-of select="symbol/@arity"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:value-of select="labeledSymbol/@arity"/>
          </xsl:otherwise>
        </xsl:choose>
      </arity>
      <xsl:apply-templates select="polynomial"/>
    </interpret>
  </xsl:template>

  <xsl:template match="polynomial">
    <polynomial>
      <sum>
        <xsl:choose>
          <xsl:when test="count(monomial)=0">
            <polynomial>
              <coefficient>
                <integer>0</integer>
              </coefficient>
            </polynomial>
          </xsl:when>
          <xsl:otherwise>
            <xsl:apply-templates select="monomial"/>
          </xsl:otherwise>
        </xsl:choose>
      </sum>
    </polynomial>
  </xsl:template>

  <xsl:template match="monomial">
    <polynomial>
      <xsl:choose>
        <xsl:when test="count(polo-factor) = 0">
          <coefficient>
            <xsl:choose>
              <xsl:when test="count(rational) &gt; 0">
                <rational>
                  <numerator>
                    <xsl:value-of select="rational/numerator/@value"/>
                  </numerator>
                  <denominator>
                    <xsl:value-of select="rational/denominator/@value"/>
                  </denominator>
                </rational>
              </xsl:when>
              <xsl:otherwise>
                <integer>
                  <xsl:value-of select="integer/@value"/>
                </integer>              
              </xsl:otherwise>
            </xsl:choose>
          </coefficient>
        </xsl:when>
        <xsl:otherwise>
          <product>
            <polynomial>
              <coefficient>
                <xsl:choose>
                  <xsl:when test="count(rational) &gt; 0">
                    <rational>
                      <numerator>
                        <xsl:value-of select="rational/numerator/@value"/>
                      </numerator>
                      <denominator>
                        <xsl:value-of select="rational/denominator/@value"/>
                      </denominator>
                    </rational>
                  </xsl:when>
                  <xsl:otherwise>
                    <integer>
                      <xsl:value-of select="integer/@value"/>
                    </integer>              
                  </xsl:otherwise>
                </xsl:choose>
              </coefficient>
            </polynomial>
            <xsl:call-template name="polo-factors">
              <xsl:with-param name="monom" select="."/>
            </xsl:call-template>
          </product>
        </xsl:otherwise>
      </xsl:choose>
    </polynomial>
  </xsl:template>

  <xsl:template name="polo-factors">
    <xsl:param name="monom"/>
    <xsl:param name="factorIndex" select="1"/>
    <xsl:call-template name="factor">
      <xsl:with-param name="var" select="$monom/polo-factor[$factorIndex]/variable"/>
    </xsl:call-template>
    <xsl:if test="count($monom/polo-factor) &gt; $factorIndex">
      <xsl:call-template name="polo-factors">
        <xsl:with-param name="monom" select="."/>
        <xsl:with-param name="factorIndex" select="$factorIndex + 1"/>
      </xsl:call-template>
    </xsl:if>
  </xsl:template>
  
  <xsl:template name="factor">
    <xsl:param name="var"/>
    <xsl:param name="index" select="1"/>
    <xsl:choose>
      <xsl:when test="concat('x_', $index) = $var/@name">
        <xsl:choose>
          <xsl:when test="count($var/../integer/@value) = 0">
            <xsl:call-template name="variable">
              <xsl:with-param name="iteration" select="1"/>
              <xsl:with-param name="index" select="$index"/>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:call-template name="variable">
              <xsl:with-param name="iteration" select="$var/../integer/@value"/>
              <xsl:with-param name="index" select="$index"/>
            </xsl:call-template>
          </xsl:otherwise>
        </xsl:choose>      
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="factor">
          <xsl:with-param name="var" select="$var"/>
          <xsl:with-param name="index" select="$index + 1"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template name="variable">
    <xsl:param name="iteration" select="1"/>
    <xsl:param name="index"/>
    <xsl:if test="$iteration &gt; 0">
      <polynomial>
        <variable>
          <xsl:value-of select="$index"/>
        </variable>
      </polynomial>
      <xsl:call-template name="variable">
        <xsl:with-param name="iteration" select="$iteration - 1"/>
        <xsl:with-param name="index" select="$index"/>
      </xsl:call-template>
    </xsl:if>  
  </xsl:template>

  <!-- ****************************************************************************************
       **  Matrix Order
       ****************************************************************************************
-->

  <xsl:template match="matrix-order">
    <interpretation>
      <type>
        <matrixInterpretation>
          <domain>
            <xsl:choose>
              <xsl:when test="@type='int'">
                <naturals/>
              </xsl:when>
              <xsl:when test="@type='rationals'">
                <rationals>
                  <delta>
                    <rational>
                      <numerator>1</numerator>
                      <denominator>2000</denominator>
                    </rational>
                  </delta>
                </rationals>
              </xsl:when>
              <xsl:when test="@type='arctic' and @belowZero='false'">
                <arctic>
                  <domain>
                    <naturals/>
                  </domain>
                </arctic>
              </xsl:when>
              <xsl:otherwise>
                <arctic>
                  <domain> 
                    <integers/>
                  </domain>
                </arctic>
              </xsl:otherwise>
            </xsl:choose>
          </domain>
          <dimension>
            <xsl:value-of select="@dimension"/>
          </dimension>
          <strictDimension>1</strictDimension>
        </matrixInterpretation>
      </type>
      <xsl:choose>
        <xsl:when test="@type='int'">
          <xsl:call-template name="matrix-mappings">
            <xsl:with-param name="order" select="."/>
            <xsl:with-param name="dimension" select="@dimension"/>
          </xsl:call-template>
        </xsl:when>
       <!-- <xsl:when test="@belowZero='true'">
          <xsl:call-template name="matrix-mappings">
            <xsl:with-param name="order" select="."/>
            <xsl:with-param name="dimension" select="@dimension"/>
            <xsl:with-param name="arctic" select="@type"/>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
        </xsl:otherwise>-->
        <xsl:otherwise>
          <xsl:call-template name="matrix-mappings">
            <xsl:with-param name="order" select="."/>
            <xsl:with-param name="dimension" select="@dimension"/>
            <xsl:with-param name="arctic" select="@type"/>
          </xsl:call-template>
        </xsl:otherwise>
      </xsl:choose>
    </interpretation>
  </xsl:template>

  <xsl:template name="matrix-mappings">
    <xsl:param name="order"/>
    <xsl:param name="i" select="1"/>
    <xsl:param name="dimension"/>
    <xsl:param name="arctic" select="false"/>
    <xsl:apply-templates select="$order/matrix-interpretation[$i]">
      <xsl:with-param name="dimension" select="$dimension"/>
      <xsl:with-param name="arctic" select="$arctic"/>
    </xsl:apply-templates>
    <xsl:choose>
      <xsl:when test="$i &lt; count($order/matrix-interpretation)">
        <xsl:call-template name="matrix-mappings">
          <xsl:with-param name="order" select="$order"/>
          <xsl:with-param name="i" select="$i + 1"/>
          <xsl:with-param name="dimension" select="$dimension"/>
          <xsl:with-param name="arctic" select="$arctic"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="matrix-interpretation">
    <xsl:param name="dimension"/>
    <xsl:param name="arctic"/>
    <interpret>
      <xsl:apply-templates select="symbol"/>
      <xsl:apply-templates select="labeledSymbol"/>
      <xsl:apply-templates select="mpolynomial">
        <xsl:with-param name="dimension" select="$dimension"/>
        <xsl:with-param name="arctic" select="$arctic"/>
      </xsl:apply-templates>        
    </interpret>
  </xsl:template>

  <xsl:template match="mpolynomial">
    <xsl:param name="dimension"/>
    <xsl:param name="arctic"/>
    <arity>
      <xsl:choose>
        <xsl:when test="count(../labeledSymbol) = 0">
          <xsl:value-of select="../symbol/@arity"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="../labeledSymbol/@arity"/>
        </xsl:otherwise>
      </xsl:choose>
    </arity>
    <polynomial>
      <sum>
        <xsl:choose>
          <xsl:when test="count(mmonomial)=0">
            <polynomial>
              <coefficient>
                <integer>0</integer>
              </coefficient>
            </polynomial>
          </xsl:when>
          <xsl:otherwise>
            <xsl:choose>
              <xsl:when test="count(denominator) = 0">
                <xsl:apply-templates select="mmonomial">
                  <xsl:with-param name="dimension" select="$dimension"/>
                  <xsl:with-param name="arctic" select="$arctic"/>
                  <xsl:with-param name="commonDenom" select="0"/>
                </xsl:apply-templates>              
              </xsl:when>
              <xsl:otherwise>
                <xsl:apply-templates select="mmonomial">
                  <xsl:with-param name="dimension" select="$dimension"/>
                  <xsl:with-param name="arctic" select="$arctic"/>
                  <xsl:with-param name="commonDenom" select="denominator/@value"/>
                </xsl:apply-templates>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </sum>
    </polynomial>
  </xsl:template>

  <xsl:template match="mmonomial">
    <xsl:param name="dimension"/>
    <xsl:param name="arctic"/>
    <xsl:param name="commonDenom"/>
    <polynomial>
      <product>
        <polynomial>
          <xsl:choose>
            <xsl:when test="count(polo-factor) &gt; 0">
              <coefficient>
                <xsl:apply-templates select="matrix">
                  <xsl:with-param name="dimension" select="$dimension"/>
                  <xsl:with-param name="arctic" select="$arctic"/>
                  <xsl:with-param name="commonDenom" select="$commonDenom"/>
                </xsl:apply-templates>
              </coefficient>
            </xsl:when>
            <xsl:otherwise>
              <coefficient>
                <xsl:apply-templates select="matrix/mvect">
                  <xsl:with-param name="dimension" select="$dimension"/>
                  <xsl:with-param name="arctic" select="$arctic"/>
                  <xsl:with-param name="commonDenom" select="$commonDenom"/>
                </xsl:apply-templates>
              </coefficient>
            </xsl:otherwise>
          </xsl:choose>
        </polynomial>
        <xsl:if test="count(polo-factor) &gt; 0">
          <xsl:call-template name="polo-factors">
            <xsl:with-param name="monom" select="."/>
          </xsl:call-template>
        </xsl:if>
      </product>
    </polynomial>
  </xsl:template>
        
  <xsl:template match="matrix">
    <xsl:param name="dimension"/>
    <xsl:param name="arctic"/>
    <xsl:param name="commonDenom"/>
    <matrix>
      <xsl:apply-templates select="mvect">
        <xsl:with-param name="dimension" select="$dimension"/>
        <xsl:with-param name="arctic" select="$arctic"/>
        <xsl:with-param name="commonDenom" select="$commonDenom"/>
      </xsl:apply-templates>  
    </matrix>
  </xsl:template>

  <xsl:template match="mvect">
    <xsl:param name="dimension"/>
    <xsl:param name="arctic"/>
    <xsl:param name="commonDenom"/>
    <vector>
      <xsl:choose>
        <xsl:when test="count(integer) &gt; count(arctic-int)">
          <xsl:call-template name="vectorList">
            <xsl:with-param name="node" select="."/>
            <xsl:with-param name="stop" select="count(integer)"/>
            <xsl:with-param name="dimension" select="$dimension"/>
            <xsl:with-param name="arctic" select="$arctic"/>
            <xsl:with-param name="commonDenom" select="$commonDenom"/>
          </xsl:call-template>
        </xsl:when>
        <!-- This is for the export of the varPolys 
             that might appear in the matrices -->
        <xsl:when test="count(polynomial) &gt; count(arctic-int)">
          <xsl:call-template name="vectorList">
            <xsl:with-param name="node" select="."/>
            <xsl:with-param name="stop" select="count(polynomial)"/>
            <xsl:with-param name="dimension" select="$dimension"/>
            <xsl:with-param name="arctic" select="$arctic"/>
            <xsl:with-param name="commonDenom" select="$commonDenom"/>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
          <xsl:call-template name="vectorList">
            <xsl:with-param name="node" select="."/>
            <xsl:with-param name="stop" select="count(arctic-int)"/>
            <xsl:with-param name="dimension" select="$dimension"/>
            <xsl:with-param name="arctic" select="$arctic"/>
            <xsl:with-param name="commonDenom" select="$commonDenom"/>
          </xsl:call-template>
        </xsl:otherwise>
      </xsl:choose>
    </vector>
  </xsl:template>

  <xsl:template name="vectorList">
    <xsl:param name="dimension"/>
    <xsl:param name="node"/>
    <xsl:param name="start" select="1"/>
    <xsl:param name="stop"/>
    <xsl:param name="arctic"/>
    <xsl:param name="commonDenom"/>
    <xsl:choose>
      <xsl:when test="$start &gt; $stop">
        <!-- Fill collapsing matrices with zeros -->
        <xsl:choose>
          <xsl:when test="number($dimension) &gt; $stop">
            <xsl:call-template name="fillVector">
              <xsl:with-param name="dimension" select="$dimension"/>
              <xsl:with-param name="stop" select="$stop"/>
              <xsl:with-param name="arctic" select="$arctic"/>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:text/>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <coefficient>
          <xsl:choose>
            <xsl:when test="count($node/arctic-int) &gt; 0">
              <xsl:choose>
                <xsl:when test="$node/arctic-int[$start]/@infinite = 'true'">
                  <minusInfinity/>
                </xsl:when>
                <xsl:otherwise>
                  <integer>
                    <xsl:value-of select="$node/arctic-int[$start]/@value"/>
                  </integer>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:when>
            <xsl:when test="count($node/polynomial) &gt; 0">
              <xsl:choose>
                <xsl:when test="count($node/polynomial[$start]/monomial)=0">
                  <integer>0</integer>
                </xsl:when>
                <xsl:otherwise>
                  <rational>
                    <numerator>
                      <xsl:value-of select="$node/polynomial[$start]/monomial/integer/@value"/>
                    </numerator>
                    <denominator>
                      <xsl:value-of select="$commonDenom"/>
                    </denominator>
                  </rational>
                </xsl:otherwise>
              </xsl:choose>
              <xsl:apply-templates mode="matrix" select="$node/polynomial"/>
            </xsl:when>
            <xsl:otherwise>
              <integer>
                <xsl:value-of select="$node/integer[$start]/@value"/>
              </integer>
            </xsl:otherwise>
          </xsl:choose>
        </coefficient>
        <xsl:call-template name="vectorList">
          <xsl:with-param name="node" select="$node"/>
          <xsl:with-param name="start" select="$start+1"/>
          <xsl:with-param name="stop" select="$stop"/>
          <xsl:with-param name="dimension" select="$dimension"/>
          <xsl:with-param name="arctic" select="$arctic"/>
          <xsl:with-param name="commonDenom" select="$commonDenom"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template name="fillVector">
    <xsl:param name="dimension"/>
    <xsl:param name="stop"/>
    <xsl:param name="arctic"/>
    <coefficient>
      <xsl:choose>
        <xsl:when test="$arctic='arctic'">
          <minusInfinity/>
        </xsl:when>
        <xsl:otherwise>
          <integer>0</integer>
        </xsl:otherwise>
      </xsl:choose>
    </coefficient>
    <xsl:if test="$dimension &gt; ($stop + 1)">
      <xsl:call-template name="fillVector">
        <xsl:with-param name="dimension" select="$dimension"/>
        <xsl:with-param name="stop" select="$stop + 1"/>
        <xsl:with-param name="arctic" select="$arctic"/>
      </xsl:call-template>
    </xsl:if>
  </xsl:template>
  
  <!-- ****************************************************************************************
       **  Term-related structures
       ****************************************************************************************
-->

  <xsl:template match="labeledSymbol">
    <xsl:choose>
      <xsl:when test="@sharp = 'true'">
        <sharp>
          <labeledSymbol>
            <!-- This is an exclusive or -->
            <xsl:apply-templates select="symbol"/>
            <xsl:apply-templates select="labeledSymbol"/>

            <xsl:apply-templates select="label"/>              
          </labeledSymbol>
        </sharp>
      </xsl:when>
      <xsl:otherwise>
        <labeledSymbol>
          <!-- This is an exclusive or -->
          <xsl:apply-templates select="symbol"/>
          <xsl:apply-templates select="labeledSymbol"/>

          <xsl:apply-templates select="label"/>              
        </labeledSymbol>        
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="label">
    <xsl:choose>
      <xsl:when test="@type = 'FSym'">
        <symbolLabel>
          <xsl:apply-templates select="symbol"/>
          <xsl:apply-templates select="labeledSymbol"/>
        </symbolLabel>
      </xsl:when>
      <xsl:otherwise>
        <numberLabel>
          <xsl:apply-templates mode="number" select="label"/>
        </numberLabel>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template mode="number" match="label">
    <number>
      <xsl:value-of select="integer/@value"/>
    </number>
  </xsl:template>

  <xsl:template match="symbol">
    <xsl:choose>
      <xsl:when test="@sharp='true'">
        <sharp>
          <name>
            <xsl:value-of select="@name"/>
          </name>
        </sharp>
      </xsl:when>
      <xsl:otherwise>
        <name>
          <xsl:value-of select="@name"/>
        </name>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template match="variable">
    <var>
      <xsl:value-of select="@name"/>
    </var>
  </xsl:template>

  <xsl:template match="term">
    <xsl:apply-templates/>
  </xsl:template>
  
  <xsl:template match="qtermset">
    <xsl:apply-templates/>
  </xsl:template>
  
  <xsl:template match="last-term">
    <xsl:apply-templates/>
  </xsl:template>

  <xsl:template match="fun-app">
    <funapp>
      <xsl:apply-templates select="symbol"/>
      <xsl:apply-templates select="labeledSymbol"/>
      <xsl:call-template name="arg-list"/>
    </funapp>
  </xsl:template>

  <xsl:template name="arg-list">
    <xsl:param name="i" select="1"/>
    <xsl:if test="$i &lt;= count(term)">
      <arg>
        <xsl:apply-templates select="term[$i]"/>
      </arg>
    </xsl:if>
    <xsl:choose>
      <xsl:when test="$i &lt; count(term)">
        <xsl:call-template name="arg-list">
          <xsl:with-param name="i" select="$i + 1"/>
        </xsl:call-template>
      </xsl:when>
      <!--No more arguments left-->
      <xsl:otherwise><xsl:text/></xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- Rules -->

  <xsl:template match="rule">
    <rule>
      <lhs>
        <xsl:apply-templates select="term[1]"/>
      </lhs>
      <rhs>
        <xsl:apply-templates select="term[2]"/>
      </rhs>
    </rule>
  </xsl:template>

  <xsl:template name="ruleset">
    <xsl:param name="rules"/>
    <xsl:param name="i" select="1"/>
    <xsl:choose>
      <xsl:when test="$i &lt;= count($rules/rule)">
        <xsl:apply-templates select="$rules/rule[$i]"/>
      </xsl:when>
    </xsl:choose>
    <xsl:choose>
      <xsl:when test="$i &lt; count($rules/rule)">
        <xsl:call-template name="ruleset">
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
      <rules>
        <xsl:call-template name="ruleset">
          <xsl:with-param name="rules" select="."/>
        </xsl:call-template>
      </rules>
  </xsl:template>

  <!-- ****************************************************************************************
       **  Auxiliary functions
       ****************************************************************************************
-->

  <!-- Transformation of natural numbers into CetaXML -->

  <xsl:template match="integer">
    <xsl:value-of select="@value"/>
  </xsl:template>

</xsl:transform>
