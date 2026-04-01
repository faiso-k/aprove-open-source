<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet 
    xmlns:xsl="http://www.w3.org/1999/XSL/Transform" 
    xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
    version="1.0">      
    
    <xsl:param name="toolUserAsCompetition">false</xsl:param>
    
    <!-- 
        this is the second part of the converter from CPF 2 to CPF 3;

        the first phase 1 is implemented in Haskell; it does the following things which were tedious/impossible in XSLT: 
           - compute rule-index
           - (on demand) compute term-index
           - compute implicit signature of trsInput
           - change from remaining rules/pairs to deleted rules/pairs
           - remove "arg" in "funapp"   (xsltproc hits segfault on highly nested terms)
           
         this second phase does the other steps, which are visible and documented in the source code below
    -->

    <!-- choose whether the output should be indented --> 
    <xsl:output method="xml" indent="no"/>
    
    <!-- do not modify the part below -->
            
    
    <xsl:strip-space elements="*"/>
        
    <!-- CHANGE TO INPUT / PROPERTY / ANSWER / PROOF STRUCTURE -->            
        
    <xsl:template match="certificationProblem">
        <xsl:processing-instruction name="xml-stylesheet">type="text/xsl" href="cpf3HTML.xsl"</xsl:processing-instruction>
        <certificationProblem xsi:noNamespaceSchemaLocation="cpf3.xsd">
            <cpfVersion>3.0</cpfVersion>
            <!-- insert a lookupTables element, and copy existing ones -->
            <lookupTables>
                <xsl:apply-templates select="lookupTables/termIndexTable"/>
                <xsl:apply-templates select="lookupTables/ruleTable"/>
            </lookupTables>
            <xsl:call-template name="inputOfCPF"/>
            <xsl:call-template name="propertyOfCPF"/>
            <xsl:call-template name="answerOfCPF"/>
            <xsl:apply-templates select="proof"/>
            <xsl:apply-templates select="origin"/>
        </certificationProblem>                
    </xsl:template>    
    
    <!-- patch input from CPF 2.x -->
    <xsl:template name="inputOfCPF">
        <input>
            <xsl:apply-templates select="input/*[1]" mode="input"/>
        </input>
    </xsl:template>
    
    <xsl:template match="complexityInput" mode="input">
        <xsl:apply-templates select="*[1]"/>
    </xsl:template>

    <xsl:template match="commutationInput" mode="input">
        <twoTrsWithSignature>
            <xsl:apply-templates select="*"/>            
        </twoTrsWithSignature>
    </xsl:template>
    
    <xsl:template match="trsInput" mode="input">
        <!-- (non)-confluence proofs require a signature -->
        <xsl:choose>
            <xsl:when test="/certificationProblem/proof/crProof">
                <xsl:call-template name="trsWithSignature"/>
            </xsl:when>
            <xsl:when test="/certificationProblem/proof/crDisproof">
                <xsl:call-template name="trsWithSignature"/>
            </xsl:when>
            <xsl:otherwise>
                <xsl:apply-templates select="."/>
            </xsl:otherwise>
        </xsl:choose>
    </xsl:template>
        
    <xsl:template name="trsWithSignature">
        <trsWithSignature>
            <!-- the signature will be computed in phase 1 of the converter and is available under lookupTables -->
            <xsl:apply-templates select="/certificationProblem/lookupTables/signature"/>
            <xsl:apply-templates select="trs"/>
        </trsWithSignature>
    </xsl:template>
    
    <xsl:template match="treeAutomatonProblem" mode="input">
        <treeAutomatonAndTrs>
            <xsl:apply-templates select="*"/>
        </treeAutomatonAndTrs>
    </xsl:template>
    
    <!-- add condition type for ctrs -->
    <xsl:template match="ctrsInput" mode="input">
        <ctrsInput>
            <ctrs>
                <conditionType><oriented/></conditionType>
                <xsl:apply-templates select="rules"/>
            </ctrs>
        </ctrsInput>        
    </xsl:template>
    
    <!-- add condition type for ctrs, change structure probs/rules/rule* to infeasibilityQuery/rule* -->
    <xsl:template match="infeasibilityInput" mode="input">
        <infeasibilityInput>
            <ctrs>
                <conditionType><oriented/></conditionType>
                <xsl:apply-templates select="rules"/>
            </ctrs>
            <infeasibilityQuery>
                <xsl:apply-templates select="probs/rules/*"/>
            </infeasibilityQuery>            
        </infeasibilityInput>        
    </xsl:template>
    
    <xsl:template match="completionInput" mode="input">
        <xsl:apply-templates select="equations"/>
    </xsl:template>
    
    <xsl:template match="*" mode="input">
        <xsl:apply-templates select="."/>
    </xsl:template>
    
    <!-- extract property from CPF 2.x -->
    <xsl:template name="propertyOfCPF">
        <property>
            <xsl:apply-templates select="proof/*[1]" mode="property"/>
        </property>
    </xsl:template>
            
    <xsl:template match="acTerminationProof" mode="property">
        <termination/>
    </xsl:template>
    
    <xsl:template match="comDisproof" mode="property">
        <commutation/>
    </xsl:template>
    
    <xsl:template match="comProof" mode="property">
        <commutation/>
    </xsl:template>
    
    <xsl:template match="completionProof" mode="property">
        <completion/>
    </xsl:template>
    
    <xsl:template match="complexityProof" mode="property">
        <complexity>
            <xsl:copy-of select="/certificationProblem/input/complexityInput/*[2]"/>
        </complexity>
    </xsl:template>
    
    <xsl:template match="conditionalCrDisproof" mode="property">
        <confluence/>
    </xsl:template>
    
    <xsl:template match="conditionalCrProof" mode="property">
        <confluence/>
    </xsl:template>
    
    <xsl:template match="crDisproof" mode="property">
        <confluence/>
    </xsl:template>
    
    <xsl:template match="crProof" mode="property">
        <confluence/>
    </xsl:template>
    
    <xsl:template match="dpNonterminationProof" mode="property">
        <termination/>
    </xsl:template>
    
    <xsl:template match="dpProof" mode="property">
        <termination/>
    </xsl:template>
    
    <xsl:template match="equationalDisproof" mode="property">
        <entailment/>
    </xsl:template>
    
    <xsl:template match="equationalProof" mode="property">
        <entailment/>
    </xsl:template>
    
    <xsl:template match="infeasibilityProof" mode="property">
        <infeasibility/>
    </xsl:template>
    
    <xsl:template match="ltsSafetyProof" mode="property">
        <safety/>
    </xsl:template>
    
    <xsl:template match="ltsTerminationProof" mode="property">
        <termination/>
    </xsl:template>
    
    <xsl:template match="quasiReductiveProof" mode="property">
        <termination/>
    </xsl:template>
    
    <xsl:template match="relativeNonterminationProof" mode="property">
        <termination/>
    </xsl:template>
    
    <xsl:template match="relativeTerminationProof" mode="property">
        <termination/>
    </xsl:template>
    
    <xsl:template match="treeAutomatonClosedProof" mode="property">
        <closedUnderRewriting/>
    </xsl:template>
    
    <xsl:template match="trsNonterminationProof" mode="property">
        <termination/>
    </xsl:template>
    
    <xsl:template match="trsTerminationProof" mode="property">
        <termination/>
    </xsl:template>    
    
    <xsl:template match="*" mode="property">
        <xsl:message terminate="yes">Could not extract property for <xsl:value-of select="name(.)"/></xsl:message>        
    </xsl:template>
    
    
    <!-- extract answer from CPF 2.x -->
    <xsl:template name="answerOfCPF">
        <answer>
            <xsl:apply-templates select="proof/*[1]" mode="answer"/>
        </answer>
    </xsl:template>
    
    <xsl:template match="acTerminationProof" mode="answer">
        <yes/>
    </xsl:template>
    
    <xsl:template match="comDisproof" mode="answer">
        <no/>
    </xsl:template>
    
    <xsl:template match="comProof" mode="answer">
        <yes/>
    </xsl:template>
    
    <xsl:template match="completionProof" mode="answer">
        <completedTrs>
            <xsl:apply-templates select="/certificationProblem/input/completionInput/*[2]"/>
        </completedTrs>
    </xsl:template>
    
    <xsl:template match="complexityProof" mode="answer">
        <upperBound>
            <xsl:copy-of select="/certificationProblem/input/complexityInput/*[3]"/>
        </upperBound>
    </xsl:template>
    
    <xsl:template match="conditionalCrDisproof" mode="answer">
        <no/>
    </xsl:template>
    
    <xsl:template match="conditionalCrProof" mode="answer">
        <yes/>
    </xsl:template>
    
    <xsl:template match="crDisproof" mode="answer">
        <no/>
    </xsl:template>
    
    <xsl:template match="crProof" mode="answer">
        <yes/>
    </xsl:template>
    
    <xsl:template match="dpNonterminationProof" mode="answer">
        <no/>
    </xsl:template>
    
    <xsl:template match="dpProof" mode="answer">
        <yes/>
    </xsl:template>
    
    <xsl:template match="equationalDisproof" mode="answer">
        <no/>
    </xsl:template>
    
    <xsl:template match="equationalProof" mode="answer">
        <yes/>
    </xsl:template>
    
    <xsl:template match="infeasibilityProof" mode="answer">
        <yes/>
    </xsl:template>
    
    <xsl:template match="ltsSafetyProof" mode="answer">
        <yes/>
    </xsl:template>
    
    <xsl:template match="ltsTerminationProof" mode="answer">
        <yes/>
    </xsl:template>
    
    <xsl:template match="quasiReductiveProof" mode="answer">
        <yes/>
    </xsl:template>
    
    <xsl:template match="relativeNonterminationProof" mode="answer">
        <no/>
    </xsl:template>
    
    <xsl:template match="relativeTerminationProof" mode="answer">
        <yes/>
    </xsl:template>
    
    <xsl:template match="treeAutomatonClosedProof" mode="answer">
        <yes/>
    </xsl:template>
    
    <xsl:template match="trsNonterminationProof" mode="answer">
        <no/>
    </xsl:template>
    
    <xsl:template match="trsTerminationProof" mode="answer">
        <yes/>
    </xsl:template>
    
    <!-- adjust meta-information -->
    
    <xsl:template match="origin">
        <metaInformation>
            <xsl:if test="count(inputOrigin/tpdbReference) + count(inputOrigin/source) > 0">
                <inputInfos>
                    <xsl:for-each select="inputOrigin/source">
                        <inputInfo>
                            <xsl:value-of select="text()"/>
                        </inputInfo>
                    </xsl:for-each>                                
                    <xsl:for-each select="inputOrigin/tpdbReference/fileName">
                        <inputInfo>
                            <xsl:value-of select="concat('TPDB-filename: ',text())"/>
                        </inputInfo>
                    </xsl:for-each>
                    <xsl:for-each select="inputOrigin/tpdbReference/tpdbId">
                        <inputInfo>
                            <xsl:value-of select="concat('TPDB-id: ', text())"/>
                        </inputInfo>
                    </xsl:for-each>                
                </inputInfos>
            </xsl:if>
            <xsl:apply-templates select="proofOrigin"/>
            <xsl:if test="$toolUserAsCompetition='true'">
                <competitionInfo><xsl:value-of select="concat(proofOrigin/toolUser/firstName/text(),' ',proofOrigin/toolUser/lastName/text())"/></competitionInfo>
            </xsl:if>
        </metaInformation>
    </xsl:template>
        
    <xsl:template match="proofOrigin">
        <toolInfos>
            <xsl:for-each select="tool">
                <toolInfo>
                    <xsl:value-of select="name/text()"/>
                </toolInfo>
                <toolInfo>
                    <xsl:value-of select="concat('version: ', version/text())"/>
                </toolInfo>
                <xsl:if test="strategy">
                    <toolInfo>
                        <xsl:value-of select="concat('strategy: ', strategy/text())"/>
                    </toolInfo>                    
                </xsl:if>
                <xsl:if test="url">
                    <toolInfo>
                        <xsl:value-of select="concat('url: ', url/text())"/>
                    </toolInfo>                    
                </xsl:if>                
            </xsl:for-each>
            <xsl:for-each select="toolUser">
                <toolInfo>
                    <xsl:value-of select="concat('tool user: ',firstName/text(),' ',lastName/text())"/>
                </toolInfo>
            </xsl:for-each>
        </toolInfos>
    </xsl:template>
    
   
    <!-- LIMITATIONS -->
    
    <xsl:template match="unlab">
        <xsl:message terminate="yes">the converter cannot treat "unlab", convert to "split" manually</xsl:message>
    </xsl:template>
    
    <xsl:template match="unlabProc">
        <xsl:message terminate="yes">the converter cannot treat "unlabProc", convert to "splitProc" manually</xsl:message>
    </xsl:template>
    
   
    <!-- LOCAL CHANGES OF CPF -->
    
       
    <!-- remove "arg" in "funapp": 
         this is done by phase 1, since xslt processors cannot treat deeply nested terms (segmentation faults);
         therefore, we here abort the recursive replacement procedure and just do a copy -->
    <xsl:template match="funapp">
        <xsl:copy-of select="."/>
    </xsl:template>
    
    
    <!-- remove "orderingConstraintProof" element around  a reduction pair -->
    <xsl:template match="orderingConstraintProof">
        <xsl:apply-templates/>        
    </xsl:template>

    <!-- remove "redPair" element around a reduction pair -->
    <xsl:template match="redPair">
        <xsl:apply-templates/>        
    </xsl:template>
    
    <!-- remove "polynomial" element to define polynomials, but not as bound- or as domain-type -->
    <xsl:template match="polynomial">
        <xsl:choose>
            <xsl:when test="count(*) = 1">
                 <xsl:apply-templates/>                    
            </xsl:when>
            <xsl:otherwise>
                <polynomial>
                    <xsl:apply-templates/>                    
                </polynomial>
            </xsl:otherwise>
        </xsl:choose>                
    </xsl:template>
    
    <!-- remove "coefficient" element to define polynomials and vectors -->
    <xsl:template match="coefficient">
        <xsl:apply-templates/>        
    </xsl:template>
    
    <!-- remove "lhs" and "rhs" in (conditional) rules, but not in tree automata -->
    <xsl:template match="lhs">
        <xsl:choose>
            <xsl:when test="count(var)+count(funapp)+count(termIndex) != 0">
                <xsl:apply-templates/>
            </xsl:when>
            <xsl:otherwise>
                <lhs>
                    <xsl:apply-templates/>
                </lhs>
            </xsl:otherwise>
        </xsl:choose>
    </xsl:template>

    <xsl:template match="rhs">
        <xsl:choose>
            <xsl:when test="count(var)+count(funapp)+count(termIndex) != 0">
                <xsl:apply-templates/>
            </xsl:when>
            <xsl:otherwise>
                <rhs>
                    <xsl:apply-templates/>
                </rhs>
            </xsl:otherwise>
        </xsl:choose>
    </xsl:template>
    
    <!-- rename pathOrder to recursivePathOrder -->
    <xsl:template match="pathOrder">
        <recursivePathOrder>
            <xsl:apply-templates/>
        </recursivePathOrder>
    </xsl:template>
    
    <!-- drop "markedSymbols" in "dpTrans" -->
    <xsl:template match="dpTrans">
        <dpTrans>
            <xsl:apply-templates select="*[1]"/>
            <xsl:apply-templates select="*[3]"/>
        </dpTrans>
    </xsl:template>
    
    <!-- only list dps and proof in (ac)-dp-graph-component -->
    <xsl:template match="depGraphProc">
        <depGraphProc>
            <xsl:for-each select="component">
                <component>
                    <xsl:apply-templates select="dps"/>
                    <xsl:apply-templates select="dpProof"/>
                </component>                
            </xsl:for-each>
        </depGraphProc>
    </xsl:template>

    <xsl:template match="acDepGraphProc">
        <acDepGraphProc>
            <xsl:for-each select="component">
                <component>
                    <xsl:apply-templates select="dps"/>
                    <xsl:apply-templates select="acDPTerminationProof"/>
                </component>                
            </xsl:for-each>
        </acDepGraphProc>
    </xsl:template>
    
    <!-- merge of relativeTerminationProof and trsTerminationProof: just rename, and delete sIsEmpty -->
    <xsl:template match="relativeTerminationProof">
        <xsl:choose>
            <xsl:when test="sIsEmpty">
                <xsl:apply-templates select="sIsEmpty/*"/>
            </xsl:when>            
            <xsl:otherwise>
                <trsTerminationProof>
                    <xsl:apply-templates/>
                </trsTerminationProof>                
            </xsl:otherwise>
        </xsl:choose>
    </xsl:template>

    <!-- insert tag "ignoreRelativePart" for trs-nontermination-proof in relative-nontermination-proof -->
    <xsl:template match="relativeNonterminationProof">
        <relativeNonterminationProof>
            <xsl:choose>
                <xsl:when test="trsNonterminationProof">
                    <ignoreRelativePart>
                        <xsl:apply-templates/>
                    </ignoreRelativePart>
                </xsl:when>            
                <xsl:otherwise>
                    <xsl:apply-templates/>
                </xsl:otherwise>
            </xsl:choose>            
        </relativeNonterminationProof>
    </xsl:template>
    
    <!-- simplify conversions where just terms need to be listed now -->
    <xsl:template match="conversion">
        <conversion>
            <xsl:apply-templates select="startTerm/*[1]"/>
            <xsl:for-each select="equationStep">
                <xsl:apply-templates select="*[4]"/>
            </xsl:for-each>
        </conversion>
    </xsl:template>
    
    <!-- transform convertibleCriticalPeaks -->
    <xsl:template match="convertibleCriticalPeaks">
        <joinSequences>
            <xsl:for-each select="convertibleCriticalPeak">
                <critPairInfo>
                    <left><xsl:apply-templates select="conversionLeft/conversion[1]/startTerm/*[1]"/></left>
                    <peak><xsl:apply-templates select="source/*[1]"/></peak>
                    <right><xsl:apply-templates select="conversionRight/conversion[1]/startTerm/*[1]"/></right>
                    <intermediateTerms>
                        <!-- in total there are n steps, and we have to list the targets of the first n-1 steps -->
                        <xsl:variable name="steps6" select="count(conversionRight/conversion[1]/equationStep) != 0"/>                        
                        <xsl:variable name="steps5" select="count(conversionRight/rewriteSequence/rewriteStep) != 0 or $steps6"/>
                        <xsl:variable name="steps4" select="count(conversionRight/conversion[2]/equationStep) != 0 or $steps5"/>
                        <xsl:variable name="steps3" select="count(conversionLeft/conversion[2]/equationStep) != 0 or $steps4"/>
                        <xsl:variable name="steps2" select="count(conversionLeft/rewriteSequence/rewriteStep) != 0 or $steps3"/>
                        <xsl:for-each select="conversionLeft/conversion[1]/equationStep">
                            <xsl:if test="$steps2 or position() != last()">
                                <xsl:apply-templates select="*[last()]"/>
                            </xsl:if>
                        </xsl:for-each> 
                        <xsl:for-each select="conversionLeft/rewriteSequence/rewriteStep">
                            <xsl:if test="$steps3 or position() != last()">
                                <xsl:apply-templates select="*[last()]"/>
                            </xsl:if>
                        </xsl:for-each> 
                        <xsl:for-each select="conversionLeft/conversion[2]/equationStep">
                            <xsl:if test="$steps4 or position() != last()">
                                <xsl:apply-templates select="*[last()]"/>
                            </xsl:if>                           
                        </xsl:for-each>
                        <xsl:for-each select="conversionRight/conversion[2]/equationStep">
                            <xsl:sort select="position()" data-type="number" order="descending"/>
                            <xsl:if test="$steps5 or position() != last()">
                                <xsl:apply-templates select="*[last()]"/>
                            </xsl:if>
                        </xsl:for-each>
                        <xsl:for-each select="conversionRight/rewriteSequence/rewriteStep">
                            <xsl:sort select="position()" data-type="number" order="descending"/>
                            <xsl:if test="$steps6 or position() != last()">
                                <xsl:apply-templates select="*[last()]"/>
                            </xsl:if>
                        </xsl:for-each>
                        <xsl:for-each select="conversionRight/conversion[1]/equationStep">
                            <xsl:sort select="position()" data-type="number" order="descending"/>
                            <xsl:if test="position() != last()">
                                <xsl:apply-templates select="*[last()]"/>
                            </xsl:if>
                        </xsl:for-each>
                    </intermediateTerms>
                </critPairInfo>
            </xsl:for-each>
        </joinSequences>
    </xsl:template>
        
    <!-- transform joinableCriticalPairs -->
    <xsl:template match="joinableCriticalPairs">
        <joinSequences>
            <xsl:for-each select="joinableCriticalPair">
                <critPairInfo>
                    <left><xsl:apply-templates select="rewriteSequence[1]/startTerm/*[1]"/></left>
                    <right><xsl:apply-templates select="rewriteSequence[2]/startTerm/*[1]"/></right>
                    <intermediateTerms>
                        <xsl:for-each select="rewriteSequence[1]/rewriteStep">
                            <xsl:if test="not (position() = last())">
                                <xsl:apply-templates select="*[last()]"/>
                            </xsl:if>
                        </xsl:for-each>
                        <xsl:for-each select="rewriteSequence[2]/rewriteStep">
                            <xsl:sort select="position()" data-type="number" order="descending"/>
                            <xsl:apply-templates select="*[last()]"/>
                        </xsl:for-each>
                    </intermediateTerms>
                </critPairInfo>
            </xsl:for-each>
        </joinSequences>
    </xsl:template>
    
    <xsl:template match="wcrProof">
        <wcrProof>
            <xsl:choose>
                <xsl:when test="joinableCriticalPairsAuto">
                    <joinAutoNF/>
                </xsl:when>
                <xsl:when test="joinableCriticalPairsBFS">
                    <joinAutoBfs><xsl:value-of select="joinableCriticalPairsBFS/text()"/></joinAutoBfs>
                </xsl:when>
                <xsl:when test="joinableCriticalPairs">
                    <xsl:apply-templates select="joinableCriticalPairs"/>
                </xsl:when>
            </xsl:choose>
        </wcrProof>
    </xsl:template>
    
    <!-- rename auto as join-hints -->
    <xsl:template match="auto">
        <joinAutoBfs>
            <xsl:value-of select="text()"/>
        </joinAutoBfs>
    </xsl:template>
    
    <!-- convert various join-limit numbers on critical pairs in crProof into joinAutoBfs-element -->
    <xsl:template name="joinAutoBfs">
        <joinAutoBfs>
            <xsl:choose>
                <xsl:when test="normalize-space(text()) != ''"><xsl:value-of select="text()"/></xsl:when>
                <!-- certain proofs provide a "no number" option. We encode this as -1 -->
                <xsl:otherwise>-1</xsl:otherwise>
            </xsl:choose>
        </joinAutoBfs>
    </xsl:template>
    
    <xsl:template match="stronglyClosed">
        <stronglyClosed><xsl:call-template name="joinAutoBfs"/></stronglyClosed>
    </xsl:template>

    <xsl:template match="parallelClosed">
        <parallelClosed><xsl:call-template name="joinAutoBfs"/></parallelClosed>
    </xsl:template>
    
    <xsl:template match="developmentClosed">
        <developmentClosed><xsl:call-template name="joinAutoBfs"/></developmentClosed>
    </xsl:template>
    
    <xsl:template match="criticalPairClosingSystem">
        <criticalPairClosingSystem>
            <xsl:apply-templates select="*[1]"/>
            <xsl:apply-templates select="*[2]"/>
            <joinAutoBfs>
                <xsl:value-of select="nrSteps/text()"/>
            </joinAutoBfs>
        </criticalPairClosingSystem>
    </xsl:template>
    
        
    <!-- merge trss in relative setting -->
    <xsl:template match="semlab">
        <semlab>
            <xsl:apply-templates select="*[1]"/>
            <trs>
                <xsl:apply-templates select="trs/*"/>
            </trs>
            <xsl:apply-templates select="*[last()]"/>
        </semlab>
    </xsl:template>
    
    <!-- transpose matrix representation from list of column vectors to list of row vectors -->
    <xsl:template match="matrix">
        <matrix>
            <xsl:call-template name="matrix2">
                <xsl:with-param name="width" select="count(vector)"/>
                <xsl:with-param name="heigth" select="count(vector[1]/*)"/>
                <xsl:with-param name="h" select="1"/>
            </xsl:call-template>            
        </matrix>
    </xsl:template>
    
    <xsl:template name="matrix2">
        <xsl:param name="heigth"/>
        <xsl:param name="width"/>
        <xsl:param name="h"/>
        <vector>
            <xsl:call-template name="matrix3">
                <xsl:with-param name="width" select="$width"/>
                <xsl:with-param name="h" select="$h"/>                
                <xsl:with-param name="w" select="1"/>                
            </xsl:call-template>
        </vector>
        <xsl:if test="$h != $heigth">
            <xsl:call-template name="matrix2">
                <xsl:with-param name="heigth" select="$heigth"/>
                <xsl:with-param name="width" select="$width"/>
                <xsl:with-param name="h" select="$h + 1"/>
            </xsl:call-template>
        </xsl:if>
    </xsl:template>
    
    <xsl:template name="matrix3">
        <xsl:param name="width"/>
        <xsl:param name="h"/>
        <xsl:param name="w"/>
        <xsl:apply-templates select="vector[$w]/*[$h]"/>
        <xsl:if test="$w != $width">
            <xsl:call-template name="matrix3">
                <xsl:with-param name="width" select="$width"/>
                <xsl:with-param name="w" select="$w + 1"/>
                <xsl:with-param name="h" select="$h"/>
            </xsl:call-template>
        </xsl:if>
    </xsl:template>    
                
    <!-- default: copy data of element unchanged and recurse  -->
    <xsl:template match="*">
        <xsl:copy>
            <xsl:copy-of select="@*"/>
            <xsl:apply-templates/>
        </xsl:copy>
    </xsl:template>
    
        
</xsl:stylesheet>
