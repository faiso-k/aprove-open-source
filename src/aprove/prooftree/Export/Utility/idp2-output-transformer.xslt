<?xml version="1.0" encoding="iso-8859-1"?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
                version="2.0">
    <xsl:include href="src/aprove/ProofTree/Export/Utility/plainCharacters.xslt"/>
	<xsl:output method="text" use-character-maps="plain" encoding="UTF-8" omit-xml-declaration="yes" indent="no" />

	<!-- TODO: <?xml ... Tag aus der Ausgabe raus. Einstellungsmöglichkeit, 
		ob bei Clause Newlines oder Unds gesetzt werden sollen als Argument des XmlExporters. 
		Einbauen: - ItpfEdgeOrientation - ItpfTrue - ItpfEdgeUra -->

	<xsl:variable name="singlei" select="3" />

    <xsl:strip-space elements="*" />
    
	<xsl:template match="*">
		<xsl:text>!! XSL: unknown element '</xsl:text>
		<xsl:value-of select="local-name()" />
		<xsl:text>' !!</xsl:text>
	</xsl:template>

	<xsl:template name="nl">
		<xsl:text>
</xsl:text>
	</xsl:template>

	<xsl:template name="indent">
		<xsl:param name="count" />
		<xsl:if test="$count > 0">
			<xsl:text> </xsl:text>
			
			<xsl:call-template name="indent">
				<xsl:with-param name="count" select="$count - 1" />
			</xsl:call-template>
		</xsl:if>
	</xsl:template>

	<xsl:template match="/">
		<xsl:apply-templates>
			<xsl:with-param name="indent" select="0" />
		</xsl:apply-templates>
	</xsl:template>

    <xsl:template match="ItpfTrue">
        <xsl:param name="indent" />
        <xsl:call-template name="indent">
            <xsl:with-param name="count" select="$indent" />
        </xsl:call-template>
        <xsl:text>TRUE</xsl:text>
    </xsl:template>    
    
    <xsl:template match="ItpfFalse">
        <xsl:param name="indent" />
        <xsl:call-template name="indent">
            <xsl:with-param name="count" select="$indent" />
        </xsl:call-template>
        <xsl:text>FALSE</xsl:text>
    </xsl:template>    

	<xsl:template match="ItpfFormula">
		<xsl:param name="indent" />
        <xsl:call-template name="indent">
            <xsl:with-param name="count" select="$indent" />
        </xsl:call-template>

		<xsl:if test="ItpfQuantor">
			<xsl:for-each select="ItpfQuantor">
	            <xsl:apply-templates select=".">
	            </xsl:apply-templates> 
	            <xsl:if test="position()!=last()">
	                <xsl:text> </xsl:text>
	            </xsl:if>
			</xsl:for-each>
	        
	        <xsl:call-template name="nl" />
        </xsl:if>	        
		
        <xsl:for-each select="ItpfConjClause">
	        <xsl:apply-templates select=".">
	            <xsl:with-param name="indent" select="$indent" />
	        </xsl:apply-templates>
            <xsl:if test="position()!=last()">
                <xsl:call-template name="nl" />
            </xsl:if>
        </xsl:for-each>
	</xsl:template>

    <xsl:template match="ItpfQuantor">
		<xsl:choose>
			<xsl:when test="@universalQuantor='true'">
			     <xsl:call-template name="forall"/>
			</xsl:when>
            <xsl:otherwise>
                 <xsl:call-template name="exists"/>
            </xsl:otherwise>
		</xsl:choose>
        <xsl:apply-templates select="IVariable">
            <xsl:with-param name="indent" select="0" />
        </xsl:apply-templates>
    </xsl:template>

	<xsl:template match="ItpfImplication">
		<xsl:param name="indent" />

		<xsl:apply-templates select="precondition">
			<xsl:with-param name="indent" select="$indent" />
		</xsl:apply-templates>

		<xsl:call-template name="indent">
			<xsl:with-param name="count" select="$indent" />
		</xsl:call-template>

        <xsl:call-template name="rArr"/>
   
		<xsl:apply-templates select="conclusion">
			<xsl:with-param name="indent" select="$indent" />
		</xsl:apply-templates>
	</xsl:template>

	<xsl:template match="precondition">
		<xsl:param name="indent" />

		<xsl:call-template name="indent">
			<xsl:with-param name="count" select="$indent" />
		</xsl:call-template>

		<xsl:text>precondition {</xsl:text>
        <xsl:call-template name="nl" />

		<xsl:apply-templates>
			<xsl:with-param name="indent" select="$indent + $singlei" />
		</xsl:apply-templates>

		<xsl:call-template name="nl" />
		<xsl:call-template name="indent">
			<xsl:with-param name="count" select="$indent" />
		</xsl:call-template>
        <xsl:text>}</xsl:text>
	</xsl:template>

	<xsl:template match="conclusion">
		<xsl:param name="indent" />

		<xsl:call-template name="indent">
			<xsl:with-param name="count" select="$indent" />
		</xsl:call-template>
		
		<xsl:text>conclusion {</xsl:text>
        <xsl:call-template name="nl" />
		
		<xsl:apply-templates>
			<xsl:with-param name="indent" select="$indent + $singlei" />
		</xsl:apply-templates>

		<xsl:call-template name="nl" />
		<xsl:call-template name="indent">
			<xsl:with-param name="count" select="$indent" />
		</xsl:call-template>
		<xsl:text>}</xsl:text>
	</xsl:template>

	<xsl:template match="ItpfConjClause">
		<xsl:param name="indent" />
        <xsl:variable name="childIndent" select="$singlei + $indent * (count(*) &gt; 1)" />
        
		<xsl:call-template name="indent">
			<xsl:with-param name="count" select="$indent" />
		</xsl:call-template>
		
        <xsl:if test="count(*) &gt; 1">
          <xsl:text>AND {</xsl:text>
          <xsl:call-template name="nl" />
        </xsl:if>		
        
		<xsl:for-each select="*">
            <xsl:apply-templates select=".">
                <xsl:with-param name="indent" select="$childIndent" />
            </xsl:apply-templates>
            
            <xsl:if test="position() != last()">
                <xsl:call-template name="nl"/>
            </xsl:if>
        </xsl:for-each>
		
        <xsl:if test="count(*) &gt; 1">
            <xsl:call-template name="nl"/>
	        <xsl:call-template name="indent">
	            <xsl:with-param name="count" select="$indent" />
	        </xsl:call-template>
    		<xsl:text>}</xsl:text>
        </xsl:if>           
    		
	</xsl:template>

	<xsl:template match="ItpfBoolPolyVar">
		<xsl:param name="indent" />
		<xsl:call-template name="indent">
			<xsl:with-param name="count" select="$indent" />
		</xsl:call-template>

		<xsl:apply-templates>
			<xsl:with-param name="indent" select="$indent" />
		</xsl:apply-templates>
	</xsl:template>

	<xsl:template match="IVariable">
		<xsl:param name="indent" />
		<xsl:value-of select="@name" />
	</xsl:template>

	<xsl:template match="ItpfPolyAtom">
		<xsl:param name="indent" />

		<xsl:call-template name="indent">
			<xsl:with-param name="count" select="$indent" />
		</xsl:call-template>

		<xsl:apply-templates select="left">
			<xsl:with-param name="indent" select="$indent" />
		</xsl:apply-templates>
            
        <xsl:text> </xsl:text>

		<xsl:value-of select="ConstraintType/@value" />

        <xsl:text> </xsl:text>

		<xsl:apply-templates select="right">
			<xsl:with-param name="indent" select="$indent" />
		</xsl:apply-templates>
	</xsl:template>

	<xsl:template match="left">
		<xsl:apply-templates select="*" />
	</xsl:template>

	<xsl:template match="right">
		<xsl:apply-templates select="*" />
	</xsl:template>

	<xsl:template match="var">
		<xsl:apply-templates select="*" />
	</xsl:template>

	<xsl:template match="exp">
		<xsl:apply-templates select="*" />
	</xsl:template>

	<xsl:template match="coeff">
		<xsl:apply-templates select="*" />
	</xsl:template>

	<xsl:template match="Polynomial">
		<xsl:for-each select="monomial">
			<xsl:variable name="mid" select="@id" />

			<xsl:variable name="coeff">
				<xsl:apply-templates select="../coeff[@id=$mid]" />
			</xsl:variable>

			<xsl:variable name="abscoeff"
				select="$coeff*($coeff >= 0) - $coeff*($coeff &lt; 0)" />

			<xsl:if test="./Monomial/var">
                <xsl:if test="position() != 1">
                    <xsl:text> </xsl:text>
                </xsl:if>
                
				<xsl:if test="$coeff &lt; 0">
                    <xsl:call-template name="minus"/>
	                <xsl:if test="$abscoeff = 1">
                        <xsl:text> </xsl:text>
	                </xsl:if>
  				</xsl:if>
                <xsl:if test="$coeff >= 0 and position() != 1">
                    <xsl:call-template name="plus"/>
                    <xsl:text> </xsl:text>
                </xsl:if>
				
				<xsl:if test="$abscoeff != 1">
					<xsl:value-of select="$abscoeff" />
				</xsl:if>

				<xsl:apply-templates select="Monomial" />
			</xsl:if>

			<xsl:if test="not(./Monomial/var)">
				<xsl:value-of select="$coeff" />
			</xsl:if>
		</xsl:for-each>
	</xsl:template>

	<xsl:template match="Monomial">
		<!-- TODO: anpassen an Änderungen wie oben beschrieben -->

		<xsl:for-each select="var">
			<xsl:variable name="vid" select="@id" />

			<xsl:variable name="exp">
				<xsl:apply-templates select="../exp[@id=$vid]" />
			</xsl:variable>

			<xsl:apply-templates select=".">
			</xsl:apply-templates>

			<xsl:choose>
                <xsl:when test="$exp!=1">
	                <xsl:call-template name="sup">
	                    <xsl:with-param name="value" select="$exp" />
	                </xsl:call-template>
                </xsl:when>
                <xsl:otherwise>
                    <xsl:value-of select="$exp" />
                </xsl:otherwise>
			</xsl:choose>

			<xsl:if test="position()!=last()">
                <xsl:text> </xsl:text>
                <xsl:call-template name="times"/>
                <xsl:text> </xsl:text>
   			</xsl:if>
		</xsl:for-each>

		<!--<xsl:apply-templates select="var"> <xsl:with-param name="indent" select="$indent" 
			/> </xsl:apply-templates><xsl:if test="exp/BigInt/@value!=1">^<xsl:apply-templates 
			select="exp"> <xsl:with-param name="indent" select="$indent" /> </xsl:apply-templates></xsl:if> -->
	</xsl:template>

	<xsl:template match="key">
		<xsl:param name="indent" />
		<xsl:apply-templates>
			<xsl:with-param name="indent" select="$indent" />
		</xsl:apply-templates>
	</xsl:template>

	<xsl:template match="value">
		<xsl:param name="indent" />
		<xsl:apply-templates>
			<xsl:with-param name="indent" select="$indent" />
		</xsl:apply-templates>
	</xsl:template>

	<xsl:template match="ConstraintType">
		<xsl:param name="indent" />
		<xsl:value-of select="@value" />
	</xsl:template>

	<xsl:template match="ItpfItp">
		<xsl:param name="indent" />

		<xsl:call-template name="indent">
			<xsl:with-param name="count" select="$indent" />
		</xsl:call-template>

		<xsl:apply-templates select="l">
			<xsl:with-param name="indent" select="$indent" />
		</xsl:apply-templates>

		<xsl:text> </xsl:text>

		<xsl:apply-templates select="relation">
			<xsl:with-param name="indent" select="$indent" />
		</xsl:apply-templates>

		<xsl:text> </xsl:text>

		<xsl:apply-templates select="r">
			<xsl:with-param name="indent" select="$indent" />
		</xsl:apply-templates>
	</xsl:template>

	<xsl:template match="l">
		<xsl:apply-templates select="*" />
	</xsl:template>

	<xsl:template match="r">
		<xsl:apply-templates select="*" />
	</xsl:template>

	<xsl:template match="relation">
		<xsl:apply-templates select="*" />
	</xsl:template>

	<xsl:template match="argument">
		<xsl:apply-templates select="*" />
	</xsl:template>

	<xsl:template match="IFunctionApplication">
		<xsl:param name="indent" />

		<xsl:if test="IFunctionSymbol/@predef and IFunctionSymbol/@arity=2">
			<xsl:for-each select="argument">
				<xsl:apply-templates select="." />
				<xsl:if test="position()!=last()">
                    <xsl:text> </xsl:text>
					<xsl:value-of select="../IFunctionSymbol/@name" />
                    <xsl:text> </xsl:text>
				</xsl:if>
			</xsl:for-each>
		</xsl:if>

		<xsl:if test="not(IFunctionSymbol/@predef) or IFunctionSymbol/@arity!=2">
			<xsl:value-of select="IFunctionSymbol/@name" />
			<xsl:if test="argument">
				<xsl:text>(</xsl:text>
				<xsl:for-each select="argument">
					<xsl:apply-templates />
					<xsl:if test="position()!=last()">
						<xsl:text>, </xsl:text>
					</xsl:if>
				</xsl:for-each>
                <xsl:text>)</xsl:text>
			</xsl:if>
		</xsl:if>
	</xsl:template>

	<xsl:template match="ItpRelation">
		<xsl:param name="indent" />
		<xsl:value-of select="@value" />
	</xsl:template>

	<xsl:template match="BigInt">
		<xsl:param name="indent" />
		<xsl:value-of select="@value" />
	</xsl:template>

</xsl:stylesheet>
