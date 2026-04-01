<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.0" >
  <xsl:output xmlns:xsl="http://www.w3.org/1999/XSL/Transform" method="html" />
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="/" >
    <html>
      <head>
        <title>
    Term
   </title>
      </head>
      <body>
        <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform"/>
      </body>
    </html>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Term" >
    <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="Varsym|Defsym|Conssym|Tuplesym" />
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Varsym" >
    <FONT COLOR="#CC8888" >
      <I>
        <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="text()" />
      </I>
    </FONT>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Defsym[@infix=&quot;yes&quot;]" >
    <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform">(</xsl:text>
    <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="../Term[1]" />
    <FONT COLOR="#000088" >
      <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform"/>
      <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="text()" />
      <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform"/>
    </FONT>
    <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="../Term[2]" />)
</xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Defsym[@infix=&quot;no&quot;]" >
    <FONT COLOR="#000088" >
      <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="text()" />
    </FONT>
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(../Term) > 0" >
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
    <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="../Term[1]" />
    <FONT COLOR="#666600" >
      <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform"/>
      <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="text()" />
      <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform"/>
    </FONT>
    <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="../Term[2]" />)
</xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Conssym[@infix=&quot;no&quot;]" >
    <FONT COLOR="#666600" >
      <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="text()" />
    </FONT>
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(../Term) > 0" >
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
    <xsl:call-template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="String" >
      <xsl:with-param xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="string()" name="myString" />
    </xsl:call-template>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="String" >
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="(substring(string(), 1,1) = &quot;-&quot;) and (substring(string(), string-length(string()), 1) = &quot;-&quot;) and (string-length() > 2)" >
      <S>
        <xsl:call-template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="StringAfterStrikeTest" >
          <xsl:with-param xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="myString" select="substring(string(), 2, string-length() - 2)" />
        </xsl:call-template>
      </S>
    </xsl:if>
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="not((substring(string(), 1,1) = &quot;-&quot;) and (substring(string(), string-length(string()), 1) = &quot;-&quot;) and (string-length() > 2))" >
      <xsl:call-template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="StringAfterStrikeTest" >
        <xsl:with-param xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="myString" select="string()" />
      </xsl:call-template>
    </xsl:if>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="StringAfterStrikeTest" >
    <xsl:param xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="myString" select="string()" />
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="(substring($myString, 1,1) = &quot;_&quot;) and (substring($myString, string-length($myString), 1) = &quot;_&quot;) and (string-length($myString) > 2)" >
      <U>
        <xsl:call-template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="StringAfterUnderlineTest" >
          <xsl:with-param xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="myString2" select="substring($myString, 2, string-length($myString) - 2)" />
        </xsl:call-template>
      </U>
    </xsl:if>
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="not((substring($myString, 1,1) = &quot;-&quot;) and (substring($myString, string-length($myString), 1) = &quot;-&quot;) and (string-length($myString) > 2))" >
      <xsl:call-template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="StringAfterUnderlineTest" >
        <xsl:with-param xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="myString2" select="$myString" />
      </xsl:call-template>
    </xsl:if>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="StringAfterUnderlineTest" >
    <xsl:param xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="myString2" select="string()" />
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="(substring($myString2, 1,1) = &quot;*&quot;) and (substring($myString2, string-length($myString2), 1) = &quot;*&quot;) and (string-length($myString2) > 2)" >
      <STRONG>
        <xsl:call-template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="InnerString" >
          <xsl:with-param xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="myString3" select="translate(substring($myString2, 2, string-length($myString2) - 2), &quot;[]&quot;, &quot;{}&quot;)" />
        </xsl:call-template>
      </STRONG>
    </xsl:if>
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="not((substring($myString2, 1,1) = &quot;*&quot;) and (substring($myString2, string-length($myString2), 1) = &quot;*&quot;) and (string-length($myString2) > 2))" >
      <xsl:call-template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="InnerString" >
        <xsl:with-param xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="translate($myString2, &quot;[]&quot;, &quot;{}&quot;)" name="myString3" />
      </xsl:call-template>
    </xsl:if>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="InnerString" >
    <xsl:param xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="myString3" select="string()" />
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="contains($myString3, &quot;_&quot;)" >
      <xsl:value-of xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="substring-before($myString3, &quot;_&quot;)" />
      <SUB>
        <FONT SIZE="-1" >
          <xsl:call-template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="InnerString" >
            <xsl:with-param xmlns:xsl="http://www.w3.org/1999/XSL/Transform" name="myString3" select="substring-after($myString3, &quot;_&quot;)" />
          </xsl:call-template>
        </FONT>
      </SUB>
    </xsl:if>
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="not(contains($myString3, &quot;_&quot;))" >
      <xsl:value-of xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="$myString3" />
    </xsl:if>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Tuplesym[@infix=&quot;yes&quot;]" >
    <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform">(</xsl:text>
    <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="../Term[1]" />
    <FONT COLOR="#006666" >
      <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform"/>
      <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="text()" />
      <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform"/>
    </FONT>
    <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="../Term[2]" />)
</xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Tuplesym[@infix=&quot;no&quot;]" >
    <FONT COLOR="#006666" >
      <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="text()" />
    </FONT>
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(../Term) > 0" >
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
