<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.0" >
  <xsl:include xmlns:xsl="http://www.w3.org/1999/XSL/Transform" href="TermToHTML.xsl" />
  <xsl:output xmlns:xsl="http://www.w3.org/1999/XSL/Transform" method="html" />
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="/" >
At least one Dependency Pair of this SCC can be strictly oriented.<BR/>
    <BR/>
    <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="AfsSccProof/OrientedRules" />
    <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="AfsSccProof/Pathorder" />
    <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="AfsSccProof/SccProofInfo/NewSccs" />
    <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="AfsSccProof/AFS" />
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="OrientedRules" >
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(child::Rule) = 0" >No rules need to be oriented.<BR/>
    </xsl:if>
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(child::Rule) > 0" >
      <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(child::Rule) = 1" >The following rule can be oriented:</xsl:if>
      <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(child::Rule) > 1" >The following rules can be oriented:</xsl:if>
      <BLOCKQUOTE>
        <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="Rule" />
      </BLOCKQUOTE>
    </xsl:if>
    <BR/>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Pathorder" >Used ordering: <xsl:value-of xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="OrderName" /> with <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(KBO)=0" >
      <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="child::*/child::*" />
    </xsl:if>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="NewSccs" >
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(child::SCC) = 0" > resulting in no new SCCs.</xsl:if>
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(child::SCC) = 1" > resulting in one new SCC.</xsl:if>
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(child::SCC) > 1" > resulting in string(count(child::SCC)) new SCCs.</xsl:if>
    <BR/>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="AFS[@trivial = &quot;yes&quot;]" >Used Argument Filtering System: trivial</xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="AFS[@trivial = &quot;no&quot;]" >Used Argument Filtering System: <BLOCKQUOTE>
      <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="Rules/Rule" />
    </BLOCKQUOTE>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Rule" >
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(Condition/Rule) > 0" >
      <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="Condition" />
    </xsl:if>
    <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="Term[1]" /> -> <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="Term[2]" />
    <BR/>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Condition" >
    <xsl:for-each xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="Rule" >
      <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select=".." />
      <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="not(position() = last())" >
        <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform">, </xsl:text>
      </xsl:if>
    </xsl:for-each>
    <xsl:text xmlns:xsl="http://www.w3.org/1999/XSL/Transform"> |  </xsl:text>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="PoWithoutStatus" >Precedence: <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="@trivial = &quot;yes&quot;" >
      <BR/>
      <BLOCKQUOTE>trivial</BLOCKQUOTE>
    </xsl:if>
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="@trivial = &quot;no&quot;" >
      <BLOCKQUOTE>
        <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" mode="P" select="Chain" />
      </BLOCKQUOTE>
    </xsl:if>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="QoWithoutStatus" >Quasi Precedence: <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="@trivial = &quot;yes&quot;" >
      <BLOCKQUOTE>trivial</BLOCKQUOTE>
    </xsl:if>
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="@trivial = &quot;no&quot;" >
      <BLOCKQUOTE>
        <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="not(count(Chain) = 0)" >
          <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" mode="Q" select="Chain" />
        </xsl:if>
      </BLOCKQUOTE>
    </xsl:if>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="PoWithStatus" >Precedence: <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="@trivial = &quot;yes&quot;" >
      <BR/>
      <BLOCKQUOTE>trivial</BLOCKQUOTE>
    </xsl:if>
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="@trivial = &quot;no&quot;" >
      <BLOCKQUOTE>
        <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" mode="P" select="Chain" />
      </BLOCKQUOTE>
    </xsl:if>
    <BR/>Status:<BR/>
    <BLOCKQUOTE>
      <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(*/Status) = count(*/Status/Trivial)" >Trivial<BR/>
      </xsl:if>
      <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="not(count(*/Status) = count(*/Status/Trivial))" >
        <xsl:for-each xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="PoSElem" >
          <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(Status/Trivial)=0" >
            <xsl:value-of xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="PoElem/Name" />: <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="Status" />
            <BR/>
          </xsl:if>
        </xsl:for-each>
      </xsl:if>
    </BLOCKQUOTE>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="QoWithStatus" >Quasi Precedence: <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="@trivial = &quot;yes&quot;" >
      <BLOCKQUOTE>trivial</BLOCKQUOTE>
    </xsl:if>
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="@trivial = &quot;no&quot;" >
      <BLOCKQUOTE>
        <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="not(count(Chain) = 0)" >
          <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" mode="Q" select="Chain" />
        </xsl:if>
      </BLOCKQUOTE>
    </xsl:if>
    <BR/>Status:<BR/>
    <BLOCKQUOTE>
      <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(*/Status) = count(*/Status/Trivial)" >Trivial<BR/>
      </xsl:if>
      <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="not(count(*/Status) = count(*/Status/Trivial))" >
        <xsl:for-each xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="PoSElem" >
          <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(Status/Trivial)=0" >
            <xsl:value-of xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="PoElem/Name" />: <xsl:apply-templates xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="Status" />
            <BR/>
          </xsl:if>
        </xsl:for-each>
      </xsl:if>
    </BLOCKQUOTE>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" mode="P" match="Chain" >
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(ChainElem) > 1" >
      <xsl:for-each xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="ChainElem" >
        <xsl:value-of xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="." />
        <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="not(position() = last())" > > </xsl:if>
      </xsl:for-each>
      <BR/>
    </xsl:if>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" mode="Q" match="Chain" >
    <xsl:for-each xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="ChainElem" >
      <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="not(count(../../descendant::QoElem[Name=current()]/Equiv/Name) = 0)" >{<xsl:value-of xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="." />, <xsl:for-each xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="../../descendant::QoElem[Name=current()]/Equiv/Name" >
          <xsl:value-of xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="." />
          <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="not(position() = last())" >, </xsl:if>
        </xsl:for-each>}</xsl:if>
      <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="(count(../../descendant::QoElem[Name=current()]/Equiv/Name) = 0) and (not(count(../ChainElem) = 1))" >
        <xsl:value-of xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="." />
      </xsl:if>
      <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="not(position() = last())" > > </xsl:if>
      <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="(position() = last()) and (not(position() = 1))" >
        <BR/>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>
  <xsl:template xmlns:xsl="http://www.w3.org/1999/XSL/Transform" match="Status" >
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(Multi) = 1" >multiset</xsl:if>
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(Flat) = 1" >flat</xsl:if>
    <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="count(Perm) = 1" >[<xsl:for-each xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="Perm/IntArray/Int" >
        <xsl:value-of xmlns:xsl="http://www.w3.org/1999/XSL/Transform" select="." />
        <xsl:if xmlns:xsl="http://www.w3.org/1999/XSL/Transform" test="not(position() = last())" >, </xsl:if>
      </xsl:for-each>]</xsl:if>
  </xsl:template>
</xsl:stylesheet>
