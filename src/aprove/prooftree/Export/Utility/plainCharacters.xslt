<?xml version="1.0" encoding="iso-8859-1"?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
                version="2.0">

    <xsl:template name="forall">
        <xsl:text>\/</xsl:text>
    </xsl:template>

    <xsl:template name="exists">
        <xsl:text>E</xsl:text>
    </xsl:template>

    <xsl:template name="minus">
        <xsl:text>-</xsl:text>
    </xsl:template>

    <xsl:template name="plus">
        <xsl:text>+</xsl:text>
    </xsl:template>

    <xsl:template name="times">
        <xsl:text>*</xsl:text>
    </xsl:template>

    <xsl:template name="rArr">
        <xsl:text>==&gt;</xsl:text>
    </xsl:template>

    <xsl:template name="sup">
        <xsl:param name="value" />
        <xsl:text>^</xsl:text>
        <xsl:value-of select="$value" />
    </xsl:template>
    
</xsl:stylesheet>