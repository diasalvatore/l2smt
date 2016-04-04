package com.thore.language;

import org.w3c.dom.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.io.StringWriter;

public class RawExpression extends AbstractLElement {
    private String expression;

    public RawExpression(Element e) {
        super(e);

        if (e != null) {
            expression = e.getTextContent().trim().replaceAll("[\n\t\r]", " ").replaceAll(" +", " ");
        }
    }

    public String getLContent() {
        return expression;
    }

    public String toString() {
        return expression;
    }
}