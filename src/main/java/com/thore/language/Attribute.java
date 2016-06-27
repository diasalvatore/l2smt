package com.thore.language;

import org.w3c.dom.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.io.StringWriter;

public class Attribute extends AbstractLElement {
    private String type, value;

    public Attribute(Element e) {
        super(e);

        if (e != null) {
            // type
            type = transType(e.hasAttribute("type") ? e.getAttribute("type") : "String");

            // value
            value = e.getTextContent();
        }
    }

    public String toString() {
        return  "A:"+name+","+type+","+value;
    }

    public String getLPreamble() {
        return decorateL("Is"+type+"("+name+");", "P", false);
    }

    public String getLContent() {
        return this.name + " == " + this.value + ";\n";
    }

    public String getValue() {
        return value;
    }
}