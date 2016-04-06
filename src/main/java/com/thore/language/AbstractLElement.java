package com.thore.language;

import org.w3c.dom.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.io.StringWriter;
import java.util.*;

public abstract class AbstractLElement implements Comparable<AbstractLElement> {
    protected final UUID _UUID;
    protected String id, label, name;
    protected int step = -1;
    protected Element element;

    public AbstractLElement(Element element) {
        this._UUID = UUID.randomUUID();

        this.element = element;
        this.id = element.getAttribute("id");
        this.label = element.getAttribute("label");
        this.name = element.getAttribute("name");

        if (element.hasAttribute("step") && !element.getAttribute("step").toLowerCase().equals("")) {
            this.step = Integer.parseInt(element.getAttribute("step"));
        }
    }

    public String toXML() {
        String xmlString = "";

        try {
            Transformer transformer = TransformerFactory.newInstance().newTransformer();
            // transformer.setOutputProperty(OutputKeys.INDENT, "yes");

            StreamResult result = new StreamResult(new StringWriter());
            DOMSource source = new DOMSource((Node)element);

            transformer.transform(source, result);
    
            xmlString = result.getWriter().toString();
        } catch (Exception ex) {
            System.err.println(ex); // ToDo
        }

        return xmlString;
    }

    
    protected String transType(String type) {
        type = type.toLowerCase();

        if (type.startsWith("int"))         return "Int";
        else if (type.startsWith("real"))   return "Real";
        else if (type.startsWith("bool"))   return "Bool";
        else if (type.startsWith("string")) return "String";
        else if (type.startsWith("ae"))     return "AttrE";
        else if (type.startsWith("ad"))     return "AttrDS";
        else if (type.startsWith("ds"))     return "DS";
        else if (type.startsWith("r"))      return "Role";

        return "";
    }

    
    protected Element firstChild(Element element, String name) {
        NodeList nodes = element.getElementsByTagName(name);

        return (nodes.getLength() > 0 ? (Element)nodes.item(0) : null);
    }

    
    protected String firstChildText(Element element, String name) {
        Element e = firstChild(element, name);

        return (e == null ? "" : e.getTextContent()); 
    }

    
    protected String join(Collection<String> list, String conjunction) {
        StringBuilder sb = new StringBuilder();
        boolean first = true;
        
        for (String item : list) {
            if (first)
                first = false;
            else
                sb.append(conjunction);
            sb.append(item);
        }

        return sb.toString();
    }

    public int compareTo(AbstractLElement e) {
        return this.step - e.step;
    }

    public String decorateL(String content, boolean withLabel) {
        StringBuilder sb = new StringBuilder();

        if (withLabel && label != null && !label.equals("")) {
            sb.append("[").append(label).append("]\n");
        }

        sb.append("//"+this.toXML().replaceAll("\n\t",""));
        sb.append("[#").append(_UUID.toString().replaceAll("-","")).append("]\n");
        sb.append(content).append("\n\n");
        return sb.toString();
    }

    public String getName() {
        return this.name;
    }

    public String getLPreamble() {
        return "";
    }
    public abstract String getLContent();
    public String getLPost() {
        return "";
    }
}