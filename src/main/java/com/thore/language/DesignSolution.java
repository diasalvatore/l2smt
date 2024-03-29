package com.thore.language;

import org.w3c.dom.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.io.StringWriter;
import java.util.*;

public class DesignSolution extends AbstractLElement {
    private List<Role> roles = new LinkedList<>();
    private List<Attribute> attributes = new LinkedList<>();

    public DesignSolution(Element e) {
        super(e);

        if (e != null) {
            // attributes
            Node attributes_tag = firstChild(e, "attributes");
            if (attributes_tag != null) {
                NodeList attributes_nodes = element.getElementsByTagName("attribute");

                for (int i=0; i<attributes_nodes.getLength(); i++) {
                    Element attribute_element = (Element)attributes_nodes.item(i);
                    attributes.add(new Attribute(attribute_element));
                }
            }

            // roles
            Node roles_tag = firstChild(e, "roles");
            if (roles_tag != null) {
                NodeList roles_nodes = element.getElementsByTagName("role");

                for (int i=0; i<roles_nodes.getLength(); i++) {
                    Element role_element = (Element)roles_nodes.item(i);
                    roles.add(new Role(role_element));
                }
            }
        }
    }

    public List<Role> getRoles() {
        return roles;
    }

    public String getLPreamble() {
        StringBuilder sb_mine = new StringBuilder();
        StringBuilder sb = new StringBuilder();
        
        sb_mine.append("IsDS("+name+");\n");

        for (Role r : roles) {
            sb_mine.append(r.getType()).append("(").append(name).append(", ").append(r.getName()).append(");\n");
            sb.append(r.getLPreamble());
        }

        for (Attribute a : attributes) {
            String aName = "AD."+name+"."+a.getName();
            sb_mine.append("IsAttrDS(").append(aName).append(");\n");
            sb_mine.append("HasAttr(").append(name).append(", ").append(aName).append(");\n");
            sb_mine.append(aName).append(" == ").append(a.getValue()).append(";\n");
            sb.append(a.getLPreamble());
        }

        return decorateL(sb_mine.toString()+";", "P", false) + sb.toString();
    }

    public String getLContent() {
        return "";
        // StringBuilder sb = new StringBuilder();

        // for (Role r : roles) {
        //     if (r.getPre() != null) sb.append("Precondition(").append(name).append(", ").append(r.getName()).append(", ").append(r.getPre().getLContent()).append(");\n");
        //     if (r.getPost() != null) sb.append("Postcondition(").append(name).append(", ").append(r.getName()).append(", ").append(r.getPost().getLContent()).append(");\n");
        // }

        // return (sb.toString().isEmpty() ? "" : decorateL(sb.toString()+";", "C", false));
    }

    public String toString() {
        return  "DS:"+name+
                " a:"+attributes.toString()+
                " r:"+roles.toString();
    }
}