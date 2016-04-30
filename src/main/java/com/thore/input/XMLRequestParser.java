package com.thore.input;

import org.antlr.v4.runtime.*;
import org.w3c.dom.*;
import javax.xml.parsers.*;
import java.io.*;
import java.util.*;
import com.thore.language.*;

public class XMLRequestParser {
    public static Request parseFile(String pathname) {
        Request r = new Request();
        
        try {            
            DocumentBuilderFactory builderFactory = DocumentBuilderFactory.newInstance();
            DocumentBuilder builder = null;

            builder = builderFactory.newDocumentBuilder();
            Document document = builder.parse(new FileInputStream(pathname));
            Element root_element = document.getDocumentElement();
            NodeList nodes = root_element.getChildNodes();

            r.setMultiStep((root_element.hasAttribute("multistep") && root_element.getAttribute("multistep").toLowerCase().equals("true")));
            
            for (int i=0; i<nodes.getLength(); i++) {
                Node node = nodes.item(i);

                if (node instanceof Element) {
                    Element element = (Element) node;
                    NodeList child_nodes = null;

                    switch (element.getNodeName()) {
                        case "roles":
                            child_nodes = element.getElementsByTagName("role");
                            for (int j=0; j<child_nodes.getLength(); j++) r.addR(new Role((Element)child_nodes.item(j)));
                            break;

                        case "design-solutions":
                            child_nodes = element.getElementsByTagName("design-solution");
                            for (int j=0; j<child_nodes.getLength(); j++) r.addDS(new DesignSolution((Element)child_nodes.item(j)));
                            break;

                        case "attributes":
                            child_nodes = element.getElementsByTagName("attribute");
                            for (int j=0; j<child_nodes.getLength(); j++) r.addA(new Attribute((Element)child_nodes.item(j)));
                            break;

                        case "bindings":
                            child_nodes = element.getElementsByTagName("binding");
                            for (int j=0; j<child_nodes.getLength(); j++) r.addB(new Binding((Element)child_nodes.item(j)));
                            break;

                        case "constraints":
                            child_nodes = element.getElementsByTagName("constraint");
                            for (int j=0; j<child_nodes.getLength(); j++) r.addC(new RawExpression((Element)child_nodes.item(j)));
                            break;
                    }
                }
            }
        } catch (Exception ex) {
            System.err.println(ex.toString());
        }
        return r;
    }
}