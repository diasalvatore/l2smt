package com.thore.input;

import org.antlr.v4.runtime.*;
import org.w3c.dom.*;
import javax.xml.parsers.*;
import java.io.*;
import java.util.*;
import com.thore.language.*;
import org.apache.logging.log4j.*;

public class XMLRequestParser {
    private static Logger logger = LogManager.getFormatterLogger(XMLRequestParser.class.getName());

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
                    NodeList child_nodes = null, child_nodes2 = null;

                    logger.debug("Parsing %s", element.getNodeName());
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
                            child_nodes = element.getElementsByTagName("step");
                            logger.debug("Found %d steps", child_nodes.getLength());
                            r.newStep();
                            for (int j=0; j<child_nodes.getLength(); j++) {
                                child_nodes2 = ((Element)child_nodes.item(j)).getElementsByTagName("binding");
                                logger.debug("Found %d bindings", child_nodes2.getLength());
                                for (int k=0; k<child_nodes2.getLength(); k++) {
                                    r.addB(new Binding((Element)child_nodes2.item(k)));
                                }
                                r.newStep();
                            }                                
                            break;

                        case "constraints":
                            child_nodes = element.getElementsByTagName("constraint");
                            for (int j=0; j<child_nodes.getLength(); j++) r.addC(new RawExpression((Element)child_nodes.item(j)));
                            break;
                    }
                }
            }
        } catch (Exception ex) {
            System.err.println("XML Parsing error: "+ex.toString());
        }
        return r;
    }
}