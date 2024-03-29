package com.thore.language;

import org.w3c.dom.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.io.StringWriter;
import org.apache.logging.log4j.*;
import java.util.*;

public class Binding extends AbstractLElement {
    private Logger logger = LogManager.getFormatterLogger(getClass().getName());

	private String role;
	private String consumer, provider;
	private boolean roleUnknown = false, consumerUnknown = false, providerUnknown = false;
	private int unknownNumber = 0;
    private Map<String, DesignSolution> ds_list;

	public Binding(Element e, Map<String, DesignSolution> ds_list) {
		super(e);
        this.ds_list = ds_list;

		if (e != null) {
			role = e.getAttribute("role");
			consumer = e.getAttribute("consumer");
			provider = e.getAttribute("provider");
		}

		if (role.endsWith("?")) { 
			roleUnknown = true;
			unknownNumber++;
		}

		if (consumer.endsWith("?")) { 
			consumerUnknown = true;
			unknownNumber++;
		}

		if (provider.endsWith("?")) { 
			providerUnknown = true;
			unknownNumber++;
		}

        logger.debug("Parsed: %s", toString());
	}

	public String getLContent() {
        StringBuilder sb = new StringBuilder();
        
        // ToDo error 
        if (unknownNumber > 1) {
        	System.err.println("Too many unknown endpoint in Binding:\n" + toXML());
        	System.exit(-1);
        }

        if (!consumerUnknown) { 
            sb.append("IsDS("+consumer+");\n ");
            DesignSolution d = ds_list.get(consumer);

            for (Role r : d.getRoles()) {
                if (r.getPre() != null) sb.append("Precondition(").append(consumer).append(", ").append(r.getName()).append(", ").append(r.getPre().getLContent()).append(");\n");
                if (r.getPost() != null) sb.append("Postcondition(").append(consumer).append(", ").append(r.getName()).append(", ").append(r.getPost().getLContent()).append(");\n");
            }
        }

        if (!providerUnknown) { 
            sb.append("IsDS("+provider+");\n ");
            DesignSolution d = ds_list.get(provider);

            if (d != null) {
                for (Role r : d.getRoles()) {
                    if (r.getPre() != null) sb.append("Precondition(").append(provider).append(", ").append(r.getName()).append(", ").append(r.getPre().getLContent()).append(");\n");
                    if (r.getPost() != null) sb.append("Postcondition(").append(provider).append(", ").append(r.getName()).append(", ").append(r.getPost().getLContent()).append(");\n");
                }
            }
        }

        
        if (!roleUnknown) {
        	sb.append("IsRole("+role+");\n ");
	        if (!consumerUnknown) sb.append("Consumes("+consumer+", "+role+");\n ");
	        if (!providerUnknown) sb.append("Provides("+provider+", "+role+");\n ");
	    }

	    if (!consumerUnknown && !providerUnknown && !roleUnknown) sb.append("Bond("+consumer+", "+provider+", "+role+");\n");

		if (providerUnknown) {
			String uName = provider.replace("?","");
			sb.append(String.format("[?unknown %s]\nEXISTS %s:DS { Precondition(%s, %s, %s) };", uName, uName, uName, consumer, role));
		} else if (consumerUnknown) {
			String uName = consumer.replace("?","");
			sb.append(String.format("[?unknown %s]\nEXISTS %s:DS { Precondition(%s, %s, %s) };", uName, uName, provider, uName, role));
		} else if (roleUnknown) {
			String uName = role.replace("?","");
			sb.append(String.format("[?unknown %3$s]\nEXISTS %3$s:Role { Precondition(%1$s, %2$s, %3$s) && Precondition(%2$s, %1$s, %3$s) && Provides(%1$s, %3$s) && Consumes(%2$s, %3$s) };", provider, consumer, uName));
		} 

        return decorateL(sb.toString(), "C", true);
	}

    public String toString() {
        return  "B:"+consumer+":"+provider+":"+role;
    }	
}