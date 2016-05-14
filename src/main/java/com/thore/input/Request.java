package com.thore.input;

import com.thore.language.*;
import org.w3c.dom.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.io.StringWriter;
import java.util.*;
import org.apache.logging.log4j.*;

public class Request {
	private Logger logger = LogManager.getFormatterLogger(getClass().getName());
	private boolean multistep = false;

	private List<AbstractLElement> all = new LinkedList<>();
	private List<Attribute> attributes = new LinkedList<>();
	private List<Role> roles = new LinkedList<>();
	private List<DesignSolution> design_solutions = new LinkedList<>();
	private List<RawExpression> costraints = new LinkedList<>();
	private List<List<Binding>> group_bindings = new LinkedList<>();
	private List<Binding> bindings = null;

	public void addDS(DesignSolution ds) {
		all.add(ds);
		design_solutions.add(ds);
	}

	public void addR(Role r) {
		all.add(r);
		roles.add(r);
	}

	public void addA(Attribute a) {
		all.add(a);
		attributes.add(a);
	}

	public void addC(RawExpression c) {
		all.add(c);
		costraints.add(c);
	}

	public void newStep() {
		if (bindings != null) group_bindings.add(bindings);
		logger.debug("New Step");
		bindings = new LinkedList<>();
	}

	public void addB(Binding b) {
		bindings.add(b);
	}

	public void setMultiStep(boolean multistep) {
		this.multistep = multistep;
	}

	public String toL() {
		StringBuilder sb = new StringBuilder("[Preamble]\n");

		for (AbstractLElement e : all) {
			if (!e.getLPreamble().isEmpty()) sb.append(e.getLPreamble());
		}	

		sb.append("\n");

		for (AbstractLElement e : all) {
			if (!e.getLContent().isEmpty()) sb.append(e.getLContent());
		}	

		int i = 0;
		for (List<Binding> group : group_bindings) {
			sb.append("\n\n$$$\n");
			for (Binding b : group) {
				sb.append(b.getLContent());
			}
		}
		return sb.toString();
	}
}