package com.thore.output;

import com.thore.language.*;
import java.util.*;
import java.util.regex.*;
import org.apache.commons.lang3.math.*;
import org.apache.logging.log4j.*;


public class Z3 implements TheoremProver {
	private Logger logger = LogManager.getFormatterLogger(getClass().getName());
	private List<String> input, output;
	private String smt;
	private ProcessExecutor p;

	private int toInt(String s) {
		StringBuffer snum = new StringBuffer();

		for (int i = 0; i < s.length(); i++) {
		   char c = s.charAt(i);
		   if (Character.isDigit(c)) {
		   	  snum.append(c);
		   }
		}

		return NumberUtils.toInt(snum.toString());
	}

	public Z3() {
        p = new ProcessExecutor("z3 -in");
	}

	public void solve(SystemState s) { 
		setState(s);
		this.output = p.run(smt);
	}

	public void setState(SystemState s) {
		smt = s.getSMT();
		this.input  = Arrays.asList(smt.split("\n"));
	}

	public String getRawOutput() {
		return output.toString();
	}

	public boolean isSat() {
		for (int i=0; i<output.size(); i++) {
			if (output.get(i).toLowerCase().equals("sat")) return true;
		}

		return false;
	}

	public String findLabel(String label) {
		for (String s : input) {
			if (s.indexOf(label) != -1) return s.replace("(assert (! ","").replace(" :named "+label+"))", "");
		}

		return "";
	}
	
	public Map<String, String> getResolved() {
		String sat_model = null;
		Map<String, String> resolved = new HashMap<>();
        List<String> allMatches = new ArrayList<String>();
        List<String> responses = new ArrayList<String>();
        Matcher m = Pattern.compile("\\[\\?unknown([a-zA-Z]+)\\]").matcher(smt);
        while (m.find()) {
            allMatches.add(m.group(1));
        }

		for (int i=2; i<output.size(); i++) {
			String o = output.get(i);
			for (int j=0; j<allMatches.size(); j++) {
				String u = allMatches.get(j);

				if (o.indexOf("(define-fun "+u, 0) != -1) {
					i++;
					int id = toInt(output.get(i));

					m = Pattern.compile("\\(assert \\(= ([a-zA-Z]+) "+id+"\\)\\)").matcher(smt);
					if (m.find()) {
						resolved.put(u,m.group(1));
					}
				}
			}
		}	

		return resolved;
	}

	public String getWrongVar() {
		StringBuilder sb = new StringBuilder();
		String unsat_core = null;
		if (output.size() > 1) unsat_core = output.get(1);

        Matcher m = Pattern.compile("\\$([a-zA-Z]+)").matcher(smt);
        m.find();
        return m.group(1);
  //       System.out.println(m.group(1));


		// String[] labels = unsat_core.substring(1, unsat_core.length()-1).split(" ");
		// for (int i=0;i<labels.length;i++) {
		// 	sb.append("\n"+i).append("   ").append(findLabel(labels[i]));
		// }		

		// return sb.toString();
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();

		boolean sat = isSat();

		if (sat) {
			sb.append("SAT!\n");
			Map<String, String> r = getResolved();
			System.out.println(r.size()>0 ? r : "");

		} else {
			sb.append("unsat! :(\n");
			
			String unsat_core = null;
			if (output.size() > 1) unsat_core = output.get(1);

			if (unsat_core == null) {
				sb.append("unsat core is not available");
			} else {
				String[] labels = unsat_core.substring(1, unsat_core.length()-1).split(" ");
				sb.append("\nThe conjunction of following formulas is unsatisfable:");
				for (int i=0;i<labels.length;i++) {
					sb.append("\n"+i).append("   ").append(findLabel(labels[i]));
				}
			}

			// System.out.println(output);
		}

		return sb.toString();
	}
}