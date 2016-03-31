package com.thore.L2SMT;

import java.util.*;


public class Z3OutputParser {
	private List<String> output;

	public Z3OutputParser(List<String> output) {
		this.output = output;
	}

	public boolean isSat() {
		if (output.size() < 1) return false;

		if (!output.get(0).toLowerCase().equals("sat")) return false;


		return true;
	}

	@Override
	public String toString() {
		boolean sat = isSat();

		if (sat) {
			return "SATISFABLE! :)";
		} else {
			return "unsat.. :(\n" + output.toString();
		}
	}
}