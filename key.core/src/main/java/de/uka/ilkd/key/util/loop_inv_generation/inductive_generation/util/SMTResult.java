package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util;

import java.util.Map;

public class SMTResult {

    private final boolean valid;
    private final Map<String, Integer> counterexample;

    public SMTResult(boolean valid, Map<String, Integer> counterexample) {
        this.valid = valid;
        this.counterexample = counterexample;
    }

    public boolean isValid() {
        return valid;
    }

    public Map<String, Integer> getCounterexample() {
        return counterexample;
    }

    @Override
    public String toString() {
        StringBuilder result = new StringBuilder();
        result.append("Result:\t\t\t").append(valid ? "Valid" : "Invalid").append("\n").append(counterexample.isEmpty() ? "" : "Counterexample:\t|");
        for (String s : counterexample.keySet()) {
            result.append(s).append(" = ").append(counterexample.get(s)).append("|");
        }
        result.append(valid ? "" : "\n");
        return result.toString();
    }
}
