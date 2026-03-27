package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util;

import org.key_project.util.collection.Pair;

import java.util.List;
import java.util.Map;

public class SMTResult {

    private final boolean valid;
    private final Map<String, Integer> counterexampleConstants;
    private final Map<String, List<Pair<Integer,Integer>>> counterexampleArrays;

    public SMTResult(boolean valid, Map<String, Integer> counterexampleConstants,
                     Map<String, List<Pair<Integer,Integer>>> counterexampleArrays) {
        this.valid = valid;
        this.counterexampleConstants = counterexampleConstants;
        this.counterexampleArrays = counterexampleArrays;
    }

    public boolean isValid() {
        return valid;
    }

    public Map<String, Integer> getCounterexampleConstants() {
        return counterexampleConstants;
    }

    public Map<String, List<Pair<Integer,Integer>>> getCounterexampleArrays() {
        return counterexampleArrays;
    }

    @Override
    public String toString() {
        StringBuilder result = new StringBuilder();
        result.append("Result:\t\t\t").append(valid ? "Valid" : "Invalid").append("\n").append(counterexampleConstants.isEmpty() ? "" : "Counterexample:\t|");
        for (String s : counterexampleConstants.keySet()) {
            result.append(s).append(" = ").append(counterexampleConstants.get(s)).append("|");
        }
        result.append(valid ? "" : "\n");
        return result.toString();
    }
}
