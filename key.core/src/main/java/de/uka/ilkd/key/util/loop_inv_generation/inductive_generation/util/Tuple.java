package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util;

import java.util.Objects;

public class Tuple<X, Y> {

    private final X first;
    private final Y second;

    public Tuple(X first, Y second) {
        this.first = first;
        this.second = second;
    }

    public X first() {
        return first;
    }

    public Y second() {
        return second;
    }

    @Override
    public String toString() {
        return "(" + first + ", " + second + ")";
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        Tuple<?, ?> that = (Tuple<?, ?>) obj;

        return (Objects.equals(first, that.first) && Objects.equals(second, that.second)) ||
                (Objects.equals(first, that.second) && Objects.equals(second, that.first));
    }

    @Override
    public int hashCode() {
        return 19 * (first.hashCode() + second.hashCode());
    }
}
