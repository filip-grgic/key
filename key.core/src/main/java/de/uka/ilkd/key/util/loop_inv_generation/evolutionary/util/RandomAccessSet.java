package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util;

import java.util.Collection;
import java.util.HashSet;
import java.util.Random;

public class RandomAccessSet<T> extends HashSet<T> {

    public RandomAccessSet() {
        super();
    }

    public RandomAccessSet(Collection<? extends T> c) {
        super(c);
    }

    public T getRandomElement() {
        Random random = new Random();
        int index = random.nextInt(size());

        for (T t : this) {
            if (index == 0) {
                return t;
            }
            index--;
        }
        return null;
    }

    public T removeRandomElement() {
        Random random = new Random();
        int index = random.nextInt(size());
        T removedElement = null;

        for (T t : this) {
            if (index == 0) {
                removedElement = t;
                remove(t);
                break;
            }
            index--;
        }

        return removedElement;
    }

    public RandomAccessSet<T> intersect(RandomAccessSet<? extends T> other) {
        RandomAccessSet<T> result = new RandomAccessSet<>();
        for (T t : other) {
            if (this.contains(t)) {
                result.add(t);
            }
        }
        return result;
    }

    public RandomAccessSet<T> union(RandomAccessSet<? extends T> other) {
        RandomAccessSet<T> result = new RandomAccessSet<>(this);
        result.addAll(other);
        return result;
    }

    public RandomAccessSet<T> minus(RandomAccessSet<? extends T> other) {
        RandomAccessSet<T> result = new RandomAccessSet<>(this);
        for (T t : other) {
            result.remove(t);
        }
        return result;
    }
}
