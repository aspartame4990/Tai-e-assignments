/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import pascal.taie.util.collection.SetQueue;
import pascal.taie.util.collection.Sets;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        assert entry != null;
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        Queue<JMethod> workList = new SetQueue<>();
        workList.addAll(callGraph.entryMethods);
        assert callGraph.entryMethods.size() == 1;
        while (!workList.isEmpty()) {
            JMethod m = workList.poll();
            if (!callGraph.reachableMethods.contains(m)) {
                callGraph.addReachableMethod(m);
                callGraph.callSitesIn(m).forEach(callSite -> {
                    for (JMethod targetMethod : resolve(callSite)) {
                        CallKind callKind = callSite.isStatic() ? CallKind.STATIC :
                                callSite.isSpecial() ? CallKind.SPECIAL :
                                        callSite.isVirtual() ? CallKind.VIRTUAL :
                                                callSite.isInterface() ? CallKind.INTERFACE :
                                                        CallKind.OTHER;
                        callGraph.addEdge(new Edge<>(callKind, callSite, targetMethod));
                        workList.add(targetMethod);
                    }
                });
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> T = Sets.newSet();
        Subsignature m = callSite.getMethodRef().getSubsignature();
        JClass declaringClass = callSite.getMethodRef().getDeclaringClass();
        if (callSite.isStatic()) {
            T.add(declaringClass.getDeclaredMethod(m));
        }
        if (callSite.isSpecial()) {
            JMethod targetMethod = dispatch(declaringClass, m);
            if (targetMethod != null) T.add(targetMethod);
        }
        if (callSite.isVirtual()) {
            Queue<JClass> queue = new SetQueue<>();
            queue.add(declaringClass);
            Set<JClass> visited = Sets.newSet();
            while (!queue.isEmpty()) {
                JClass jClass = queue.poll();
                if (visited.contains(jClass)) {
                    continue;
                }
                visited.add(jClass);
                assert !jClass.isInterface();
                assert hierarchy.getDirectSubinterfacesOf(jClass).isEmpty();
                assert hierarchy.getDirectImplementorsOf(jClass).isEmpty();
                JMethod targetMethod = dispatch(jClass, m);
                if (targetMethod != null) T.add(targetMethod);
                for (JClass subClass : hierarchy.getDirectSubclassesOf(jClass)) {
                    if (!visited.contains(subClass)) {
                        queue.add(subClass);
                    }
                }
            }
        }
        if (callSite.isInterface()) {
            Queue<JClass> queue = new SetQueue<>();
            queue.add(declaringClass);
            Set<JClass> visited = Sets.newSet();
            while (!queue.isEmpty()) {
                JClass jClass = queue.poll();
                if (visited.contains(jClass)) {
                    continue;
                }
                visited.add(jClass);
                if (!jClass.isInterface()) {
                    assert hierarchy.getDirectSubinterfacesOf(jClass).isEmpty();
                    assert hierarchy.getDirectImplementorsOf(jClass).isEmpty();
                    JMethod targetMethod = dispatch(jClass, m);
                    if (targetMethod != null) T.add(targetMethod);
                    for (JClass subClass : hierarchy.getDirectSubclassesOf(jClass)) {
                        if (!visited.contains(subClass)) {
                            queue.add(subClass);
                        }
                    }
                } else {
                    Set<JClass> allSubClasses = Sets.newSet();
                    assert hierarchy.getDirectSubclassesOf(jClass).isEmpty();
                    allSubClasses.addAll(hierarchy.getDirectSubinterfacesOf(jClass));
                    allSubClasses.addAll(hierarchy.getDirectImplementorsOf(jClass));
                    for (JClass subClass : allSubClasses) {
                        if (!visited.contains(subClass)) {
                            queue.add(subClass);
                        }
                    }
                }
            }
        }
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod method = jclass.getDeclaredMethod(subsignature);
        if (method != null && !method.isAbstract()) {
            return method;
        }
        if (method != null && method.isAbstract()) {
            return null;
        }
        JClass superClass = jclass.getSuperClass();
        if (superClass != null) {
            return dispatch(superClass, subsignature);
        }
        return null;
    }
}

class A {
    void hello() {
        System.out.println("Hello A");
    }
}

abstract class B extends A {
    abstract void hello();
}

class C extends B {
    void hello() {
        System.out.println("Hello C");
    }
}

class Main {
    public static void main(String[] args) {
        B b = new C();
        b.hello();
    }
}