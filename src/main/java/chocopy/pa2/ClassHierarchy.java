package chocopy.pa2;

import chocopy.common.analysis.types.*;
import java.util.*;

public class ClassHierarchy {

    public static class ClassInfo {
        public final String name;
        public final String superName;
        public final Map<String, ValueType> attributes = new LinkedHashMap<>();
        public final Map<String, FuncType> methods = new LinkedHashMap<>();

        public ClassInfo(String name, String superName) {
            this.name = name;
            this.superName = superName;
        }
    }

    private final Map<String, ClassInfo> classes = new LinkedHashMap<>();

    public ClassHierarchy() {
        classes.put("object", new ClassInfo("object", null));
        classes.put("int",    new ClassInfo("int", "object"));
        classes.put("bool",   new ClassInfo("bool", "object"));
        classes.put("str",    new ClassInfo("str", "object"));
    }

    public boolean classExists(String name) { return classes.containsKey(name); }

    public void addClass(String name, String superName) {
        if (!classes.containsKey(name)) classes.put(name, new ClassInfo(name, superName));
    }

    public ClassInfo getClassInfo(String name) { return classes.get(name); }
    public String getSuperName(String name) {
        ClassInfo info = classes.get(name);
        return (info != null) ? info.superName : null;
    }

    public boolean isSubclass(String child, String parent) {
        if (child == null || parent == null) return false;
        if ("object".equals(parent)) return true;
        Set<String> visited = new HashSet<>();
        String cur = child;
        while (cur != null && !visited.contains(cur)) {
            if (cur.equals(parent)) return true;
            visited.add(cur);
            ClassInfo info = classes.get(cur);
            cur = (info != null) ? info.superName : null;
        }
        return false;
    }

    public String lcaClass(String a, String b) {
        if (a == null || b == null) return "object";
        if (a.equals(b)) return a;
        List<String> chainA = ancestorChain(a);
        Set<String> visited = new HashSet<>();
        String cur = b;
        while (cur != null && !visited.contains(cur)) {
            if (chainA.contains(cur)) return cur;
            visited.add(cur);
            ClassInfo info = classes.get(cur);
            cur = (info != null) ? info.superName : null;
        }
        return "object";
    }

    private List<String> ancestorChain(String className) {
        List<String> chain = new ArrayList<>();
        Set<String> visited = new HashSet<>();
        String cur = className;
        while (cur != null && !visited.contains(cur)) {
            chain.add(cur);
            visited.add(cur);
            ClassInfo info = classes.get(cur);
            cur = (info != null) ? info.superName : null;
        }
        return chain;
    }

    public boolean isSubtypeOf(ValueType actual, ValueType expected) {
        if (actual == null || expected == null) return false;
        if (actual.equals(expected)) return true;
        if (isObjectType(expected)) return true;

        String ac = getClassName(actual);
        String ec = getClassName(expected);

        if ("<None>".equals(ac)) {
            if (expected instanceof ListValueType) return true;
            if (ec != null) return !ec.equals("int") && !ec.equals("bool") && !ec.equals("str");
            return false;
        }
        if ("<Empty>".equals(ac) && expected instanceof ListValueType) return true;

        if (actual instanceof ListValueType && expected instanceof ListValueType) {
            if (actual.equals(expected)) return true;
            ValueType actElem = ((ListValueType) actual).elementType;
            ValueType expElem = ((ListValueType) expected).elementType;
            String actElemName = getClassName(actElem);
            if ("<None>".equals(actElemName) || "<Empty>".equals(actElemName)) {
                return isSubtypeOf(actElem, expElem);
            }
            return false;
        }

        if (ac != null && ec != null) return isSubclass(ac, ec);
        return false;
    }

    public ValueType join(ValueType t1, ValueType t2) {
        if (t1 == null) return t2;
        if (t2 == null) return t1;
        if (t1.equals(t2)) return t1;

        if (t1 instanceof ListValueType && t2 instanceof ListValueType) {
            ValueType e1 = ((ListValueType) t1).elementType;
            ValueType e2 = ((ListValueType) t2).elementType;
            String ce1 = getClassName(e1);
            String ce2 = getClassName(e2);

            if (("<None>".equals(ce1) || "<Empty>".equals(ce1)) && isSubtypeOf(e1, e2)) return t2;
            if (("<None>".equals(ce2) || "<Empty>".equals(ce2)) && isSubtypeOf(e2, e1)) return t1;

            return new ClassValueType("object");
        }

        String c1 = getClassName(t1);
        String c2 = getClassName(t2);
        boolean t1None  = "<None>".equals(c1);
        boolean t2None  = "<None>".equals(c2);
        boolean t1Empty = "<Empty>".equals(c1);
        boolean t2Empty = "<Empty>".equals(c2);

        if (t1None && t2 instanceof ClassValueType && !isPrimitive(c2)) return t2;
        if (t2None && t1 instanceof ClassValueType && !isPrimitive(c1)) return t1;
        if (t1None && t2None) return t1;

        if ((t1None || t1Empty) && t2 instanceof ListValueType) return t2;
        if ((t2None || t2Empty) && t1 instanceof ListValueType) return t1;

        if (c1 != null && c2 != null) return new ClassValueType(lcaClass(c1, c2));

        return new ClassValueType("object");
    }

    private boolean isObjectType(ValueType t) {
        return (t instanceof ClassValueType) && "object".equals(getClassName(t));
    }

    // 关键修复：绝对安全地获取真实类名，防止 toString() 捣乱
    public String getClassName(ValueType t) {
        if (t instanceof ClassValueType) return t.toString();
        return null;
    }

    private boolean isPrimitive(String cn) {
        return "int".equals(cn) || "bool".equals(cn) || "str".equals(cn);
    }

    public ValueType getAttribute(String className, String attrName) {
        return findMember(className, attrName, false);
    }

    public FuncType getMethod(String className, String methodName) {
        String cur = className;
        Set<String> visited = new HashSet<>();
        while (cur != null && !visited.contains(cur)) {
            visited.add(cur);
            ClassInfo info = classes.get(cur);
            if (info == null) break;
            FuncType ft = info.methods.get(methodName);
            if (ft != null) return ft;
            cur = info.superName;
        }
        return null;
    }

    @SuppressWarnings("unchecked")
    private ValueType findMember(String className, String name, boolean isMethod) {
        String cur = className;
        Set<String> visited = new HashSet<>();
        while (cur != null && !visited.contains(cur)) {
            visited.add(cur);
            ClassInfo info = classes.get(cur);
            if (info == null) break;
            Map<String, ?> map = isMethod ? info.methods : info.attributes;
            Object v = map.get(name);
            if (v != null) return isMethod ? null : (ValueType) v;
            cur = info.superName;
        }
        return null;
    }

    public boolean isInherited(String className, String memberName) {
        String super_ = getSuperName(className);
        if (super_ == null) return false;
        return getAttribute(super_, memberName) != null || getMethod(super_, memberName) != null;
    }

    public boolean isDefinedLocally(String className, String memberName) {
        ClassInfo info = classes.get(className);
        if (info == null) return false;
        return info.attributes.containsKey(memberName) || info.methods.containsKey(memberName);
    }

    public void setAttribute(String className, String attrName, ValueType type) {
        ClassInfo info = classes.get(className);
        if (info != null) info.attributes.put(attrName, type);
    }

    public void setMethod(String className, String methodName, FuncType ft) {
        ClassInfo info = classes.get(className);
        if (info != null) info.methods.put(methodName, ft);
    }
}