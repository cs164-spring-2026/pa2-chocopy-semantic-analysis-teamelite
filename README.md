package chocopy.pa2;

import chocopy.common.analysis.AbstractNodeAnalyzer;
import chocopy.common.analysis.SymbolTable;
import chocopy.common.analysis.types.*;
import chocopy.common.astnodes.*;

import java.util.*;

/**
* Type-checks a ChocoPy AST that has already passed semantic analysis.
*
* Annotates every expression node with its inferred type via setInferredType().
* Reports type errors with appropriate error-recovery types (as per spec §5.3.2).
*
* Assumptions (guaranteed by DeclarationAnalyzer):
*  - No duplicate declarations.
*  - All class names and type annotations are valid.
*  - The class hierarchy is fully built.
     */
     public class TypeChecker extends AbstractNodeAnalyzer<Type> {

/** Current (innermost) symbol table. */
private SymbolTable<Type> sym;
/** Global symbol table (for GlobalDecl lookups). */
private final SymbolTable<Type> globalSym;
/** Class hierarchy for subtyping and member lookup. */
private final ClassHierarchy hierarchy;
/** Error collector. */
private final Errors errors;

/** Expected return type of the innermost enclosing function (null = top level). */
private ValueType currentReturnType = null;
/** Name of the class whose method we're currently analyzing. */
private String currentClassName = null;

public TypeChecker(SymbolTable<Type> globalSymbols,
ClassHierarchy hierarchy,
Errors errors) {
this.sym        = globalSymbols;
this.globalSym  = globalSymbols;
this.hierarchy  = hierarchy;
this.errors     = errors;
}

// ------------------------------------------------------------------
//  Helpers
// ------------------------------------------------------------------

private void err(Node node, String fmt, Object... args) {
errors.semError(node, fmt, args);
}

/** Returns actual as ValueType, or OBJECT_TYPE if it can't be cast. */
private ValueType toValueType(Type t) {
if (t instanceof ValueType) return (ValueType) t;
return (ValueType) Type.OBJECT_TYPE;
}

/** True if actual conforms to expected. */
private boolean conforms(Type actual, Type expected) {
if (!(actual instanceof ValueType) || !(expected instanceof ValueType)) return false;
return hierarchy.isSubtypeOf((ValueType) actual, (ValueType) expected);
}

/** Returns the class name if t is a ClassValueType, else null. */
private String className(Type t) {
if (t instanceof ClassValueType) return t.toString();
return null;
}

private boolean isIntType(Type t)  { return Type.INT_TYPE.equals(t);  }
private boolean isBoolType(Type t) { return Type.BOOL_TYPE.equals(t); }
private boolean isStrType(Type t)  { return Type.STR_TYPE.equals(t);  }
private boolean isNoneType(Type t) { return Type.NONE_TYPE.equals(t); }

private boolean isIntCompatible(Type t) {
return isIntType(t) || isBoolType(t);
}

private boolean isPrimitive(Type t) {
return isIntType(t) || isBoolType(t) || isStrType(t);
}

// ------------------------------------------------------------------
//  Program
// ------------------------------------------------------------------

@Override
public Type analyze(Program program) {
for (Declaration decl : program.declarations) {
decl.dispatch(this);
}
for (Stmt stmt : program.statements) {
stmt.dispatch(this);
}
return null;
}

// ------------------------------------------------------------------
//  Declarations
// ------------------------------------------------------------------

@Override
public Type analyze(VarDef varDef) {
// Type-check the initial value against the declared type
Type declaredType = ValueType.annotationToValueType(varDef.var.type);
Type valueType    = varDef.value.dispatch(this);

    if (!conforms(valueType, declaredType)) {
        err(varDef.value,
            "Expected type `%s`; got type `%s`", declaredType, valueType);
    }
    return null;
}

@Override
public Type analyze(FuncDef funcDef) {
ValueType oldReturnType  = currentReturnType;
String    oldClassName   = currentClassName;
// currentClassName is preserved for nested functions (they share the outer class)
currentReturnType = ValueType.annotationToValueType(funcDef.returnType);

    SymbolTable<Type> outerSym = sym;
    sym = new SymbolTable<>(sym);

    // --- Parameters ---
    for (TypedVar param : funcDef.params) {
        sym.put(param.identifier.name,
                ValueType.annotationToValueType(param.type));
    }

    // --- Local declarations ---
    processLocalDeclarations(funcDef.declarations);

    // --- Body statements ---
    for (Stmt stmt : funcDef.statements) {
        stmt.dispatch(this);
    }

    sym               = outerSym;
    currentReturnType = oldReturnType;
    currentClassName  = oldClassName;
    return null;
}

@Override
public Type analyze(ClassDef classDef) {
String oldClassName = currentClassName;
currentClassName    = classDef.name.name;

    for (Declaration decl : classDef.declarations) {
        decl.dispatch(this);
    }

    currentClassName = oldClassName;
    return null;
}

/** Processes local declarations inside a function body. */
private void processLocalDeclarations(List<Declaration> declarations) {
for (Declaration decl : declarations) {
if (decl instanceof VarDef) {
VarDef vd = (VarDef) decl;
String name = vd.var.identifier.name;
sym.put(name, ValueType.annotationToValueType(vd.var.type));
// Type-check initial value
decl.dispatch(this);
} else if (decl instanceof FuncDef) {
FuncDef fd   = (FuncDef) decl;
String  name = fd.name.name;
// Register function in current scope
List<ValueType> pTypes = new ArrayList<>();
for (TypedVar p : fd.params) {
pTypes.add(ValueType.annotationToValueType(p.type));
}
sym.put(name, new FuncType(pTypes,
ValueType.annotationToValueType(fd.returnType)));
// Recurse
decl.dispatch(this);
} else if (decl instanceof GlobalDecl) {
String name = ((GlobalDecl) decl).variable.name;
Type   t    = globalSym.get(name);
if (t != null && !sym.declares(name)) sym.put(name, t);
} else if (decl instanceof NonLocalDecl) {
String name    = ((NonLocalDecl) decl).variable.name;
Type   t       = sym.get(name); // available from parent scope already
if (t != null && !sym.declares(name)) sym.put(name, t);
}
}
}

@Override
public Type analyze(GlobalDecl decl) { return null; }

@Override
public Type analyze(NonLocalDecl decl) { return null; }

// ------------------------------------------------------------------
//  Statements
// ------------------------------------------------------------------

@Override
public Type analyze(ExprStmt s) {
s.expr.dispatch(this);
return null;
}

@Override
public Type analyze(AssignStmt s) {
Type valueType = s.value.dispatch(this);

    String firstConformanceError = null;

    for (Expr target : s.targets) {
        if (target instanceof Identifier) {
            Identifier id   = (Identifier) target;
            String     name = id.name;
            Type       t    = sym.get(name);

            if (t == null) {
                err(id, "Not a variable: %s", name);
                id.setInferredType(Type.OBJECT_TYPE);
            } else if (t.isFuncType()) {
                err(id, "Not a variable: %s", name);
                id.setInferredType(Type.OBJECT_TYPE);
            } else {
                id.setInferredType(t);
                // Rule 8: cannot assign to outer-scope var without global/nonlocal
                if (!sym.declares(name)) {
                    err(id,
                        "Cannot assign to variable that is not explicitly "
                        + "declared in this scope: %s", name);
                } else if (firstConformanceError == null) {
                    // Check type conformance
                    if (!conforms(valueType, t)) {
                        firstConformanceError = String.format(
                            "Expected type `%s`; got type `%s`", t, valueType);
                    }
                }
            }
        } else if (target instanceof MemberExpr) {
            // Attribute assignment: obj.attr = value
            Type attrType = target.dispatch(this);
            if (firstConformanceError == null && attrType != null
                    && !conforms(valueType, attrType)) {
                firstConformanceError = String.format(
                    "Expected type `%s`; got type `%s`", attrType, valueType);
            }
        } else if (target instanceof IndexExpr) {
            // List element assignment: lst[i] = value
            Type elemType = target.dispatch(this);
            if (firstConformanceError == null && elemType != null
                    && !conforms(valueType, elemType)) {
                firstConformanceError = String.format(
                    "Expected type `%s`; got type `%s`", elemType, valueType);
            }
        } else {
            target.dispatch(this);
            err(target, "Invalid assignment target");
        }
    }

    // Attach conformance error to the whole AssignStmt
    if (firstConformanceError != null) {
        err(s, "%s", firstConformanceError);
    }

    return null;
}

@Override
public Type analyze(ReturnStmt s) {
Type actual;
if (s.value != null) {
actual = s.value.dispatch(this);
} else {
actual = Type.NONE_TYPE;
}

    if (currentReturnType != null && !conforms(actual, currentReturnType)) {
        err(s, "Expected type `%s`; got type `%s`", currentReturnType, actual);
    }
    return null;
}

@Override
public Type analyze(IfStmt s) {
Type condType = s.condition.dispatch(this);
if (!isBoolType(condType)) {
err(s.condition,
"Condition expression cannot be of type `%s`", condType);
}
for (Stmt stmt : s.thenBody) stmt.dispatch(this);
for (Stmt stmt : s.elseBody) stmt.dispatch(this);
return null;
}

@Override
public Type analyze(WhileStmt s) {
Type condType = s.condition.dispatch(this);
if (!isBoolType(condType)) {
err(s.condition,
"Condition expression cannot be of type `%s`", condType);
}
for (Stmt stmt : s.body) stmt.dispatch(this);
return null;
}

@Override
public Type analyze(ForStmt s) {
Type iterableType = s.iterable.dispatch(this);
ValueType elemType;

    if (iterableType instanceof ListValueType) {
        elemType = ((ListValueType) iterableType).elementType;
    } else if (isStrType(iterableType)) {
        elemType = (ValueType) Type.STR_TYPE;
    } else {
        err(s.iterable,
            "Cannot iterate over value of type `%s`", iterableType);
        elemType = (ValueType) Type.OBJECT_TYPE;
    }

    // Look up loop variable
    String name    = s.identifier.name;
    Type   varType = sym.get(name);

    if (varType == null || varType.isFuncType()) {
        err(s.identifier, "Not a variable: %s", name);
        s.identifier.setInferredType(Type.OBJECT_TYPE);
    } else {
        s.identifier.setInferredType(varType);
        if (!conforms(elemType, varType)) {
            err(s, "Expected type `%s`; got type `%s`", varType, elemType);
        }
    }

    for (Stmt stmt : s.body) stmt.dispatch(this);
    return null;
}

// ------------------------------------------------------------------
//  Expressions – Literals
// ------------------------------------------------------------------

@Override
public Type analyze(IntegerLiteral i) {
return i.setInferredType(Type.INT_TYPE);
}

@Override
public Type analyze(BooleanLiteral b) {
return b.setInferredType(Type.BOOL_TYPE);
}

@Override
public Type analyze(StringLiteral s) {
return s.setInferredType(Type.STR_TYPE);
}

@Override
public Type analyze(NoneLiteral n) {
return n.setInferredType(Type.NONE_TYPE);
}

// ------------------------------------------------------------------
//  Expressions – Compound
// ------------------------------------------------------------------

@Override
public Type analyze(Identifier id) {
String name = id.name;
Type   t    = sym.get(name);

    if (t == null) {
        err(id, "Not a variable: %s", name);
        return id.setInferredType(Type.OBJECT_TYPE);
    }
    if (t.isFuncType()) {
        // Function identifiers used as expressions are still given FuncType
        return id.setInferredType(t);
    }
    return id.setInferredType(t);
}

@Override
public Type analyze(UnaryExpr e) {
Type t = e.operand.dispatch(this);

    switch (e.operator) {
        case "-":
            if (!isIntCompatible(t)) {
                err(e, "Cannot apply operator `%s` on type `%s`", e.operator, t);
            }
            return e.setInferredType(Type.INT_TYPE);
        case "not":
            if (!isBoolType(t)) {
                err(e, "Cannot apply operator `%s` on type `%s`", e.operator, t);
            }
            return e.setInferredType(Type.BOOL_TYPE);
        default:
            return e.setInferredType(Type.OBJECT_TYPE);
    }
}

@Override
public Type analyze(BinaryExpr e) {
Type t1 = e.left.dispatch(this);
Type t2 = e.right.dispatch(this);

    switch (e.operator) {

        // --- Arithmetic (int only) ---
        case "-": case "*": case "//": case "%":
            if (!isIntCompatible(t1) || !isIntCompatible(t2)) {
                err(e, "Cannot apply operator `%s` on types `%s` and `%s`",
                    e.operator, t1, t2);
            }
            return e.setInferredType(Type.INT_TYPE);

        // --- Addition: int, str, or list ---
        case "+":
            if (isIntCompatible(t1) && isIntCompatible(t2)) {
                return e.setInferredType(Type.INT_TYPE);
            }
            if (isStrType(t1) && isStrType(t2)) {
                return e.setInferredType(Type.STR_TYPE);
            }
            if (t1 instanceof ListValueType && t2 instanceof ListValueType) {
                if (t1.equals(t2)) {
                    return e.setInferredType(t1);
                }
                // Mismatched list types
                err(e, "Cannot apply operator `%s` on types `%s` and `%s`",
                    e.operator, t1, t2);
                return e.setInferredType(t1);
            }
            // Error recovery: if at least one is int, return int; else object
            err(e, "Cannot apply operator `%s` on types `%s` and `%s`",
                e.operator, t1, t2);
            if (isIntCompatible(t1) || isIntCompatible(t2)) {
                return e.setInferredType(Type.INT_TYPE);
            }
            return e.setInferredType(Type.OBJECT_TYPE);

        // --- Integer comparisons ---
        case "<": case "<=": case ">": case ">=":
            if (!isIntCompatible(t1) || !isIntCompatible(t2)) {
                err(e, "Cannot apply operator `%s` on types `%s` and `%s`",
                    e.operator, t1, t2);
            }
            return e.setInferredType(Type.BOOL_TYPE);

        // --- Equality: must be same comparable type ---
        case "==": case "!=":
            if (!typesAreComparable(t1, t2)) {
                err(e, "Cannot apply operator `%s` on types `%s` and `%s`",
                    e.operator, t1, t2);
            }
            return e.setInferredType(Type.BOOL_TYPE);

        // --- Logical ---
        case "and": case "or":
            if (!isBoolType(t1) || !isBoolType(t2)) {
                err(e, "Cannot apply operator `%s` on types `%s` and `%s`",
                    e.operator, t1, t2);
            }
            return e.setInferredType(Type.BOOL_TYPE);

        // --- Identity ---
        case "is":
            if (isPrimitive(t1) || isPrimitive(t2)) {
                err(e, "Cannot apply operator `%s` on types `%s` and `%s`",
                    e.operator, t1, t2);
            }
            return e.setInferredType(Type.BOOL_TYPE);

        default:
            return e.setInferredType(Type.OBJECT_TYPE);
    }
}

/**
    * Two types are comparable with == / != if both are the same primitive type
    * (int/bool/str, where bool <= int), or both are non-primitive (class/list/None).
      */
      private boolean typesAreComparable(Type t1, Type t2) {
      // Both int-compatible
      if (isIntCompatible(t1) && isIntCompatible(t2)) return true;
      // Both str
      if (isStrType(t1) && isStrType(t2)) return true;
      // Both bool (covered by int-compatible above)
      // Both non-primitive: class types, lists, None
      if (!isPrimitive(t1) && !isPrimitive(t2)) return true;
      return false;
      }

@Override
public Type analyze(IfExpr e) {
Type condType  = e.condition.dispatch(this);
if (!isBoolType(condType)) {
err(e.condition,
"Condition expression cannot be of type `%s`", condType);
}
Type thenType = e.thenExpr.dispatch(this);
Type elseType = e.elseExpr.dispatch(this);
ValueType result = hierarchy.join(toValueType(thenType), toValueType(elseType));
return e.setInferredType(result);
}

@Override
public Type analyze(ListExpr e) {
if (e.elements.isEmpty()) {
return e.setInferredType(Type.EMPTY_TYPE);
}
ValueType elemType = toValueType(e.elements.get(0).dispatch(this));
for (int i = 1; i < e.elements.size(); i++) {
ValueType next = toValueType(e.elements.get(i).dispatch(this));
elemType = hierarchy.join(elemType, next);
}
return e.setInferredType(new ListValueType(elemType));
}

@Override
public Type analyze(IndexExpr e) {
Type listType  = e.list.dispatch(this);
Type indexType = e.index.dispatch(this);

    if (!isIntCompatible(indexType)) {
        err(e.index, "Index is of non-integer type `%s`", indexType);
    }

    if (listType instanceof ListValueType) {
        return e.setInferredType(((ListValueType) listType).elementType);
    }
    if (isStrType(listType)) {
        return e.setInferredType(Type.STR_TYPE);
    }
    // listType is not a list or string
    err(e.list, "Cannot index into type `%s`", listType);
    return e.setInferredType(Type.OBJECT_TYPE);
}

@Override
public Type analyze(MemberExpr e) {
Type objectType = e.object.dispatch(this);
String memberName = e.member.name;
// e.member.inferredType is left null per spec

    String cn = className(objectType);
    if (cn == null) {
        err(e, "Cannot access member `%s` of non-class type `%s`",
            memberName, objectType);
        return e.setInferredType(Type.OBJECT_TYPE);
    }

    // Look for attribute first, then method
    ValueType attrType = hierarchy.getAttribute(cn, memberName);
    if (attrType != null) {
        return e.setInferredType(attrType);
    }
    FuncType methodType = hierarchy.getMethod(cn, memberName);
    if (methodType != null) {
        return e.setInferredType(methodType);
    }

    err(e, "There is no attribute named `%s` in class `%s`", memberName, cn);
    return e.setInferredType(Type.OBJECT_TYPE);
}

@Override
public Type analyze(CallExpr e) {
String funcName  = e.function.name;
Type   symType   = sym.get(funcName);

    if (symType == null) {
        err(e.function, "Not a function or class: %s", funcName);
        for (Expr arg : e.args) arg.dispatch(this);
        return e.setInferredType(Type.OBJECT_TYPE);
    }

    if (!symType.isFuncType()) {
        err(e.function, "Not a function or class: %s", funcName);
        for (Expr arg : e.args) arg.dispatch(this);
        return e.setInferredType(Type.OBJECT_TYPE);
    }

    FuncType funcType = (FuncType) symType;

    // e.function.inferredType: set to the FuncType
    e.function.setInferredType(funcType);

    // Argument count check
    if (e.args.size() != funcType.parameters.size()) {
        err(e, "Expected %d arguments; got %d",
            funcType.parameters.size(), e.args.size());
        for (Expr arg : e.args) arg.dispatch(this);
        return e.setInferredType(funcType.returnType);
    }

    // Argument type checks
    for (int i = 0; i < e.args.size(); i++) {
        Type argType      = e.args.get(i).dispatch(this);
        ValueType expType = funcType.parameters.get(i);
        if (!conforms(argType, expType)) {
            err(e.args.get(i),
                "Expected type `%s`; got type `%s`", expType, argType);
        }
    }

    return e.setInferredType(funcType.returnType);
}

@Override
public Type analyze(MethodCallExpr e) {
// e.method is a MemberExpr: {object, member (=method name)}
Type objectType  = e.method.object.dispatch(this);
String methodName = e.method.member.name;
// e.method.member.inferredType = null (per spec)

    String cn = className(objectType);
    if (cn == null) {
        err(e.method,
            "Cannot call method `%s` on non-class type `%s`",
            methodName, objectType);
        for (Expr arg : e.args) arg.dispatch(this);
        e.method.setInferredType(Type.OBJECT_TYPE);
        return e.setInferredType(Type.OBJECT_TYPE);
    }

    FuncType funcType = hierarchy.getMethod(cn, methodName);
    if (funcType == null) {
        err(e.method,
            "There is no method named `%s` in class `%s`", methodName, cn);
        for (Expr arg : e.args) arg.dispatch(this);
        e.method.setInferredType(Type.OBJECT_TYPE);
        return e.setInferredType(Type.OBJECT_TYPE);
    }

    e.method.setInferredType(funcType);

    // Parameters: skip index 0 (self)
    int expectedArgs = funcType.parameters.size() - 1;
    if (e.args.size() != expectedArgs) {
        err(e, "Expected %d arguments; got %d", expectedArgs, e.args.size());
        for (Expr arg : e.args) arg.dispatch(this);
        return e.setInferredType(funcType.returnType);
    }

    for (int i = 0; i < e.args.size(); i++) {
        Type      argType  = e.args.get(i).dispatch(this);
        ValueType expType  = funcType.parameters.get(i + 1); // skip self
        if (!conforms(argType, expType)) {
            err(e.args.get(i),
                "Expected type `%s`; got type `%s`", expType, argType);
        }
    }

    return e.setInferredType(funcType.returnType);
}
}