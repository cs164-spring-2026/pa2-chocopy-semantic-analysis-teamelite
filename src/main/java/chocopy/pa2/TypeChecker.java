package chocopy.pa2;

import chocopy.common.analysis.AbstractNodeAnalyzer;
import chocopy.common.analysis.SymbolTable;
import chocopy.common.analysis.types.*;
import chocopy.common.astnodes.*;

import java.util.*;

public class TypeChecker extends AbstractNodeAnalyzer<Type> {

    private SymbolTable<Type> sym;
    private final SymbolTable<Type> globalSym;
    private final ClassHierarchy hierarchy;
    private final Errors errors;

    private ValueType currentReturnType = null;
    private String currentClassName = null;

    public TypeChecker(SymbolTable<Type> globalSymbols, ClassHierarchy hierarchy, Errors errors) {
        this.sym = globalSymbols;
        this.globalSym = globalSymbols;
        this.hierarchy = hierarchy;
        this.errors = errors;
    }

    private void err(Node node, String fmt, Object... args) { errors.semError(node, fmt, args); }

    private ValueType toValueType(Type t) {
        if (t instanceof ValueType) return (ValueType) t;
        return (ValueType) Type.OBJECT_TYPE;
    }

    private boolean conforms(Type actual, Type expected) {
        if (!(actual instanceof ValueType) || !(expected instanceof ValueType)) return false;
        return hierarchy.isSubtypeOf((ValueType) actual, (ValueType) expected);
    }

// 防弹版 className

    private String className(Type t) {

        if (t instanceof ClassValueType) return t.toString();

        return null;

    }



    private boolean isIntType(Type t) { return Type.INT_TYPE.equals(t); }

    private boolean isBoolType(Type t) { return Type.BOOL_TYPE.equals(t); }

    private boolean isStrType(Type t) { return Type.STR_TYPE.equals(t); }



    private boolean isPrimitive(Type t) {

        return isIntType(t) || isBoolType(t) || isStrType(t);

    }



    @Override

    public Type analyze(Program program) {

        for (Declaration decl : program.declarations) decl.dispatch(this);

        for (Stmt stmt : program.statements) stmt.dispatch(this);

        return null;

    }



    @Override

    public Type analyze(VarDef varDef) {

        Type declaredType = ValueType.annotationToValueType(varDef.var.type);

        Type valueType = varDef.value.dispatch(this);



        if (!conforms(valueType, declaredType)) {

            err(varDef.value, "Expected type %s; got type %s", declaredType, valueType);

        }

        return null;

    }



    private ValueType getSafeReturnType(TypeAnnotation annotation) {

        if (annotation == null) return new ClassValueType("<None>");

        return ValueType.annotationToValueType(annotation);

    }



    @Override
    public Type analyze(FuncDef funcDef) {
        ValueType oldReturnType = currentReturnType;
        String oldClassName = currentClassName;
        currentReturnType = getSafeReturnType(funcDef.returnType);

        // --- 👇 新增：面向对象专属检查 (Method Checks) 👇 ---
        if (currentClassName != null) {
            // 1. 检查 self 参数：必须有参数，且第一个参数必须是当前类
            if (funcDef.params.isEmpty()) {
                err(funcDef.name, "First parameter of the following method must be of the enclosing class: %s", funcDef.name.name);
            } else {
                ValueType firstParamType = ValueType.annotationToValueType(funcDef.params.get(0).type);
                if (!firstParamType.className().equals(currentClassName)) {
                    err(funcDef.name, "First parameter of the following method must be of the enclosing class: %s", funcDef.name.name);
                }
            }

            // 2. (可选/重要) 如果你的父类也有这个方法，这里需要检查签名是否一致！
            // 因为 ChocoPy 规定 Override 必须保持参数个数、类型和返回值一模一样。
            // 如果不一样，抛出: err(funcDef.name, "Method overridden with different type signature: %s", funcDef.name.name);
        }

        SymbolTable<Type> outerSym = sym;
        sym = new SymbolTable<>(sym);

        for (TypedVar param : funcDef.params) {
            sym.put(param.identifier.name, ValueType.annotationToValueType(param.type));
        }
        processLocalDeclarations(funcDef.declarations);

        // 正常遍历所有的 statements
        for (Stmt stmt : funcDef.statements) {
            stmt.dispatch(this);
        }

        // --- 👇 新增的返回值路径检查逻辑 👇 ---
        // 如果期望返回值不是 <None> (且不为空)，则必须做控制流检查
        if (currentReturnType != null && !currentReturnType.className().equals("<None>")) {
            if (!hasReturn(funcDef.statements)) {
                // 🚨 注意：错误一定要挂载 funcDef.name (Identifier) 上，而不是 funcDef 上
                err(funcDef.name, "All paths in this function/method must have a return statement: %s", funcDef.name.name);
            }
        }
        // --- 👆 新增逻辑结束 👆 ---

        sym = outerSym;
        currentReturnType = oldReturnType;
        currentClassName = oldClassName;
        return null;
    }

    @Override
    public Type analyze(ClassDef classDef) {
        String oldClassName = currentClassName;
        currentClassName = classDef.name.name;
        for (Declaration decl : classDef.declarations) decl.dispatch(this);
        currentClassName = oldClassName;
        return null;
    }

    private void processLocalDeclarations(List<Declaration> declarations) {

        // Pass 1: 先把当前作用域所有的“名字”和“类型”都登记在册（绝不深入内部）
        for (Declaration decl : declarations) {
            if (decl instanceof VarDef) {
                VarDef vd = (VarDef) decl;
                sym.put(vd.var.identifier.name, ValueType.annotationToValueType(vd.var.type));
            } else if (decl instanceof FuncDef) {
                FuncDef fd = (FuncDef) decl;
                List<ValueType> pTypes = new ArrayList<>();
                for (TypedVar p : fd.params) {
                    pTypes.add(ValueType.annotationToValueType(p.type));
                }
                sym.put(fd.name.name, new FuncType(pTypes, getSafeReturnType(fd.returnType)));
            } else if (decl instanceof GlobalDecl) {
                String name = ((GlobalDecl) decl).variable.name;
                Type t = globalSym.get(name);
                if (t != null && !sym.declares(name)) sym.put(name, t);
            } else if (decl instanceof NonLocalDecl) {
                String name = ((NonLocalDecl) decl).variable.name;
                // sym.get 会自动向外层作用域链查找，因为这是在分析器里，外层肯定已经建好表了
                Type t = sym.get(name);
                if (t != null && !sym.declares(name)) sym.put(name, t);
            }
        }

        // Pass 2: 等所有声明都登记完毕后，再统一下发 dispatch，进入 AST 节点内部检查
        for (Declaration decl : declarations) {
            decl.dispatch(this);
        }
    }

    @Override public Type analyze(GlobalDecl decl) { return null; }

    @Override public Type analyze(NonLocalDecl decl) { return null; }



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

                Identifier id = (Identifier) target;

                Type t = sym.get(id.name);



                if (t == null || t.isFuncType()) {

                    err(id, "Not a variable: %s", id.name);

                    id.setInferredType(Type.OBJECT_TYPE);

                } else {

                    id.setInferredType(t);

                    if (firstConformanceError == null && !conforms(valueType, t)) {

                        firstConformanceError = String.format("Expected type `%s`; got type `%s`", t, valueType);

                    }

                }

            } else if (target instanceof MemberExpr || target instanceof IndexExpr) {



                Type targetType = target.dispatch(this);





                if (target instanceof IndexExpr) {

                    IndexExpr idxTarget = (IndexExpr) target;

                    Type baseType = idxTarget.list.getInferredType();





                    if (!(baseType instanceof ListValueType)) {

                        err(idxTarget, "`%s` is not a list type", baseType);

                    }

                }



                if (firstConformanceError == null && targetType != null && !conforms(valueType, targetType)) {

                    firstConformanceError = String.format("Expected type `%s`; got type `%s`", targetType, valueType);

                }

            } else {



                target.dispatch(this);



                err(target, "Invalid assignment target");



            }



        }







        if (firstConformanceError != null) err(s, "%s", firstConformanceError);



        return null;



    }



    @Override
    public Type analyze(ReturnStmt e) {
        // e.value 为 null 代表代码里写的是单独的 "return"
        if (e.value == null) {
            // 如果函数期望的不是 None，但却隐式返回了 None
            if (currentReturnType != null && !conforms(Type.NONE_TYPE, currentReturnType)) {
                // 🚨 注意这里的格式：没有 type，没有尖括号
                err(e, "Expected type `%s`; got `None`", currentReturnType.className());
            }
        } else {
            // 代码里写的是 "return value"
            Type actualType = e.value.dispatch(this);

            // 如果返回值类型与预期的不兼容
            if (currentReturnType != null && !conforms(actualType, currentReturnType)) {
                // 🚨 注意这里的格式：有 type，如果有 NoneLiteral 它自带的 className 就是 <None>
                err(e, "Expected type `%s`; got type `%s`",
                        currentReturnType.className(), actualType.className());
            }
        }

        return null; // Statement 节点本身不需要返回类型
    }
    @Override

    public Type analyze(IfStmt s) {

        Type condType = s.condition.dispatch(this);

        if (!isBoolType(condType)) err(s.condition, "Condition expression cannot be of type `%s`", condType);

        for (Stmt stmt : s.thenBody) stmt.dispatch(this);

        for (Stmt stmt : s.elseBody) stmt.dispatch(this);

        return null;

    }



    @Override

    public Type analyze(WhileStmt s) {

        Type condType = s.condition.dispatch(this);

        if (!isBoolType(condType)) err(s.condition, "Condition expression cannot be of type `%s`", condType);

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

            err(s.iterable, "Cannot iterate over value of type `%s`", iterableType);

            elemType = (ValueType) Type.OBJECT_TYPE;

        }



        Type varType = sym.get(s.identifier.name);

        if (varType == null || varType.isFuncType()) {

            err(s.identifier, "Not a variable: %s", s.identifier.name);

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



    @Override public Type analyze(IntegerLiteral i) { return i.setInferredType(Type.INT_TYPE); }

    @Override public Type analyze(BooleanLiteral b) { return b.setInferredType(Type.BOOL_TYPE); }

    @Override public Type analyze(StringLiteral s) { return s.setInferredType(Type.STR_TYPE); }

    @Override public Type analyze(NoneLiteral n) { return n.setInferredType(new ClassValueType("<None>")); }



    @Override

    public Type analyze(Identifier id) {

        Type t = sym.get(id.name);

        if (t == null) {

            err(id, "Not a variable: %s", id.name);

            return id.setInferredType(Type.OBJECT_TYPE);

        }

        return id.setInferredType(t);

    }



    @Override

    public Type analyze(UnaryExpr e) {

        Type t = e.operand.dispatch(this);

        switch (e.operator) {

            case "-":

                if (!isIntType(t)) err(e, "Cannot apply operator `%s` on type `%s`", e.operator, t);

                return e.setInferredType(Type.INT_TYPE);

            case "not":

                if (!isBoolType(t)) err(e, "Cannot apply operator `%s` on type `%s`", e.operator, t);

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

            case "-": case "*": case "//": case "%":

                if (!isIntType(t1) || !isIntType(t2)) {

                    err(e, "Cannot apply operator `%s` on types `%s` and `%s`", e.operator, t1, t2);

                }

                return e.setInferredType(Type.INT_TYPE);



            case "+":

// 1. 合法情况：整型相加

                if (isIntType(t1) && isIntType(t2)) return e.setInferredType(Type.INT_TYPE);



// 2. 合法情况：字符串相加

                if (isStrType(t1) && isStrType(t2)) return e.setInferredType(Type.STR_TYPE);



// 3. 合法情况：明确的列表类型相加 (不包含 <Empty>)

                if (t1 instanceof ListValueType && t2 instanceof ListValueType) {

                    ValueType elemType1 = ((ListValueType) t1).elementType;

                    ValueType elemType2 = ((ListValueType) t2).elementType;

                    ValueType lcaType = hierarchy.join(elemType1, elemType2);

                    return e.setInferredType(new ListValueType(lcaType));

                }



// 4. 报错：以上全不符合，抛出类型错误

                err(e, "Cannot apply operator `%s` on types `%s` and `%s`", e.operator, t1, t2);



// 5. 错误恢复：如果有一边是 int，兜底推导为 int；否则兜底为 object

                if (isIntType(t1) || isIntType(t2)) return e.setInferredType(Type.INT_TYPE);

                return e.setInferredType(Type.OBJECT_TYPE);



            case "<": case "<=": case ">": case ">=":

                if (!isIntType(t1) || !isIntType(t2)) {

                    err(e, "Cannot apply operator `%s` on types `%s` and `%s`", e.operator, t1, t2);

                }

                return e.setInferredType(Type.BOOL_TYPE);



            case "==": case "!=":

                if (!typesAreComparable(t1, t2)) {

                    err(e, "Cannot apply operator `%s` on types `%s` and `%s`", e.operator, t1, t2);

                }

                return e.setInferredType(Type.BOOL_TYPE);



            case "and": case "or":

                if (!isBoolType(t1) || !isBoolType(t2)) {

                    err(e, "Cannot apply operator `%s` on types `%s` and `%s`", e.operator, t1, t2);

                }

                return e.setInferredType(Type.BOOL_TYPE);



            case "is":

// 显式检查值类型，避免 isPrimitive 遗漏 str 的情况

                boolean t1IsValueType = isIntType(t1) || isBoolType(t1) || isStrType(t1);

                boolean t2IsValueType = isIntType(t2) || isBoolType(t2) || isStrType(t2);



                if (t1IsValueType || t2IsValueType) {

                    err(e, "Cannot apply operator `%s` on types `%s` and `%s`", e.operator, t1, t2);

                }

                return e.setInferredType(Type.BOOL_TYPE);



            default:

                return e.setInferredType(Type.OBJECT_TYPE);

        }

    }



    private boolean typesAreComparable(Type t1, Type t2) {

// 极其严格的匹配：仅限 (int, int), (bool, bool), (str, str)

        if (isIntType(t1) && isIntType(t2)) return true;

        if (isBoolType(t1) && isBoolType(t2)) return true;

        if (isStrType(t1) && isStrType(t2)) return true;



// 其他任何情况（跨类型、对象、列表）都不允许使用 ==

        return false;

    }



    @Override

    public Type analyze(IfExpr e) {

        Type condType = e.condition.dispatch(this);

        if (!isBoolType(condType)) err(e.condition, "Condition expression cannot be of type `%s`", condType);

        Type thenType = e.thenExpr.dispatch(this);

        Type elseType = e.elseExpr.dispatch(this);

        ValueType result = hierarchy.join(toValueType(thenType), toValueType(elseType));

        return e.setInferredType(result);

    }



    @Override

    public Type analyze(ListExpr e) {

        if (e.elements.isEmpty()) return e.setInferredType(new ClassValueType("<Empty>"));

        ValueType elemType = toValueType(e.elements.get(0).dispatch(this));

        for (int i = 1; i < e.elements.size(); i++) {

            ValueType next = toValueType(e.elements.get(i).dispatch(this));

            elemType = hierarchy.join(elemType, next);

        }

        return e.setInferredType(new ListValueType(elemType));

    }



    @Override

    public Type analyze(IndexExpr e) {

        Type listType = e.list.dispatch(this);

        Type indexType = e.index.dispatch(this);



// 【修改】：把错误绑定到整个 IndexExpr 节点 e 上

        if (!isIntType(indexType)) {

            err(e, "Index is of non-integer type `%s`", indexType);

        }



        if (listType instanceof ListValueType) return e.setInferredType(((ListValueType) listType).elementType);

        if (isStrType(listType)) return e.setInferredType(Type.STR_TYPE);



// 【修改】：同样把错误绑定到整个 e 上

        err(e, "Cannot index into type `%s`", listType);

        return e.setInferredType(Type.OBJECT_TYPE);

    }



    @Override

    public Type analyze(MemberExpr e) {

        Type objectType = e.object.dispatch(this);

        String memberName = e.member.name;



        String cn = className(objectType);

        if (cn == null) {

            err(e, "Cannot access member `%s` of non-class type `%s`", memberName, objectType);

            return e.setInferredType(Type.OBJECT_TYPE);

        }



        ValueType attrType = hierarchy.getAttribute(cn, memberName);

        if (attrType != null) return e.setInferredType(attrType);



        FuncType methodType = hierarchy.getMethod(cn, memberName);

        if (methodType != null) return e.setInferredType(methodType);



        err(e, "There is no attribute named `%s` in class `%s`", memberName, cn);

        return e.setInferredType(Type.OBJECT_TYPE);

    }



    @Override
    public Type analyze(CallExpr e) {
        // 1. 无论如何，先把所有的参数 dispatch 一遍，确保里面的表达式都被推断了类型
        List<Type> argTypes = new ArrayList<>();
        for (Expr arg : e.args) {
            argTypes.add(arg.dispatch(this));
        }

        // 2. 去符号表里查这个函数名叫什么
        String funcName = e.function.name;
        Type symbolType = sym.get(funcName); // 你的符号表查询方法

        // 3. 规则 1：找不到，或者找到的既不是函数也不是类（类可以实例化）
        if (symbolType == null || (!symbolType.isFuncType() && !(symbolType instanceof ClassValueType))) {
            err(e, "Not a function or class: %s", funcName);
            return e.setInferredType(Type.OBJECT_TYPE);
        }

        // 4. 处理正常函数调用的情况
        if (symbolType.isFuncType()) {
            FuncType funcType = (FuncType) symbolType;

            // 给 identifier 节点本身赋予 FuncType (对比你的 JSON，foo 本身是有 FuncType 的)
            e.function.setInferredType(funcType);

            // 规则 3：检查参数数量
            if (e.args.size() != funcType.parameters.size()) {
                err(e, "Expected %d arguments; got %d", funcType.parameters.size(), e.args.size());
            } else {
                // 规则 4：参数数量一致的前提下，逐个检查类型
                for (int i = 0; i < e.args.size(); i++) {
                    Type expected = funcType.parameters.get(i);
                    Type actual = argTypes.get(i);

                    // 使用你代码中的类型兼容性检查方法 conforms(actual, expected)
                    if (!conforms(actual, expected)) {
                        err(e, "Expected type `%s`; got type `%s` in parameter %d",
                                expected.className(), actual.className(), i);
                    }
                }
            }

            // 规则 5：调用的最终类型是函数的返回值类型
            return e.setInferredType(funcType.returnType);
        }

        // （如果涉及到 Class 的实例化调用 C()，后续再加处理，当前单测针对的是 FuncDef）
        return e.setInferredType(Type.OBJECT_TYPE);
    }
    @Override

    public Type analyze(MethodCallExpr e) {

        Type objectType = e.method.object.dispatch(this);

        String methodName = e.method.member.name;



        String cn = className(objectType);

        if (cn == null) {

// 🐛 修复：去掉了反引号

            err(e.method, "Cannot call method %s on non-class type %s", methodName, objectType);

            for (Expr arg : e.args) arg.dispatch(this);

            e.method.setInferredType(Type.OBJECT_TYPE);

            return e.setInferredType(Type.OBJECT_TYPE);

        }



        FuncType funcType = hierarchy.getMethod(cn, methodName);

        if (funcType == null) {

            err(e.method, "There is no method named %s in class %s", methodName, cn);

            for (Expr arg : e.args) arg.dispatch(this);

            e.method.setInferredType(Type.OBJECT_TYPE);

            return e.setInferredType(Type.OBJECT_TYPE);

        }



        e.method.setInferredType(funcType);

        int expectedArgs = funcType.parameters.size() - 1;

        if (e.args.size() != expectedArgs) {

            err(e, "Expected %d arguments; got %d", expectedArgs, e.args.size());

            for (Expr arg : e.args) arg.dispatch(this);

            return e.setInferredType(funcType.returnType);

        }



        for (int i = 0; i < e.args.size(); i++) {

            Type argType = e.args.get(i).dispatch(this);

            ValueType expType = funcType.parameters.get(i + 1);

            if (!conforms(argType, expType)) {

                err(e.args.get(i), "Expected type %s; got type %s", expType, argType);

            }

        }



        return e.setInferredType(funcType.returnType);

    }

    // 检查语句列表是否在所有路径上都有 return
    private boolean hasReturn(List<Stmt> stmts) {
        if (stmts == null || stmts.isEmpty()) {
            return false;
        }

        for (Stmt stmt : stmts) {
            if (stmt instanceof ReturnStmt) {
                return true; // 遇到了直接 return
            }
            if (stmt instanceof IfStmt) {
                IfStmt ifStmt = (IfStmt) stmt;
                // 只有当 if 和 else 里面都有保证返回的路径时，整体才算有 return
                if (hasReturn(ifStmt.thenBody) && hasReturn(ifStmt.elseBody)) {
                    return true;
                }
            }
        }
        return false;
    }

}