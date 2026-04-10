package chocopy.pa2;

import chocopy.common.analysis.AbstractNodeAnalyzer;
import chocopy.common.analysis.SymbolTable;
import chocopy.common.analysis.types.FuncType;
import chocopy.common.analysis.types.ListValueType;
import chocopy.common.analysis.types.Type;
import chocopy.common.analysis.types.ValueType;
import chocopy.common.astnodes.*;
import chocopy.common.astnodes.UnaryExpr;
import chocopy.common.astnodes.BooleanLiteral;
import chocopy.common.astnodes.StringLiteral;
import chocopy.common.astnodes.NoneLiteral;
import chocopy.common.analysis.types.ListValueType;

import static chocopy.common.analysis.types.Type.INT_TYPE;
import static chocopy.common.analysis.types.Type.OBJECT_TYPE;

/** Analyzer that performs ChocoPy type checks on all nodes.  Applied after
 *  collecting declarations. */
public class TypeChecker extends AbstractNodeAnalyzer<Type> {

    /** The current symbol table (changes depending on the function
     *  being analyzed). */
    private SymbolTable<Type> sym;
    /** Collector for errors. */
    private Errors errors;
    private Type currentExpectedReturnType = null;


    /** Creates a type checker using GLOBALSYMBOLS for the initial global
     *  symbol table and ERRORS0 to receive semantic errors. */
    public TypeChecker(SymbolTable<Type> globalSymbols, Errors errors0) {
        sym = globalSymbols;
        errors = errors0;
    }

    /** Inserts an error message in NODE if there isn't one already.
     *  The message is constructed with MESSAGE and ARGS as for
     *  String.format. */
    private void err(Node node, String message, Object... args) {
        errors.semError(node, message, args);
    }

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

    @Override
    public Type analyze(ExprStmt s) {
        s.expr.dispatch(this);
        return null;
    }

    @Override
    public Type analyze(IntegerLiteral i) {
        return i.setInferredType(Type.INT_TYPE);
    }

    @Override
    public Type analyze(BinaryExpr e) {
        Type t1 = e.left.dispatch(this);
        Type t2 = e.right.dispatch(this);

        switch (e.operator) {
            case "-":
            case "*":
            case "//":
            case "%":
                if (Type.INT_TYPE.equals(t1) && Type.INT_TYPE.equals(t2)) {
                    return e.setInferredType(Type.INT_TYPE);
                } else {
                    err(e, "Cannot apply operator `%s` on types `%s` and `%s`", e.operator, t1, t2);
                    return e.setInferredType(Type.INT_TYPE);
                }

                // 【新增】加法逻辑：支持整数和字符串
            case "+":
                if (Type.INT_TYPE.equals(t1) && Type.INT_TYPE.equals(t2)) {
                    return e.setInferredType(Type.INT_TYPE);
                } else if (Type.STR_TYPE.equals(t1) && Type.STR_TYPE.equals(t2)) {
                    return e.setInferredType(Type.STR_TYPE);
                } else {
                    // (注意：这里暂时省略了 List 的合并，你可以之后再补)
                    err(e, "Cannot apply operator `%s` on types `%s` and `%s`", e.operator, t1, t2);
                    // 遇到错误，由于不知具体是啥，先保守给 INT (或者你可以根据左侧类型给)
                    return e.setInferredType(Type.INT_TYPE);
                }

                // 【新增】比较运算符逻辑
            case "<":
            case "<=":
            case ">":
            case ">=":
                if (Type.INT_TYPE.equals(t1) && Type.INT_TYPE.equals(t2)) {
                    return e.setInferredType(Type.BOOL_TYPE); // 比较结果一定是 bool
                } else {
                    err(e, "Cannot apply operator `%s` on types `%s` and `%s`", e.operator, t1, t2);
                    return e.setInferredType(Type.BOOL_TYPE); // 错误恢复：假装它返回了 bool
                }

            case "==":
            case "!=":
                // 相等性比较（只要两边类型一致基本都让比，具体规则查阅手册，这里做简化）
                // 结果一定也是 bool
                return e.setInferredType(Type.BOOL_TYPE);

            default:
                return e.setInferredType(Type.OBJECT_TYPE);
        }
    }

    @Override
    public Type analyze(UnaryExpr e) {
        Type t = e.operand.dispatch(this); // 先求操作数的类型

        if (e.operator.equals("-")) {
            if (Type.INT_TYPE.equals(t)) {
                return e.setInferredType(Type.INT_TYPE);
            } else {
                err(e, "Cannot apply operator `-` on type `%s`", t);
                return e.setInferredType(Type.INT_TYPE);
            }
        } else if (e.operator.equals("not")) {
            if (Type.BOOL_TYPE.equals(t)) {
                return e.setInferredType(Type.BOOL_TYPE);
            } else {
                err(e, "Cannot apply operator `not` on type `%s`", t);
                return e.setInferredType(Type.BOOL_TYPE);
            }
        }
        return e.setInferredType(Type.OBJECT_TYPE);
    }

    @Override
    public Type analyze(Identifier id) {
        String varName = id.name;
        Type varType = sym.get(varName);

        if (varType != null && varType.isValueType()) {
            return id.setInferredType(varType);
        }

        err(id, "Not a variable: %s", varName);
        return id.setInferredType(ValueType.OBJECT_TYPE);
    }

    // 在 TypeChecker 类中补充以下方法：

    @Override
    public Type analyze(BooleanLiteral b) {
        // 给布尔字面量打上 bool 标签
        return b.setInferredType(Type.BOOL_TYPE);
    }

    @Override
    public Type analyze(StringLiteral s) {
        // 给字符串打上 str 标签
        return s.setInferredType(Type.STR_TYPE);
    }

    @Override
    public Type analyze(NoneLiteral n) {
        // 给 None 打上 <None> 标签
        return n.setInferredType(Type.NONE_TYPE);
    }

    @Override
    public Type analyze(IfStmt s) {
        // 1. 先去分析条件表达式，获取它的类型
        Type conditionType = s.condition.dispatch(this);

        // 2. 检查条件类型是不是 bool
        if (!Type.BOOL_TYPE.equals(conditionType)) {
            err(s, "Condition expression must be of type `bool`");
        }

        // 3. 递归遍历 if 里面的语句
        for (Stmt stmt : s.thenBody) {
            stmt.dispatch(this);
        }
        // 4. 递归遍历 else 里面的语句
        for (Stmt stmt : s.elseBody) {
            stmt.dispatch(this);
        }

        // 语句 (Statement) 本身没有类型，所以返回 null
        return null;
    }

    @Override
    public Type analyze(WhileStmt s) {
        // 1. 分析条件表达式
        Type conditionType = s.condition.dispatch(this);

        // 2. while 的条件也必须是 bool
        if (!Type.BOOL_TYPE.equals(conditionType)) {
            err(s, "Condition expression must be of type `bool`");
        }

        // 3. 递归遍历循环体里面的语句
        for (Stmt stmt : s.body) {
            stmt.dispatch(this);
        }

        return null;
    }

    @Override
    public Type analyze(AssignStmt s) {
        // 1. 算出等号最右边（要赋的值）的实际类型
        Type valueType = s.value.dispatch(this);

        // 2. 遍历等号左边的所有目标变量
        for (Expr target : s.targets) {
            // 获取目标变量期望的类型
            Type targetType = target.dispatch(this);

            // 核心检查：如果 valueType 不能兼容 targetType，就报错！
            if (!isSubtypeOf(valueType, targetType)) {
                err(s, "Expected type `%s`; got type `%s`", targetType, valueType);
            }
        }

        return null;
    }

    @Override
    public Type analyze(ReturnStmt s) {
        Type actualReturnType;
        if (s.value != null) {
            actualReturnType = s.value.dispatch(this);
        } else {
            // 单独一个 "return" 视作返回 None
            actualReturnType = Type.NONE_TYPE;
        }

        // 核心校验：实际返回类型是否兼容函数定义的返回类型
        if (currentExpectedReturnType != null) {
            if (!isSubtypeOf(actualReturnType, currentExpectedReturnType)) {
                err(s, "Expected type `%s`; got type `%s`",
                        currentExpectedReturnType, actualReturnType);
            }
        }

        return null;
    }

    @Override
    public Type analyze(ListExpr e) {
        // 如果是空列表 []，它的类型叫 <Empty>
        if (e.elements.isEmpty()) {
            return e.setInferredType(Type.EMPTY_TYPE);
        }

        // 先假设列表的类型是第一个元素的类型
        Type listElementType = e.elements.get(0).dispatch(this);

        // 遍历剩下的元素，不断求取更宽泛的祖先
        for (int i = 1; i < e.elements.size(); i++) {
            Type nextElementType = e.elements.get(i).dispatch(this);
            listElementType = lowestCommonAncestor(listElementType, nextElementType);
        }

        // 假设有个 ListValueType 专门用来表示列表类型
        // （请去 common/analysis/types 里找正确的列表类型封装类，可能是 ListValueType(listElementType)）
        return e.setInferredType(new ListValueType(listElementType));
    }

    @Override
    public Type analyze(IndexExpr e) {
        // 处理类似 my_list[i + 1] 的语法
        Type listType = e.list.dispatch(this);   // 分析中括号外面的列表/字符串
        Type indexType = e.index.dispatch(this); // 分析中括号里面的索引

        // 语义规则：索引必须是整数 int
        if (!Type.INT_TYPE.equals(indexType)) {
            err(e, "Index must be of type `int`");
        }

        // 【PA2 进阶核心任务预留】
        // 这里需要检查 listType 是不是真的是个列表或字符串。
        // 并且提取出它的元素类型返回。现在先用 object 保底。
        return e.setInferredType(Type.OBJECT_TYPE);
    }

    @Override
    public Type analyze(CallExpr e) {
        String funcName = e.function.name;

        // 1. 去符号表里查这个名字
        Type symbolType = sym.get(funcName);

        // 如果找不到，或者找到的不是函数（比如它是个普通的 int 变量）
        // （提示：在 ChocoPy 中，类名也是可以调用的，相当于构造函数，这里暂且简化为 isFuncType）
        if (symbolType == null || !symbolType.isFuncType()) {
            err(e.function, "Not a function or class: %s", funcName);

            // 错误恢复：就算报错了也要把括号里的参数遍历完，防止漏报内部错误
            for (Expr arg : e.args) {
                arg.dispatch(this);
            }
            return e.setInferredType(Type.OBJECT_TYPE);
        }

        // 既然确认它是函数了，我们就把它当成函数类型来处理
        // （假设起步代码中的函数类型类叫做 FuncType，请根据实际情况 import）
        FuncType funcDef = (FuncType) symbolType;

        // 2. 检查参数数量对不对？
        if (e.args.size() != funcDef.parameters.size()) {
            err(e, "Expected %d arguments; got %d", funcDef.parameters.size(), e.args.size());

            // 错误恢复：虽然数量不对，但依然要把括号里的表达式都分析一遍
            for (Expr arg : e.args) {
                arg.dispatch(this);
            }
            // 依然给它打上期望的返回类型，防止引发外层表达式报错
            return e.setInferredType(funcDef.returnType);
        }

        // 3. 逐个查验参数类型！（高潮来了）
        for (int i = 0; i < e.args.size(); i++) {
            // 计算用户实际传入的参数类型
            Type actualArgType = e.args.get(i).dispatch(this);

            // 从函数定义中拿出规定的参数类型
            Type expectedParamType = funcDef.parameters.get(i);

            // 调用我们上一步写的“裁判”方法！
            if (!isSubtypeOf(actualArgType, expectedParamType)) {
                // 如果不兼容，把错误准确地挂在具体的那个参数节点上
                err(e.args.get(i), "Expected type `%s`; got type `%s`", expectedParamType, actualArgType);
            }
        }

        // 4. 全部检查完毕，完美通关！把函数预设的返回值类型贴到这个 CallExpr 节点上
        return e.setInferredType(funcDef.returnType);
    }

    @Override
    public Type analyze(ForStmt s) {
        // 1. 分析 in 后面的可迭代对象 (Iterable)
        Type iterableType = s.iterable.dispatch(this);

        // 【PA2 进阶任务预留】
        // 需要检查 iterableType 是不是字符串或列表，
        // 并且检查循环变量 (s.identifier) 是否被声明过，类型匹不匹配。

        // 2. 递归遍历 for 循环体里面的语句
        for (Stmt stmt : s.body) {
            stmt.dispatch(this);
        }
        return null;
    }

    @Override
    public Type analyze(FuncDef f) {
        // 1. 保存旧的返回类型（嵌套函数用）
        Type oldReturnType = currentExpectedReturnType;
        currentExpectedReturnType = ValueType.annotationToValueType(f.returnType);

        // 2. 进入新的作用域
        this.sym = new SymbolTable<>(this.sym);

        // 3. 将函数的参数存入符号表
        for (TypedVar param : f.params) {
            // 获取类型对象
            Type paramType = ValueType.annotationToValueType(param.type);

            // 【核心修正】：使用 param.identifier.name 而不是 param.name.name
            String paramName = param.identifier.name;

            // 检查重复定义并放入符号表
            if (sym.declares(paramName)) {
                // 报错也使用 param.identifier 节点
                err(param.identifier, "Duplicate identifier: " + paramName);
            } else {
                sym.put(paramName, paramType);
            }
        }

        // 4. 遍历函数内部声明和语句
        for (Declaration decl : f.declarations) {
            decl.dispatch(this);
        }
        for (Stmt stmt : f.statements) {
            stmt.dispatch(this);
        }

        // 5. 【核心修改】离开作用域
        // 将 sym 指向回它的父节点，这样刚才那一层局部变量就自然“失效”了
        this.sym = this.sym.getParent();

        // 6. 恢复返回类型
        currentExpectedReturnType = oldReturnType;

        return null;
    }




    /**
     * 判断 actual（实际类型）是否可以赋值给 expected（预期类型/目标类型）。
     * 对应 ChocoPy 规范中的 actual <= expected。
     */
    private boolean isSubtypeOf(Type actual, Type expected) {
        // 1. 如果完全一样，肯定兼容
        if (expected.equals(actual)) {
            return true;
        }

        // 2. 任何类型都可以赋值给 object
        if (Type.OBJECT_TYPE.equals(expected)) {
            return true;
        }

        // 3. 处理空值 <None>
        // <None> 可以赋给除 int, bool, str 之外的任何 ValueType (即对象/类)
        if (Type.NONE_TYPE.equals(actual)) {
            if (expected.isValueType() &&
                    !Type.INT_TYPE.equals(expected) &&
                    !Type.BOOL_TYPE.equals(expected) &&
                    !Type.STR_TYPE.equals(expected)) {
                return true;
            }
            return false;
        }

        // 4. 处理空列表 <Empty>
        // <Empty> 可以赋值给任何一种具体的列表类型 (比如 [int])
        if (Type.EMPTY_TYPE.equals(actual) && expected.isListType()) {
            return true;
        }

        // 5. 【高阶：处理类的继承】
        // 如果是自定义类，你需要顺着符号表或类层级往上找父类。
        // 这里提供一个伪逻辑框架（你需要根据 PA2 起始代码中具体的类表结构来完善）：
        /*
        if (actual.isValueType() && expected.isValueType()) {
            String currentClass = actual.className();
            String targetClass = expected.className();

            // 循环向上找父类，直到找到 targetClass，或者找到 object 为止
            while (!currentClass.equals("object")) {
                currentClass = classHierarchy.getSuperClass(currentClass);
                if (currentClass.equals(targetClass)) {
                    return true;
                }
            }
        }
        */

        // 其他情况（比如把 int 赋给 bool，或者把 [int] 赋给 [str]）都是不兼容的
        return false;
    }

    /**
     * 计算两个类型的最近公共祖先 (LCA)
     */
    private Type lowestCommonAncestor(Type t1, Type t2) {
        // 如果一模一样，那祖先就是它自己
        if (t1.equals(t2)) {
            return t1;
        }

        // 如果有一个是 <None>，另一个是类/对象，则祖先是那个类/对象
        if (Type.NONE_TYPE.equals(t1) && t2.isValueType() && !isBasicType(t2)) return t2;
        if (Type.NONE_TYPE.equals(t2) && t1.isValueType() && !isBasicType(t1)) return t1;

        // 【进阶：类的继承层级 LCA】
        // 如果 t1 和 t2 都是用户定义的类，你需要查表找到它们共同继承的那个类。
        // 如果找不到其他交集，或者它们是不同的基本类型(int 和 bool)，祖先统统是 object
        return Type.OBJECT_TYPE;
    }

    // 辅助判断是否是三个基本类型
    private boolean isBasicType(Type t) {
        return Type.INT_TYPE.equals(t) || Type.BOOL_TYPE.equals(t) || Type.STR_TYPE.equals(t);
    }
}
