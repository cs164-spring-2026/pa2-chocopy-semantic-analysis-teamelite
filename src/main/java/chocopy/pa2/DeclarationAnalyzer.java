package chocopy.pa2;

import chocopy.common.analysis.AbstractNodeAnalyzer;
import chocopy.common.analysis.SymbolTable;
import chocopy.common.analysis.types.*;
import chocopy.common.astnodes.*;

import java.util.*;

public class DeclarationAnalyzer extends AbstractNodeAnalyzer<Type> {

    private SymbolTable<Type> sym = new SymbolTable<>();
    private final SymbolTable<Type> globals = sym;
    private final Errors errors;
    private final ClassHierarchy hierarchy;

    private final Deque<SymbolTable<Type>> funcScopeStack = new ArrayDeque<>();
    private String currentClassName = null;
    private boolean insideFunction = false;
    private Type expectedReturnType = null;

    public DeclarationAnalyzer(Errors errors, ClassHierarchy hierarchy) {
        this.errors = errors;
        this.hierarchy = hierarchy;
        addBuiltins();
    }

    private void addBuiltins() {
        ClassValueType objType  = new ClassValueType("object");
        ClassValueType intType  = new ClassValueType("int");
        ClassValueType strType  = new ClassValueType("str");
        ClassValueType noneType = new ClassValueType("<None>");

        globals.put("print", new FuncType(Collections.singletonList(objType), noneType));
        globals.put("input", new FuncType(Collections.emptyList(), strType));
        globals.put("len", new FuncType(Collections.singletonList(objType), intType));
    }

    public SymbolTable<Type> getGlobals() { return globals; }

    @Override
    public Type analyze(Program program) {
        // 第一个循环：安全的 Class 注册
        for (Declaration decl : program.declarations) {
            if (decl instanceof ClassDef) {
                ClassDef cd = (ClassDef) decl;
                String className = cd.name.name;
                // 如果已经存在同名类或者和内置类型重名，直接报错并跳过注册
                if (hierarchy.classExists(className)) {
                    errors.semError(cd.name, "Duplicate declaration of identifier in same scope: %s", className);
                } else {
                    hierarchy.addClass(className, cd.superClass.name);
                }
            }
        }

        for (Declaration decl : program.declarations) {
            Identifier id = decl.getIdentifier();
            String name   = id.name;

            if (decl instanceof ClassDef) {
                ClassDef cd = (ClassDef) decl;
                String superName = cd.superClass.name;

                if (superName.equals("int") || superName.equals("bool") || superName.equals("str")) {
                    // 1. 继承不能继承的特殊类型
                    errors.semError(cd.superClass, "Cannot extend special class: %s", superName);
                } else if (!superName.equals("object")) {
                    // 2 & 3. 递归检查父类是否完全合法
                    if (!isSuperClassValid(program, superName, new HashSet<>())) {
                        // 如果不合法，我们要区分它是 "非类变量" 还是 "未定义"
                        boolean isNonClass = false;
                        for (Declaration globalD : program.declarations) {
                            if (!(globalD instanceof ClassDef) && globalD.getIdentifier().name.equals(superName)) {
                                isNonClass = true;
                                break;
                            }
                        }

                        if (isNonClass) {
                            errors.semError(cd.superClass, "Super-class must be a class: %s", superName);
                        } else {
                            errors.semError(cd.superClass, "Super-class not defined: %s", superName);
                        }
                    }
                }
            }

            if (sym.declares(name)) {
                errors.semError(id, "Duplicate declaration of identifier in same scope: %s", name);
                continue;
            }

            if (!(decl instanceof ClassDef) && hierarchy.classExists(name)) {
                errors.semError(id, "Cannot shadow class name: %s", name);
            }

            Type shallowType = shallowTypeOf(decl);
            if (shallowType != null) sym.put(name, shallowType);
        }

        for (Declaration decl : program.declarations) {
            if (decl instanceof FuncDef || decl instanceof ClassDef) decl.dispatch(this);
            else if (decl instanceof VarDef) checkTypeAnnotation(((VarDef) decl).var.type);
        }

        for (Stmt stmt : program.statements) checkTopLevelReturn(stmt);

        return null;
    }

    private Type shallowTypeOf(Declaration decl) {
        if (decl instanceof VarDef) return ValueType.annotationToValueType(((VarDef) decl).var.type);
        if (decl instanceof FuncDef) {
            FuncDef fd = (FuncDef) decl;
            List<ValueType> params = new ArrayList<>();
            for (TypedVar p : fd.params) params.add(ValueType.annotationToValueType(p.type));
            return new FuncType(params, getSafeReturnType(fd.returnType));
        }
        if (decl instanceof ClassDef) {
            ClassDef cd = (ClassDef) decl;
            return new FuncType(Collections.emptyList(), new ClassValueType(cd.name.name));
        }
        return null;
    }


    private void checkTopLevelReturn(Stmt stmt) {
        if (stmt instanceof ReturnStmt) errors.semError(stmt, "Return statement cannot appear at the top level");
        if (stmt instanceof IfStmt) {
            IfStmt s = (IfStmt) stmt;
            for (Stmt b : s.thenBody) checkTopLevelReturn(b);
            for (Stmt b : s.elseBody) checkTopLevelReturn(b);
        }
    }

    @Override
    public Type analyze(VarDef varDef) {
        checkTypeAnnotation(varDef.var.type);
        return ValueType.annotationToValueType(varDef.var.type);
    }

    // 安全返回类型解析
    private ValueType getSafeReturnType(TypeAnnotation annotation) {
        if (annotation == null) return new ClassValueType("<None>");
        return ValueType.annotationToValueType(annotation);
    }

    @Override
    public Type analyze(ClassDef classDef) {
        String className  = classDef.name.name;
        String superName  = classDef.superClass.name;
        String oldClassName = currentClassName;
        currentClassName    = className;

        SymbolTable<Type> outerSym = sym;
        sym = new SymbolTable<>(sym);

        if (superName.equals("int") || superName.equals("bool") || superName.equals("str")) {
            // 情况 1：继承了不能继承的特殊/基础类型
            errors.semError(classDef.superClass, "Cannot extend special class: %s", superName);
        } else if (!superName.equals("object") && !hierarchy.classExists(superName)) {
            // 去全局符号表里查一下这个名字到底是个啥
            Type t = sym.get(superName);

            // 如果它在符号表里，但它不是一个类（比如是个普通变量、函数）
            if (t != null && !(t instanceof ClassValueType)) {
                // 情况 2：试图继承一个变量或函数
                errors.semError(classDef.superClass, "Super-class must be a class: %s", superName);
            } else {
                // 情况 3：根本没定义这个类，或者这个类因为自身语法错误被解析器扬了
                errors.semError(classDef.superClass, "Super-class not defined: %s", superName);
            }
        }

        for (Declaration decl : classDef.declarations) {
            Identifier id = decl.getIdentifier();
            String name   = id.name;

            if (sym.declares(name)) {
                errors.semError(id, "Duplicate declaration of identifier in same scope: %s", name);
                if (decl instanceof FuncDef) processMethodBody((FuncDef) decl, className);
                continue;
            }

            if (decl instanceof VarDef) {
                VarDef vd = (VarDef) decl;
                checkTypeAnnotation(vd.var.type);
                ValueType attrType = ValueType.annotationToValueType(vd.var.type);

                if (hierarchy.getAttribute(superName, name) != null || hierarchy.getMethod(superName, name) != null) {
                    errors.semError(id, "Cannot re-define attribute: %s", name);
                }

                hierarchy.setAttribute(className, name, attrType);
                sym.put(name, attrType);

            } else if (decl instanceof FuncDef) {
                FuncDef fd = (FuncDef) decl;
                List<ValueType> paramTypes = new ArrayList<>();
                for (TypedVar p : fd.params) {
                    checkTypeAnnotation(p.type);
                    paramTypes.add(ValueType.annotationToValueType(p.type));
                }
                checkTypeAnnotation(fd.returnType);
                ValueType retType  = getSafeReturnType(fd.returnType);
                FuncType  funcType = new FuncType(paramTypes, retType);

                if (fd.params.isEmpty()) {
                    errors.semError(fd.name, "First parameter of the following method must be of the enclosing class: %s", fd.name.name);
                } else {
                    TypedVar first = fd.params.get(0);
                    String firstTypeName = first.type instanceof ClassType ? ((ClassType) first.type).className : null;
                    if (!className.equals(firstTypeName)) {
                        errors.semError(fd.name, "First parameter of the following method must be of the enclosing class: %s", name);
                    }
                }

                if (hierarchy.getAttribute(superName, name) != null) {
                    errors.semError(id, "Cannot re-define attribute: %s", name);
                }

                FuncType inherited = hierarchy.getMethod(superName, name);
                if (inherited != null && !signaturesMatch(inherited, funcType)) {
                    errors.semError(fd.name, "Method overridden with different type signature: %s", name);
                }

                hierarchy.setMethod(className, name, funcType);
                sym.put(name, funcType);
                processMethodBody(fd, className);
            }
        }

        FuncType initMethod = hierarchy.getMethod(className, "__init__");
        List<ValueType> ctorParams = new ArrayList<>();
        if (initMethod != null && initMethod.parameters.size() > 0) {
            ctorParams.addAll(initMethod.parameters.subList(1, initMethod.parameters.size()));
        }
        globals.put(className, new FuncType(ctorParams, new ClassValueType(className)));

        sym = outerSym;
        currentClassName = oldClassName;
        return null;
    }

    private boolean signaturesMatch(FuncType inherited, FuncType override) {
        if (inherited.parameters.size() != override.parameters.size()) return false;
        if (!inherited.returnType.equals(override.returnType)) return false;
        for (int i = 1; i < inherited.parameters.size(); i++) {
            if (!inherited.parameters.get(i).equals(override.parameters.get(i))) return false;
        }
        return true;
    }

    @Override
    public Type analyze(FuncDef funcDef) {
        List<ValueType> paramTypes = new ArrayList<>();
        for (TypedVar p : funcDef.params) {
            checkTypeAnnotation(p.type);
            paramTypes.add(ValueType.annotationToValueType(p.type));
        }
        checkTypeAnnotation(funcDef.returnType);
        ValueType retType  = getSafeReturnType(funcDef.returnType);
        processFuncBody(funcDef, null);
        return new FuncType(paramTypes, retType);
    }

    private void processMethodBody(FuncDef fd, String className) { processFuncBody(fd, className); }

    private void processFuncBody(FuncDef fd, String selfClass) {
        boolean wasInsideFunction = insideFunction;
        insideFunction = true;

        SymbolTable<Type> outerSym = sym;
        sym = new SymbolTable<>(sym);
        funcScopeStack.push(sym);

        // 1. 注册参数
        Set<String> paramNames = new HashSet<>();
        for (TypedVar param : fd.params) {
            String pName = param.identifier.name;
            if (paramNames.contains(pName)) {
                errors.semError(param.identifier, "Duplicate declaration of identifier in same scope: %s", pName);
            } else {
                paramNames.add(pName);
                if (hierarchy.classExists(pName)) errors.semError(param.identifier, "Cannot shadow class name: %s", pName);
                sym.put(pName, ValueType.annotationToValueType(param.type));
            }
        }

        // 2. Pass 1: 收集当前层级的所有声明
        for (Declaration decl : fd.declarations) {
            Identifier id = decl.getIdentifier();
            String name = id.name;

            if (sym.declares(name)) {
                errors.semError(id, "Duplicate declaration of identifier in same scope: %s", name);
                continue;
            }

            // 修复 1：只有普通的变量定义和函数定义才需要检查“是否遮蔽了类名”
            if ((decl instanceof VarDef || decl instanceof FuncDef) && hierarchy.classExists(name)) {
                errors.semError(id, "Cannot shadow class name: %s", name);
            }

            if (decl instanceof GlobalDecl) {
                Type t = globals.get(name);
                // 修复 2：如果找不到，或者找到的是个函数/类（它们在符号表里都是 FuncType），则报错
                if (t == null || t instanceof FuncType) {
                    errors.semError(id, "Not a global variable: %s", name);
                } else {
                    sym.put(name, t);
                }
            } else if (decl instanceof NonLocalDecl) {
                Type outerType = findNonlocalVar(name);
                // 修复 2：同理，nonlocal 也必须指向普通变量，不能是函数/类
                if (outerType == null || outerType instanceof FuncType) {
                    errors.semError(id, "Not a nonlocal variable: %s", name);
                } else {
                    sym.put(name, outerType);
                }
            } else if (decl instanceof VarDef) {
                checkTypeAnnotation(((VarDef) decl).var.type);
                sym.put(name, ValueType.annotationToValueType(((VarDef) decl).var.type));
            } else if (decl instanceof FuncDef) {
                FuncDef nested = (FuncDef) decl;
                List<ValueType> nParams = new ArrayList<>();
                for (TypedVar p : nested.params) nParams.add(ValueType.annotationToValueType(p.type));
                sym.put(name, new FuncType(nParams, getSafeReturnType(nested.returnType)));
            }
        }

        // 3. Pass 2: 等当前层级符号表就绪后，再深入嵌套函数的内部进行推导
        for (Declaration decl : fd.declarations) {
            if (decl instanceof FuncDef) {
                processFuncBody((FuncDef) decl, null);
            }
        }

        // 4. 返回值验证
        ValueType declaredRet = getSafeReturnType(fd.returnType);
        String retName = declaredRet.toString(); // 这里的 toString() 通常返回类名

        // 核心修复：如果返回类型不是 <None> 且不是 object，才强制要求所有路径都有 return
        if (!retName.equals("<None>") && !retName.equals("object") && !allPathsReturn(fd.statements)) {
            errors.semError(fd.name, "All paths in this function/method must have a return statement: %s", fd.name.name);
        }

        // 5. 语句分析
        for (Stmt stmt : fd.statements) stmt.dispatch(this);

        funcScopeStack.pop();
        sym = outerSym;
        insideFunction = wasInsideFunction;
    }

    private Type findNonlocalVar(String varName) {
        boolean skippedCurrent = false;
        for (SymbolTable<Type> scope : funcScopeStack) {
            if (!skippedCurrent) { skippedCurrent = true; continue; }
            if (scope.declares(varName)) return scope.get(varName);
        }
        return null;
    }

    // 修复：只要语句列表中有任何一条语句满足返回条件即可
    private boolean allPathsReturn(List<Stmt> stmts) {
        if (stmts == null || stmts.isEmpty()) return false;
        for (Stmt stmt : stmts) {
            if (stmt instanceof ReturnStmt) return true;
            if (stmt instanceof IfStmt) {
                IfStmt ifS = (IfStmt) stmt;
                // 如果 if 的两个分支都能保证返回，那么整个语句块也保证返回
                if (allPathsReturn(ifS.thenBody) && allPathsReturn(ifS.elseBody)) {
                    return true;
                }
            }
        }
        return false;
    }

    private void checkTypeAnnotation(TypeAnnotation annotation) {
        if (annotation == null) return;
        if (annotation instanceof ClassType) {
            String cn = ((ClassType) annotation).className;

            // 👇 新增逻辑：如果是内部类型，直接放行，不要去 hierarchy 里查！
            if (cn.equals("<None>") || cn.equals("<Empty>")) {
                return;
            }

            if (!hierarchy.classExists(cn)) {
                errors.semError(annotation, "Invalid type annotation; there is no class named: %s", cn);
            }
        } else if (annotation instanceof ListType) {
            checkTypeAnnotation(((ListType) annotation).elementType);
        }
    }

    // 防弹版 isNoneType
    private boolean isSafeNoneType(ValueType t) {
        if (t == null) return false;
        return "<None>".equals(t.toString());
    }

    private void checkRule8(Identifier id) {
        String name = id.name;
        if (sym.declares(name)) return;
        boolean existsOuter = globals.declares(name) || findNonlocalVar(name) != null;
        if (existsOuter) {
            errors.semError(id, "Cannot assign to variable that is not explicitly declared in this scope: %s", name);
        }
    }

    @Override public Type analyze(GlobalDecl decl) { return null; }
    @Override public Type analyze(NonLocalDecl decl) { return null; }
    @Override public Type analyze(ExprStmt s) { return null; }
    @Override public Type analyze(ReturnStmt s) { return null; }

    @Override
    public Type analyze(AssignStmt s) {
        if (insideFunction) {
            for (Expr target : s.targets) {
                if (target instanceof Identifier) checkRule8((Identifier) target);
            }
        }
        return null;
    }

    @Override
    public Type analyze(ForStmt s) {
        if (insideFunction) {
            checkRule8(s.identifier);
            for (Stmt stmt : s.body) stmt.dispatch(this);
        }
        return null;
    }

    @Override
    public Type analyze(IfStmt s) {
        if (insideFunction) {
            for (Stmt stmt : s.thenBody) stmt.dispatch(this);
            for (Stmt stmt : s.elseBody) stmt.dispatch(this);
        }
        return null;
    }

    @Override
    public Type analyze(WhileStmt s) {
        if (insideFunction) {
            for (Stmt stmt : s.body) stmt.dispatch(this);
        }
        return null;
    }

    private boolean isSuperClassValid(Program program, String superName, Set<String> visited) {
        if (superName.equals("object")) return true;
        if (superName.equals("int") || superName.equals("bool") || superName.equals("str")) return false;

        // 防死循环 (例如 class A(B):... class B(A):...)
        if (!visited.add(superName)) return false;

        // 在顶层声明中查找这个父类，如果找到了，继续递归检查它的父类是否合法
        for (Declaration d : program.declarations) {
            if (d instanceof ClassDef && d.getIdentifier().name.equals(superName)) {
                return isSuperClassValid(program, ((ClassDef) d).superClass.name, visited);
            }
        }
        return false; // 根本没找到这个类，或者它不合法
    }
}