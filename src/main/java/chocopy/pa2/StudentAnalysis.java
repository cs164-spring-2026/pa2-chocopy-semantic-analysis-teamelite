package chocopy.pa2;

import chocopy.common.analysis.SymbolTable;
import chocopy.common.analysis.types.Type;
import chocopy.common.astnodes.Program;

/** Top-level class for performing semantic analysis. */
public class StudentAnalysis {

    /**
     * Perform semantic analysis on PROGRAM, adding error messages and type
     * annotations. Provides debugging output iff DEBUG. Returns modified tree.
     *
     * Pass structure:
     *   Pass 1 (DeclarationAnalyzer): collect all declarations, build class
     *     hierarchy and global symbol table, report all 11 semantic errors.
     *   Pass 2 (TypeChecker): only runs if no semantic errors; assigns
     *     inferredType to every expression node and reports type errors.
     */
    public static Program process(Program program, boolean debug) {
        if (program.hasErrors()) {
            return program;
        }

        // Build class hierarchy structure (passed to both passes)
        ClassHierarchy hierarchy = new ClassHierarchy();

        // Pass 1: Declaration analysis and semantic checks
        DeclarationAnalyzer declarationAnalyzer =
            new DeclarationAnalyzer(program.errors, hierarchy);
        program.dispatch(declarationAnalyzer);
        SymbolTable<Type> globalSym = declarationAnalyzer.getGlobals();

        // Pass 2: Type checking (only when no semantic errors)
        if (!program.hasErrors()) {
            TypeChecker typeChecker =
                new TypeChecker(globalSym, hierarchy, program.errors);
            program.dispatch(typeChecker);
        }

        return program;
    }
}