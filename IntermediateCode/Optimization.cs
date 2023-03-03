using System;
using SetCollection;
using IntermediateCode;
using AbstractMachine;
using Cormen;
using System.IO;

namespace IntermediateCode
{
    public enum Meet
    {
        UNION, INTERSECTION
    };

    public class Info
    {
        public Info(Set U, Block B)
        {
            Gen = new BitSet[B.Size];
            Kill = new BitSet[B.Size];
            for (int i = 0; i < B.Size; i++)
            {
                Gen[i] = new BitSet(U);
                Kill[i] = new BitSet(U);
            }
            IN = new BitSet(U);
            OUT = new BitSet(U);
            last = -1;
        }
        public BitSet[] Gen;
        public BitSet[] Kill;
        public BitSet IN;
        public BitSet OUT;
        public int last;
    };

    public abstract class Optimization
    {
        // Control-flow Graph. 
        // -------------------
        // You will first build a control-flow graph representation 
        // of the TAC for a method. More specifically, you should 
        // design a package that builds a CFG for a method’s TACList. 
        // 
        // Generic Dataflow Analysis Framework. 
        // ------------------------------------
        // Your implementation of the dataflow analysis framework
        // will include a generic dataflow engine. This engine is 
        // implemented once and reused as the base class for each 
        // analysis instance. Each analysis instance will describe 
        // the specific lattice and transfer functions that it uses. 
        // The dataflow analysis provides a method that solves the 
        // dataflow equations using the iterative algorithm explored 
        // in the homeworks. Additional methods will access to the IN
        // and OUT values for each basic block in the CFG, once the 
        // solution is computed. The dataflow analysis engine is 
        // capable of performing both forward or and backward analyses.
        // 
        // Analysis Instances. You will then implement the following 
        // analysis instances:
        // 
        // • Live variables analysis: compute variables which may be 
        //      live at each program point;
        // • Available expressions: compute expressions available in 
        //      all of the program executions;
        // • Reaching definitions: for each program point, compute 
        //      the definitions that may reach that point;
        // 
        // Next, use the analysis results to perform the following 
        // optimizations:
        // 
        // • Constant folding: use the results from constant folding 
        //      analysis and replace each constant variable with
        // the computed constant.
        // • Dead code elimination: remove code which updates variables 
        //      whose values are not used in any executions. This 
        //      optimization will use the results from the live 
        //      variable analysis.
        // • Common subexpression elimination: reuse expressions 
        //      already computed in the program. Here you will use the 
        //      information computed with the available expressions 
        //      analysis. If an expression is available before an 
        //      instruction that re-computes that expression, you have 
        //      to replace the computation by the variable which holds 
        //      the result of that expression in all executions of the 
        //      program. If there is no such variable, you will create 
        //      a temporary variable to store the result of the expression.
        // • Loop invariant code motion: for a given loop, detect 
        //      computation which doesn’t change in different iterations 
        //      of the loop and hoist that computation out of the loop. 
        //      Use reaching definition information to determine loop 
        //      invariant code. For this transformation, you must 
        //      identify loops in the CFG.
        // • Elimination of run-time checks. Perform transformations 
        //      similar to common subexpression elimination and loop 
        //      invariant code motion to eliminate redundant array bounds 
        //      checks or null pointer checks, or move such checks outside 
        //      loops.

        public abstract ArrayOf<Info> Analysis(ArrayOf<Block> blocks, Set domain);
        public abstract ArrayOf<Info> Initialize(ArrayOf<Block> blocks, Set domain);
        public abstract void TransferFunction(ArrayOf<Block> blocks, Set domain, ref ArrayOf<Info> info);

        protected ArrayOf<Info> ForwardAnalysis(ArrayOf<Block> blocks, Set domain, Meet meet)
        {
            ArrayOf<Info> info = Initialize(blocks, domain);

            TransferFunction(blocks, domain, ref info);

            // Forward Analysis
            bool done = false;
            while (!done)
            {
                done = true;
                for (int i = 1; i < blocks.Count; i++)
                {
                    int last = info[i].last;

                    if (meet == Meet.UNION)
                    {
                        info[i].IN.SetToZeros();
                        foreach (Block pred in blocks[i].Predecessor)
                            info[i].IN = info[i].IN + info[pred.Id].OUT;
                    }
                    else if (meet == Meet.INTERSECTION)
                    {
                        info[i].IN.SetToOnes();
                        foreach (Block pred in blocks[i].Predecessor)
                            info[i].IN = info[i].IN * info[pred.Id].OUT;
                    }

                    if (blocks[i].Size > 0)
                    {
                        BitSet old = info[i].OUT;
                        info[i].OUT = info[i].Gen[last] + (info[i].IN - info[i].Kill[last]);
                        done = done && (old == info[i].OUT);
                    }
                }
            }

            return info;
        }

        protected ArrayOf<Info> BackwardAnalysis(ArrayOf<Block> blocks, Set domain, Meet meet)
        {
            ArrayOf<Info> info = Initialize(blocks, domain);

            TransferFunction(blocks, domain, ref info);

            // Backward Analysis
            bool done = false;
            while (!done)
            {
                done = true;
                for (int i = blocks.Count - 2; i >= 0; i--)
                {
                    int last = info[i].last;

                    if (meet == Meet.UNION)
                    {
                        info[i].OUT.SetToZeros();
                        foreach (Block succ in blocks[i].Sucessor)
                            info[i].OUT = info[i].OUT + info[succ.Id].IN;
                    }
                    else if (meet == Meet.INTERSECTION)
                    {
                        info[i].OUT.SetToOnes();
                        foreach (Block succ in blocks[i].Sucessor)
                            info[i].OUT = info[i].OUT * info[succ.Id].IN;
                    }

                    if (blocks[i].Size > 0)
                    {
                        BitSet old = info[i].IN;
                        info[i].IN = info[i].Gen[last] + (info[i].OUT - info[i].Kill[last]);
                        done = done && (old == info[i].IN);
                    }
                }
            }

            return info;
        }
    }

    public class ReachableDefinition : Optimization
    {
        public override ArrayOf<Info> Analysis(ArrayOf<Block> blocks, Set domain)
        {
            return ForwardAnalysis(blocks, domain, Meet.UNION);
        }

        public override ArrayOf<Info> Initialize(ArrayOf<Block> blocks, Set domain)
        {
            ArrayOf<Info> info = new ArrayOf<Info>();

            for (int i = 0; i < blocks.Count; i++)
                info.Add(new Info(domain, blocks[i]));

            return info;
        }

        public int FillReachableDefinitionsInfo(Block block, Set UDef, ref BitSet[] gen, ref BitSet[] kill)
        {
            AbstractMachine.IntermediateCode code = block.Code;

            // A definition di in UDef of a variable x in Var reaches a
            // program point u if di occurs on some path from Start to u and is not followed
            // by any other definition of x on this path.

            for (int i = code.Count - 1; i >= 0; i--)
            {
                if (i < code.Count - 1)
                {
                    gen[i] = gen[i] + gen[i + 1];
                    kill[i] = kill[i] + kill[i + 1];
                }
                if (code[i].Target != null)
                    for (int j = 0; j < UDef.Count; j++)
                        if (code[i].Target == ((IntermediateInstruction)UDef[j]).Target)
                            if (Object.ReferenceEquals(UDef[j], code[i]))
                                gen[i][j] = true;
                            else
                                kill[i][j] = true;
                kill[i] = kill[i] + gen[i];
            }

            return 0;
        }

        public override void TransferFunction(ArrayOf<Block> blocks, Set domain, ref ArrayOf<Info> info)
        {
            for (int i = 0; i < blocks.Count; i++)
                info[i].last = FillReachableDefinitionsInfo(blocks[i], domain, ref info[i].Gen, ref info[i].Kill);
        }

        public static string ToLaTeX(ArrayOf<Info> info, Set domain)
        {
            string str = "";
            int bk;

            string Title = "Alcan\\c{c}abilidade de Defini\\c{c}\\~oes";

            str += "\\section{" + Title + "}\n\n";
            str += "\\begin{itemize}\n";
            str += "  \\item[$Gen$] ...\n";
            str += "  \\item[$Kill$] ...\n";
            str += "  \\item[$IN$] ...\n";
            str += "  \\item[$OUT$] ...\n";
            str += "\\end{itemize}\n\n";

            str += "\\begin{table}[ht]\n";
            str += "\\centering\n";
            str += "\\begin{tabular}{l|l|l|l|l}\n";
            str += "\t& Gen & Kill & IN & OUT\\\\\n";
            str += "\\hline\n";
            for (bk = 1; bk < info.Count - 1; bk++)
            {
                int last = info[bk].last;
                str += "$B_{" + bk.ToString() + "}$ & ";
                str += " $" + info[bk].Gen[last].ToBinary() + "$ &" +
                    " $" + info[bk].Kill[last].ToBinary() + "$ &" +
                    " $" + info[bk].IN.ToBinary() + "$ &" +
                    " $" + info[bk].OUT.ToBinary() + "$\\\\\n";
            }
            str += "\\end{tabular}\n";
            str += "\\caption{" + Title + " --- $(" + domain.ToString() + ")$}\n";
            str += "\\end{table}\n\n";

            return str;
        }

        public static string Write(string path, ArrayOf<Info> info, Set domain)
        {
            string name = "ReachableDefinitions.tex";
            string filename = Path.Combine(path, name);

            System.IO.StreamWriter output = new System.IO.StreamWriter(filename);

            if (output != null)
                output.Write(ToLaTeX(info, domain));

            output.Close();

            return name;
        }
    }

    public class DefinitionsForCopyPropagation : Optimization
    {
        public override ArrayOf<Info> Analysis(ArrayOf<Block> blocks, Set domain)
        {
            return ForwardAnalysis(blocks, domain, Meet.INTERSECTION);
        }

        public override ArrayOf<Info> Initialize(ArrayOf<Block> blocks, Set domain)
        {
            ArrayOf<Info> info = new ArrayOf<Info>();

            for (int i = 0; i < blocks.Count; i++)
                info.Add(new Info(domain, blocks[i]));

            return info;
        }

        public int FillDefinitionsForCopyPropagationInfo(Block block, Set UDef, ref BitSet[] gen, ref BitSet[] kill)
        {
            AbstractMachine.IntermediateCode code = block.Code;

            // A copy definition di in UDef of a variable x in Var reaches a
            // program point u if di occurs on some path from Start to u and is not followed
            // by any other definition of x on this path.

            for (int i = 0; i < code.Count; i++)
            {
                if (i > 0)
                {
                    gen[i] = gen[i] + gen[i - 1];
                    kill[i] = kill[i] + kill[i - 1];
                }

                if (code[i].GetType() != typeof(Nop))
                {
                    switch (code[i][0].Op)
                    {
                        case Operator.COPY:
                            foreach (Copy inst in gen[i])
                                if (inst[0].Arg1 == code[i].Target || inst[0].Arg2 == code[i].Target)
                                    gen[i].Remove(inst);
                            foreach (IntermediateInstruction inst in UDef)
                                if (inst.GetType() == typeof(Copy))
                                    if (inst[0].Arg1 == code[i].Target || inst[0].Arg2 == code[i].Target)
                                        kill[i].Add(inst);
                            gen[i].Add(code[i]);
                            break;

                        case Operator.NEG:
                            foreach (Copy inst in gen[i])
                                if (inst[0].Arg1 == code[i].Target || inst[0].Arg2 == code[i].Target)
                                    gen[i].Remove(inst);
                            foreach (IntermediateInstruction inst in UDef)
                                if (inst.GetType() == typeof(Copy))
                                    if (inst[0].Arg1 == code[i].Target || inst[0].Arg2 == code[i].Target)
                                        kill[i].Add(inst);
                            break;

                        case Operator.FROMARRAY:
                            foreach (Copy inst in gen[i])
                                if (inst[0].Arg1 == code[i].Target || inst[0].Arg2 == code[i].Target)
                                    gen[i].Remove(inst);
                            foreach (IntermediateInstruction inst in UDef)
                                if (inst.GetType() == typeof(Copy))
                                    if (inst[0].Arg1 == code[i].Target || inst[0].Arg2 == code[i].Target)
                                        kill[i].Add(inst);
                            break;

                        case Operator.DEC:
                        case Operator.INC:
                        case Operator.ADDRESS:
                        case Operator.FROMMEMORY:
                            foreach (Copy inst in gen[i])
                                if (inst[0].Arg1 == code[i].Target || inst[0].Arg2 == code[i].Target)
                                    gen[i].Remove(inst);
                            foreach (IntermediateInstruction inst in UDef)
                                if (inst.GetType() == typeof(Copy))
                                    if (inst[0].Arg1 == code[i].Target || inst[0].Arg2 == code[i].Target)
                                        kill[i].Add(inst);
                            break;

                        default:
                            break;
                    }
                }
            }

            return code.Count - 1;
        }

        public override void TransferFunction(ArrayOf<Block> blocks, Set domain, ref ArrayOf<Info> info)
        {
            for (int i = 0; i < blocks.Count; i++)
                info[i].last = FillDefinitionsForCopyPropagationInfo(blocks[i], domain, ref info[i].Gen, ref info[i].Kill);
        }

        public static string ToLaTeX(ArrayOf<Info> info, Set domain)
        {
            string str = "";
            int bk;

            string Title = "Alcan\\c{c}abilidade de Defini\\c{c}\\~oes para Propaga\\c{c}\\~ao de C\\'opias";

            str += "\\section{" + Title + "}\n\n";
            str += "\\begin{itemize}\n";
            str += "  \\item[$Gen$] ...\n";
            str += "  \\item[$Kill$] ...\n";
            str += "  \\item[$In$] ...\n";
            str += "  \\item[$In$] ...\n";
            str += "\\end{itemize}\n\n";

            str += "\\begin{table}[ht]\n";
            str += "\\centering\n";
            str += "\\begin{tabular}{l|l|l|l|l}\n";
            str += "\t& Gen & Kill & IN & OUT\\\\\n";
            str += "\\hline\n";
            for (bk = 1; bk < info.Count - 1; bk++)
            {
                int last = info[bk].last;
                str += "$B_{" + bk.ToString() + "}$ & ";
                str += " $" + info[bk].Gen[last].ToBinary() + "$ &" +
                    " $" + info[bk].Kill[last].ToBinary() + "$ &" +
                    " $" + info[bk].IN.ToBinary() + "$ &" +
                    " $" + info[bk].OUT.ToBinary() + "$\\\\\n";
            }
            str += "\\end{tabular}\n";
            str += "\\caption{" + Title + " --- $(" + domain.ToString() + ")$}\n";
            str += "\\end{table}\n\n";

            return str;
        }

        public static string Write(string path, ArrayOf<Info> info, Set domain)
        {
            string name = "DefinitionsForCopyPropagation.tex";
            string filename = Path.Combine(path, name);

            System.IO.StreamWriter output = new System.IO.StreamWriter(filename);

            if (output != null)
                output.Write(ToLaTeX(info, domain));

            output.Close();

            return name;
        }
    }

    public class LiveVariable : Optimization
    {
        public override ArrayOf<Info> Analysis(ArrayOf<Block> blocks, Set domain)
        {
            return BackwardAnalysis(blocks, domain, Meet.UNION);
        }

        public override ArrayOf<Info> Initialize(ArrayOf<Block> blocks, Set domain)
        {
            ArrayOf<Info> info = new ArrayOf<Info>();

            for (int i = 0; i < blocks.Count; i++)
                info.Add(new Info(domain, blocks[i]));

            return info;
        }

        public int FillLiveVariablesInfo(Block block, Set UVar, ref BitSet[] gen, ref BitSet[] kill)
        {
            AbstractMachine.IntermediateCode code = block.Code;

            // A variable x in UVar is live at a program point u if some
            // path from u to End contains a use of x which is not preceded by its definition.

            for (int i = code.Count - 1; i >= 0; i--)
            {
                if (i < code.Count - 1)
                {
                    gen[i] = gen[i] + gen[i + 1];
                    kill[i] = kill[i] + kill[i + 1];
                }

                if (code[i].Target != null)
                {
                    gen[i].Remove(code[i].Target);
                    kill[i].Add(code[i].Target);
                }

                if (code[i].GetType() != typeof(Nop))
                {
                    switch (code[i][0].Op)
                    {
                        case Operator.MUL:
                        case Operator.DIV:
                        case Operator.ADD:
                        case Operator.SUB:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                                gen[i].Add(code[i][0].Arg1);
                            if (code[i][0].Arg2.GetType() == typeof(Name))
                                gen[i].Add(code[i][0].Arg2);
                            break;

                        case Operator.DEC:
                        case Operator.INC:
                            gen[i].Add(code[i].Target);
                            break;

                        case Operator.NEG:
                            gen[i].Add(code[i].Target);
                            break;

                        case Operator.COPY:
                        case Operator.ADDRESS:
                            if (code[i][0].Arg2.GetType() == typeof(Name))
                                gen[i].Add(code[i][0].Arg2);
                            break;

                        case Operator.FROMMEMORY:
                            if (code[i][0].Arg2.GetType() == typeof(Name))
                                gen[i].Add(code[i][0].Arg2);
                            break;

                        case Operator.TOMEMORY:
                            gen[i].Add(code[i][0].Arg1);
                            if (code[i][0].Arg2.GetType() == typeof(Name))
                                gen[i].Add(code[i][0].Arg2);
                            break;

                        case Operator.IFTRUE:
                        case Operator.IFFALSE:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                                gen[i].Add(code[i][0].Arg1);
                            break;

                        case Operator.IFEXP:
                            if (code[i][1].Arg1.GetType() == typeof(Name))
                                gen[i].Add(code[i][1].Arg1);
                            if (code[i][1].Arg2.GetType() == typeof(Name))
                                gen[i].Add(code[i][1].Arg2);
                            break;

                        case Operator.PARAM:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                                gen[i].Add(code[i][0].Arg1);
                            break;

                        case Operator.RETURN:
                            if (code[i][0].Arg1 != null)
                                if (code[i][0].Arg1.GetType() == typeof(Name))
                                    gen[i].Add(code[i][0].Arg1);
                            break;

                        case Operator.FROMARRAY:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                                gen[i].Add(code[i][0].Arg1);
                            if (code[i][0].Arg2.GetType() == typeof(Name))
                                gen[i].Add(code[i][0].Arg2);
                            break;

                        case Operator.TOARRAY:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                                gen[i].Add(code[i][0].Arg1);
                            if (code[i][0].Arg2.GetType() == typeof(Name))
                                gen[i].Add(code[i][0].Arg2);
                            if (code[i][1].Arg1.GetType() == typeof(Name))
                                gen[i].Add(code[i][1].Arg1);
                            break;
                    }
                }
            }

            return 0;
        }

        public override void TransferFunction(ArrayOf<Block> blocks, Set domain, ref ArrayOf<Info> info)
        {
            for (int i = 0; i < blocks.Count; i++)
                info[i].last = FillLiveVariablesInfo(blocks[i], domain, ref info[i].Gen, ref info[i].Kill);
        }

        public static string ToLaTeX(ArrayOf<Info> info, Set domain)
        {
            string str = "";
            int bk;

            string Title = "Vivacidade de Vari\\'aveis";

            str += "\\section{" + Title + "}\n\n";
            str += "\\begin{itemize}\n";
            str += "  \\item[$Gen$] ...\n";
            str += "  \\item[$Kill$] ...\n";
            str += "  \\item[$IN$] ...\n";
            str += "  \\item[$OUT$] ...\n";
            str += "\\end{itemize}\n\n";
            str += "\n";
            str += "\\xymatrix{\n";
            str += "  & \\emptyset \\ar[dl]\\ar[d]\\ar[dr] & \\\\\n";
            str += "  \\{v_1\\} \\ar[d]\\ar[dr] & \\{v_2\\} \\ar[dl]\\ar[dr] & \\{v_3\\} \\ar[d]\\ar[dl] \\\\\n";
            str += "  \\{v_1,v_2\\} \\ar[dr] & \\{v_1,v_3\\} \\ar[d] & \\{v_2,v_3\\} \\ar[dl] \\\\\n";
            str += "  & \\{v_1,v_2,v_3\\} & \\\\\n";
            str += "}\n";
            str += "\n";

            str += "\\begin{table}[ht]\n";
            str += "\\centering\n";
            str += "\\begin{tabular}{l|l|l|l|l}\n";
            str += "\t& Gen & Kill & IN & OUT\\\\\n";
            str += "\\hline\n";
            for (bk = 1; bk < info.Count - 1; bk++)
            {
                int last = info[bk].last;
                str += "$B_{" + bk.ToString() + "}$ & ";
                str += " $" + info[bk].Gen[last].ToBinary() + "$ &" +
                    " $" + info[bk].Kill[last].ToBinary() + "$ &" +
                    " $" + info[bk].IN.ToBinary() + "$ &" +
                    " $" + info[bk].OUT.ToBinary() + "$\\\\\n";
            }
            str += "\\end{tabular}\n";
            str += "\\caption{" + Title + " --- $(" + domain.ToString() + ")$}\n";
            str += "\\end{table}\n\n";

            return str;
        }

        public static string Write(string path, ArrayOf<Info> info, Set domain)
        {
            string name = "LiveVariable.tex";
            string filename = Path.Combine(path, name);

            System.IO.StreamWriter output = new System.IO.StreamWriter(filename);

            if (output != null)
                output.Write(ToLaTeX(info, domain));

            output.Close();

            return name;
        }
    }

    public class DeadVariable : Optimization
    {
        public override ArrayOf<Info> Analysis(ArrayOf<Block> blocks, Set domain)
        {
            return BackwardAnalysis(blocks, domain, Meet.INTERSECTION);
        }

        public override ArrayOf<Info> Initialize(ArrayOf<Block> blocks, Set domain)
        {
            ArrayOf<Info> info = new ArrayOf<Info>();

            for (int i = 0; i < blocks.Count; i++)
                info.Add(new Info(domain, blocks[i]));

            for (int i = 1; i < blocks.Count; i++)
                info[i].IN.SetToOnes();

            return info;
        }

        public int FillDeadVariablesInfo(Block block, Set UVar, ref BitSet[] gen, ref BitSet[] kill)
        {
            AbstractMachine.IntermediateCode code = block.Code;

            // Gen will now contain all variables whose values are modified 
            // in the block such that the modifications are upwards exposed 
            // (i.e., are not preceded by a use of the variable). Kill 
            // will contain variables which are used anywhere regardless of 
            // what precedes or follows the uses.

            for (int i = code.Count - 1; i >= 0; i--)
            {
                if (i < code.Count - 1)
                {
                    gen[i] = gen[i] + gen[i + 1];
                    kill[i] = kill[i] + kill[i + 1];
                }

                if (code[i].Target != null)
                {
                    kill[i].Remove(code[i].Target);
                    gen[i].Add(code[i].Target);
                }

                if (code[i].GetType() != typeof(Nop))
                {
                    switch (code[i][0].Op)
                    {
                        case Operator.MUL:
                        case Operator.DIV:
                        case Operator.ADD:
                        case Operator.SUB:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                                kill[i].Add(code[i][0].Arg1);
                            if (code[i][0].Arg2.GetType() == typeof(Name))
                                kill[i].Add(code[i][0].Arg2);
                            break;

                        case Operator.DEC:
                        case Operator.INC:
                            //                        Kill.Add(code[i].Target);
                            break;

                        case Operator.NEG:
                            //                        Kill.Add(code[i].Target);
                            break;

                        case Operator.COPY:
                        case Operator.ADDRESS:
                            if (code[i][0].Arg2.GetType() == typeof(Name))
                                kill[i].Add(code[i][0].Arg2);
                            break;

                        case Operator.FROMMEMORY:
                            if (code[i][0].Arg2.GetType() == typeof(Name))
                                kill[i].Add(code[i][0].Arg2);
                            break;

                        case Operator.TOMEMORY:
                            kill[i].Add(code[i][0].Arg1);
                            if (code[i][0].Arg2.GetType() == typeof(Name))
                                kill[i].Add(code[i][0].Arg2);
                            break;

                        case Operator.IFTRUE:
                        case Operator.IFFALSE:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                                kill[i].Add(code[i][0].Arg1);
                            break;

                        case Operator.IFEXP:
                            if (code[i][1].Arg1.GetType() == typeof(Name))
                                kill[i].Add(code[i][1].Arg1);
                            if (code[i][1].Arg2.GetType() == typeof(Name))
                                kill[i].Add(code[i][1].Arg2);
                            break;

                        case Operator.PARAM:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                                kill[i].Add(code[i][0].Arg1);
                            break;

                        case Operator.RETURN:
                            if (code[i][0].Arg1 != null)
                                if (code[i][0].Arg1.GetType() == typeof(Name))
                                    kill[i].Add(code[i][0].Arg1);
                            break;

                        case Operator.FROMARRAY:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                                kill[i].Add(code[i][0].Arg1);
                            if (code[i][0].Arg2.GetType() == typeof(Name))
                                kill[i].Add(code[i][0].Arg2);
                            break;

                        case Operator.TOARRAY:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                                kill[i].Add(code[i][0].Arg1);
                            if (code[i][0].Arg2.GetType() == typeof(Name))
                                kill[i].Add(code[i][0].Arg2);
                            if (code[i][1].Arg1.GetType() == typeof(Name))
                                kill[i].Add(code[i][1].Arg1);
                            break;
                    }
                }
            }

            return 0;
        }

        public override void TransferFunction(ArrayOf<Block> blocks, Set domain, ref ArrayOf<Info> info)
        {
            for (int i = 0; i < blocks.Count; i++)
                info[i].last = FillDeadVariablesInfo(blocks[i], domain, ref info[i].Gen, ref info[i].Kill);
        }

        public static string ToLaTeX(ArrayOf<Info> info, Set domain)
        {
            string str = "";
            int bk;

            string Title = "Mortalidade de Vari\\'aveis";

            str += "\\section{" + Title + "}\n\n";
            str += "\\begin{itemize}\n";
            str += "  \\item[$Gen$] ...\n";
            str += "  \\item[$Kill$] ...\n";
            str += "  \\item[$In$] ...\n";
            str += "  \\item[$In$] ...\n";
            str += "\\end{itemize}\n\n";

            str += "\\begin{table}[ht]\n";
            str += "\\centering\n";
            str += "\\begin{tabular}{l|l|l|l|l}\n";
            str += "\t& Gen & Kill & IN & OUT\\\\\n";
            str += "\\hline\n";
            for (bk = 1; bk < info.Count - 1; bk++)
            {
                int last = info[bk].last;
                str += "$B_{" + bk.ToString() + "}$ & ";
                str += " $" + info[bk].Gen[last].ToBinary() + "$ &" +
                    " $" + info[bk].Kill[last].ToBinary() + "$ &" +
                    " $" + info[bk].IN.ToBinary() + "$ &" +
                    " $" + info[bk].OUT.ToBinary() + "$\\\\\n";
            }
            str += "\\end{tabular}\n";
            str += "\\caption{" + Title + " --- $(" + domain.ToString() + ")$}\n";
            str += "\\end{table}\n\n";

            return str;
        }

        public static string Write(string path, ArrayOf<Info> info, Set domain)
        {
            string name = "DeadVariable.tex";
            string filename = Path.Combine(path, name);

            System.IO.StreamWriter output = new System.IO.StreamWriter(filename);

            if (output != null)
                output.Write(ToLaTeX(info, domain));

            output.Close();

            return name;
        }
    }

    public class AvailableExpressions : Optimization
    {
        // Available expressions is another classical data flow analysis, 
        // used in compiler construction to determine when the value of a 
        // subexpression can be saved and reused rather than recomputed. 
        // This is permissible when the value of the subexpression remains 
        // unchanged regardless of the execution path from the first 
        // computation to the second.
        // 
        // Available expressions can be defined in terms of paths in the 
        // control flow graph. An expression is available at a point if, 
        // for all paths through the control flow graph from procedure 
        // entry to that point, the expression has been computed and not 
        // subsequently modified. We say an expression is generated 
        // (becomes available) where it is computed and is killed (ceases 
        // to be available) when the value of any part of it changes (e.g., 
        // when a new value is assigned to a variable in the expression).
        // 
        // As with reaching definitions, we can obtain an efficient 
        // analysis by describing the relation between the available 
        // expressions that reach a node in the control flow graph and 
        // those at adjacent nodes. The expressions that become available 
        // at each node (the gen set) and the expressions that change and 
        // cease to be available (the kill set) can be computed simply, 
        // without consideration of control flow. Their propagation to a 
        // node from its predecessors is described by a pair of set 
        // equations:
        // 
        // The similarity to the set equations for reaching definitions is 
        // striking. Both propagate sets of values along the control flow 
        // graph in the direction of program execution (they are forward 
        // analyses), and both combine sets propagated along different 
        // control flow paths. However, reaching definitions combines 
        // propagated sets using set union, since a definition can reach a 
        // use along any execution path. Available expressions combines 
        // propagated sets using set intersection, since an expression is 
        // considered available at a node only if it reaches that node 
        // along all possible execution paths. Thus we say that, while 
        // reaching definitions is a forward, any-path analysis, available 
        // expressions is a forward, all-paths analysis. A work-list 
        // algorithm to implement available expressions analysis is nearly 
        // identical to that for reaching definitions, except for 
        // initialization and the flow equations, as shown in Figure 6.7.
        // 
        // 
        //     Algorithm Available expressions
        //     
        //         Input:   A control flow graph G =(nodes,edges), with a distinguished root node start.
        //                  pred(n)= {m in nodes | (m,n) in edges}
        //                  succ(m)= {n in nodes | (m,n) in edges}
        //                  gen(n)= all expressions e computed at node n
        //                  kill(n)= expressions e computed anywhere, whose value is changed at n;
        //                      kill(start) is the set of all e.
        //         Output: Avail(n)= the available expressions at node n
        //     
        //         for n in nodes loop
        //             AvailOut(n)= set of all e defined anywhere ;
        //         end loop;
        //         workList = nodes ;
        //         while (workList = {}) loop
        //             // Take a node from worklist (e.g., pop from stack or queue)
        //             n = any node in workList ;
        //             workList = workList \ {n} ;
        //             oldVal = AvailOut(n) ;
        //             // Apply flow equations, propagating values from predecessors
        //             Avail(n) = Union[m in pred(n)], AvailOut(m);
        //             AvailOut(n)=(Avail(n) \ kill(n)) union gen(n) ;
        //             if ( AvailOut(n) != oldVal ) then
        //                  // Propagate changes to successors
        //                  workList = workList union succ(n)
        //             end if;
        //         end loop;

        private BitSet[] Redundant;

        public override ArrayOf<Info> Analysis(ArrayOf<Block> blocks, Set domain)
        {
            ArrayOf<Info> info = ForwardAnalysis(blocks, domain, Meet.INTERSECTION);
            Redundant = new BitSet[blocks.Count];

            for (int B = 0; B < blocks.Count; B++)
                for (int i = 0; i < blocks[B].Size; i++)
                    Redundant[B] = info[B].Gen[i] * info[B].IN;

            return info;
        }

        public override ArrayOf<Info> Initialize(ArrayOf<Block> blocks, Set domain)
        {
            ArrayOf<Info> info = new ArrayOf<Info>();

            for (int i = 0; i < blocks.Count; i++)
                info.Add(new Info(domain, blocks[i]));

            info[0].OUT.SetToZeros();
            for (int i = 1; i < blocks.Count; i++)
                info[i].OUT.SetToOnes();

            return info;
        }

        public int FillAvailableExpressionsInfo(Block block, Set UExp, ref BitSet[] gen, ref BitSet[] kill)
        {
            AbstractMachine.IntermediateCode code = block.Code;

            // An expression e in UExp is available at a program point
            // u if all paths from Start to u contain a computation of e which is not followed
            // by an assignment to any of its operands.

            for (int i = 0; i < code.Count; i++)
            {
                if (i > 0)
                {
                    gen[i] = gen[i] + gen[i - 1];
                    kill[i] = kill[i] + kill[i - 1];
                }

                if (code[i].GetType() != typeof(Nop))
                {
                    switch (code[i][0].Op)
                    {
                        case Operator.MUL:
                        case Operator.DIV:
                        case Operator.ADD:
                        case Operator.SUB:
                            foreach (TAC inst in gen[i])
                                if (inst.Arg1 == code[i][1].Arg2 || inst.Arg2 == code[i][1].Arg2)
                                    gen[i].Remove(inst);
                            gen[i].Add(code[i][0]);
                            foreach (TAC inst in UExp)
                                if (inst.Arg1 == code[i][1].Arg2 || inst.Arg2 == code[i][1].Arg2)
                                    kill[i].Add(inst);
                            break;

                        case Operator.DEC:
                        case Operator.INC:
                            foreach (TAC inst in gen[i])
                                if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                    gen[i].Remove(inst);
                            gen[i].Add(code[i][0]);
                            foreach (TAC inst in UExp)
                                if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                    kill[i].Add(inst);
                            break;

                        case Operator.COPY:
                        case Operator.ADDRESS:
                        case Operator.FROMMEMORY:
                            foreach (TAC inst in gen[i])
                                if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                    gen[i].Remove(inst);
                            foreach (TAC inst in UExp)
                                if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                    kill[i].Add(inst);
                            break;

                        case Operator.NEG:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                            {
                                foreach (TAC inst in gen[i])
                                    if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                        gen[i].Remove(inst);
                                foreach (TAC inst in UExp)
                                    if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                        kill[i].Add(inst);
                            }
                            break;

                        case Operator.FROMARRAY:
                            if (code[i][1].Arg1.GetType() == typeof(Name))
                            {
                                foreach (TAC inst in gen[i])
                                    if (inst.Arg1 == code[i][1].Arg1 || inst.Arg2 == code[i][1].Arg1)
                                        gen[i].Remove(inst);
                                foreach (TAC inst in UExp)
                                    if (inst.Arg1 == code[i][1].Arg1 || inst.Arg2 == code[i][1].Arg1)
                                        kill[i].Add(inst);
                            }
                            break;

                        default:
                            break;
                    }
                }
            }

            return code.Count - 1;
        }

        public override void TransferFunction(ArrayOf<Block> blocks, Set domain, ref ArrayOf<Info> info)
        {
            for (int i = 0; i < blocks.Count; i++)
                info[i].last = FillAvailableExpressionsInfo(blocks[i], domain, ref info[i].Gen, ref info[i].Kill);
        }

        public static string ToLaTeX(ArrayOf<Info> info, Set domain)
        {
            string str = "";
            int bk;

            string Title = "Disponibilidade de Express\\~oes";

            str += "\\section{" + Title + "}\n\n";
            str += "A an\\'alise \\'e para frente (\\textsf{forward}) e sua inten\\c{c}\\~ao \\'e determinar em cada ponto do c\\'odigo, quais express\\~oes est\\~ao dispon\\'iveis, isto \\'e, foram seguramente executadas e, caso fossem executadas novamente (naquele ponto) produziriam o mesmo resultado.\n";
            str += "\\begin{itemize}\n";
            str += "  \\item[$Gen$] Indica quais express\\~oes foram geradas dentro do bloco e que n\\~ao foram ``mortas\'\' por redefini\\c{c}\\~oes de seus operandos dentro do mesmo bloco. {\\color{red} \\'E igual \\`a entrada das express\\~oes antecip\\'aveis}.\n";
            str += "  \\item[$Kill$] Indica quais express\\~oes (considerando o universo inteiro) foram mortas por redefini\\c{c}\\~oes (posteriores~\\footnote{S\\'o faz sentido em an\\'alises internas ao bloco.}) de seus operandos que ocorrem dentro do bloco.\n";
            str += "  \\item[$IN$] Indica quais express\\~oes est\\~ao dispon\\'iveis na entrada do bloco. \\'E uma interse\\c{c}\\~ao das sa\\'idas dos blocos predecessores.\n";
            str += "  \\item[$OUT$] Indica quais express\\~oes est\\~ao dispon\\'iveis na sa\\'ida do bloco. {\\color{red} \\'E igual ao \\'ultimo $Gen$}.\n";
            str += "\\end{itemize}\n\n";
            str += "\n";
            str += "\\xymatrix{\n";
            str += "  & \\{e_1,e_2,e_3\\} \\ar[dl]\\ar[d]\\ar[dr] & \\\\\n";
            str += "  \\{e_1,e_2\\} \\ar[d]\\ar[dr] & \\{e_1,e_3\\} \\ar[dl]\\ar[dr] & \\{e_2,e_3\\} \\ar[d]\\ar[dl] \\\\\n";
            str += "  \\{e_1\\} \\ar[dr] & \\{e_2\\} \\ar[d] & \\{e_3\\} \\ar[dl] \\\\\n";
            str += "  & \\emptyset & \\\\\n";
            str += "}\n";
            str += "\n";

            str += "\\begin{table}[ht]\n";
            str += "\\centering\n";
            str += "\\begin{tabular}{l|l|l|l|l}\n";
            str += "\t& Gen & Kill & IN & OUT\\\\\n";
            str += "\\hline\n";
            for (bk = 1; bk < info.Count - 1; bk++)
            {
                int last = info[bk].last;
                str += "$B_{" + bk.ToString() + "}$ & ";
                str += " $" + info[bk].Gen[last].ToBinary() + "$ &" +
                    " $" + info[bk].Kill[last].ToBinary() + "$ &" +
                    " $" + info[bk].IN.ToBinary() + "$ &" +
                    " $" + info[bk].OUT.ToBinary() + "$\\\\\n";
            }
            str += "\\end{tabular}\n";
            str += "\\caption{" + Title + " --- $(" + domain.ToString() + ")$}\n";
            str += "\\end{table}\n\n";

            return str;
        }

        public static string Write(string path, ArrayOf<Info> info, Set domain)
        {
            string name = "AvailableExpressions.tex";
            string filename = Path.Combine(path, name);

            System.IO.StreamWriter output = new System.IO.StreamWriter(filename);

            if (output != null)
                output.Write(ToLaTeX(info, domain));

            output.Close();

            return name;
        }
    }

    public class PartiallyAvailableExpressions : Optimization
    {
        private BitSet[] ParRedund;

        public override ArrayOf<Info> Analysis(ArrayOf<Block> blocks, Set domain)
        {
            ArrayOf<Info> info = ForwardAnalysis(blocks, domain, Meet.UNION);
            ParRedund = new BitSet[blocks.Count];

            for (int B = 0; B < blocks.Count; B++)
                for (int i = 0; i < blocks[B].Size; i++)
                    ParRedund[B] = info[B].Gen[i] * info[B].IN;

            return info;
        }

        public override ArrayOf<Info> Initialize(ArrayOf<Block> blocks, Set domain)
        {
            ArrayOf<Info> info = new ArrayOf<Info>();

            for (int i = 0; i < blocks.Count; i++)
                info.Add(new Info(domain, blocks[i]));

            return info;
        }

        public int FillAvailableExpressionsInfo(Block block, Set UExp, ref BitSet[] gen, ref BitSet[] kill)
        {
            AbstractMachine.IntermediateCode code = block.Code;

            // An expression e in UExp is available at a program point
            // u if all paths from Start to u contain a computation of e which is not followed
            // by an assignment to any of its operands.

            for (int i = 0; i < code.Count; i++)
            {
                if (i > 0)
                {
                    gen[i] = gen[i] + gen[i - 1];
                    kill[i] = kill[i] + kill[i - 1];
                }

                if (code[i].GetType() != typeof(Nop))
                {
                    switch (code[i][0].Op)
                    {
                        case Operator.MUL:
                        case Operator.DIV:
                        case Operator.ADD:
                        case Operator.SUB:
                            foreach (TAC inst in gen[i])
                                if (inst.Arg1 == code[i][1].Arg2 || inst.Arg2 == code[i][1].Arg2)
                                    gen[i].Remove(inst);
                            gen[i].Add(code[i][0]);
                            foreach (TAC inst in UExp)
                                if (inst.Arg1 == code[i][1].Arg2 || inst.Arg2 == code[i][1].Arg2)
                                    kill[i].Add(inst);
                            break;

                        case Operator.DEC:
                        case Operator.INC:
                            foreach (TAC inst in gen[i])
                                if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                    gen[i].Remove(inst);
                            gen[i].Add(code[i][0]);
                            foreach (TAC inst in UExp)
                                if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                    kill[i].Add(inst);
                            break;

                        case Operator.COPY:
                        case Operator.ADDRESS:
                        case Operator.FROMMEMORY:
                            foreach (TAC inst in gen[i])
                                if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                    gen[i].Remove(inst);
                            foreach (TAC inst in UExp)
                                if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                    kill[i].Add(inst);
                            break;

                        case Operator.NEG:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                            {
                                foreach (TAC inst in gen[i])
                                    if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                        gen[i].Remove(inst);
                                foreach (TAC inst in UExp)
                                    if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                        kill[i].Add(inst);
                            }
                            break;

                        case Operator.FROMARRAY:
                            if (code[i][1].Arg1.GetType() == typeof(Name))
                            {
                                foreach (TAC inst in gen[i])
                                    if (inst.Arg1 == code[i][1].Arg1 || inst.Arg2 == code[i][1].Arg1)
                                        gen[i].Remove(inst);
                                foreach (TAC inst in UExp)
                                    if (inst.Arg1 == code[i][1].Arg1 || inst.Arg2 == code[i][1].Arg1)
                                        kill[i].Add(inst);
                            }
                            break;

                        default:
                            break;
                    }
                }
            }

            return code.Count - 1;
        }

        public override void TransferFunction(ArrayOf<Block> blocks, Set domain, ref ArrayOf<Info> info)
        {
            for (int i = 0; i < blocks.Count; i++)
                info[i].last = FillAvailableExpressionsInfo(blocks[i], domain, ref info[i].Gen, ref info[i].Kill);
        }

        public static string ToLaTeX(ArrayOf<Info> info, Set domain)
        {
            string str = "";
            int bk;

            string Title = "Disponibilidade Parcial de Express\\~oes";

            str += "\\section{" + Title + "}\n\n";
            str += "\\begin{itemize}\n";
            str += "  \\item[$Gen$] ...\n";
            str += "  \\item[$Kill$] ...\n";
            str += "  \\item[$IN$] ...\n";
            str += "  \\item[$OUT$] ...\n";
            str += "\\end{itemize}\n\n";

            str += "\\begin{table}[ht]\n";
            str += "\\centering\n";
            str += "\\begin{tabular}{l|l|l|l|l}\n";
            str += "\t& Gen & Kill & IN & OUT\\\\\n";
            str += "\\hline\n";
            for (bk = 1; bk < info.Count - 1; bk++)
            {
                int last = info[bk].last;
                str += "$B_{" + bk.ToString() + "}$ & ";
                str += " $" + info[bk].Gen[last].ToBinary() + "$ &" +
                    " $" + info[bk].Kill[last].ToBinary() + "$ &" +
                    " $" + info[bk].IN.ToBinary() + "$ &" +
                    " $" + info[bk].OUT.ToBinary() + "$\\\\\n";
            }
            str += "\\end{tabular}\n";
            str += "\\caption{" + Title + " --- $(" + domain.ToString() + ")$}\n";
            str += "\\end{table}\n\n";

            return str;
        }

        public static string Write(string path, ArrayOf<Info> info, Set domain)
        {
            string name = "PartiallyAvailableExpressions.tex";
            string filename = Path.Combine(path, name);

            System.IO.StreamWriter output = new System.IO.StreamWriter(filename);

            if (output != null)
                output.Write(ToLaTeX(info, domain));

            output.Close();

            return name;
        }
    }

    public class AnticipableExpressions : Optimization
    {
        public override ArrayOf<Info> Analysis(ArrayOf<Block> blocks, Set domain)
        {
            return BackwardAnalysis(blocks, domain, Meet.INTERSECTION);
        }

        public override ArrayOf<Info> Initialize(ArrayOf<Block> blocks, Set domain)
        {
            ArrayOf<Info> info = new ArrayOf<Info>();

            for (int i = 0; i < blocks.Count; i++)
                info.Add(new Info(domain, blocks[i]));

            for (int i = 0; i < blocks.Count - 1; i++)
                info[i].IN.SetToOnes();
            info[blocks.Count - 1].IN.SetToZeros();

            return info;
        }

        public int FillAnticipableExpressionsInfo(Block block, Set UExp, ref BitSet[] gen, ref BitSet[] kill)
        {
            AbstractMachine.IntermediateCode code = block.Code;

            // An expression e in UExp is anticipable at a program
            // point u if every path from u to End contains a computation of e which is not
            // preceded by an assignment to any operand of e.

            for (int i = code.Count - 1; i >= 0; i--)
            {
                if (i < code.Count - 1)
                {
                    gen[i] = gen[i] + gen[i + 1];
                    kill[i] = kill[i] + kill[i + 1];
                }
                if (code[i].GetType() != typeof(Nop))
                {
                    switch (code[i][0].Op)
                    {
                        case Operator.MUL:
                        case Operator.DIV:
                        case Operator.ADD:
                        case Operator.SUB:
                            foreach (TAC inst in gen[i])
                                if (inst.Arg1 == code[i][1].Arg2 || inst.Arg2 == code[i][1].Arg2)
                                    gen[i].Remove(inst);
                            gen[i].Add(code[i][0]);
                            foreach (TAC inst in UExp)
                                if (inst.Arg1 == code[i][1].Arg2 || inst.Arg2 == code[i][1].Arg2)
                                    kill[i].Add(inst);
                            break;

                        case Operator.DEC:
                        case Operator.INC:
                            foreach (TAC inst in gen[i])
                                if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                    gen[i].Remove(inst);
                            gen[i].Add(code[i][0]);
                            foreach (TAC inst in UExp)
                                if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                    kill[i].Add(inst);
                            break;

                        case Operator.COPY:
                        case Operator.ADDRESS:
                        case Operator.FROMMEMORY:
                            foreach (TAC inst in gen[i])
                                if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                    gen[i].Remove(inst);
                            foreach (TAC inst in UExp)
                                if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                    kill[i].Add(inst);
                            break;

                        case Operator.NEG:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                            {
                                foreach (TAC inst in gen[i])
                                    if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                        gen[i].Remove(inst);
                                foreach (TAC inst in UExp)
                                    if (inst.Arg1 == code[i][0].Arg1 || inst.Arg2 == code[i][0].Arg1)
                                        kill[i].Add(inst);
                            }
                            break;

                        case Operator.FROMARRAY:
                            if (code[i][1].Arg1.GetType() == typeof(Name))
                            {
                                foreach (TAC inst in gen[i])
                                    if (inst.Arg1 == code[i][1].Arg1 || inst.Arg2 == code[i][1].Arg1)
                                        gen[i].Remove(inst);
                                foreach (TAC inst in UExp)
                                    if (inst.Arg1 == code[i][1].Arg1 || inst.Arg2 == code[i][1].Arg1)
                                        kill[i].Add(inst);
                            }
                            break;

                        default:
                            break;
                    }
                }
            }

            return 0;
        }

        public override void TransferFunction(ArrayOf<Block> blocks, Set domain, ref ArrayOf<Info> info)
        {
            for (int i = 0; i < blocks.Count; i++)
                info[i].last = FillAnticipableExpressionsInfo(blocks[i], domain, ref info[i].Gen, ref info[i].Kill);
        }

        public static string ToLaTeX(ArrayOf<Info> info, Set domain)
        {
            string str = "";
            int bk;

            string Title = "Disponibilidade de Express\\~oes Anticip\\'aveis";

            str += "\\section{" + Title + "}\n\n";
            str += "A an\\'alise \\'e para tr\\'as (\\textsf{backward}) e sua inten\\c{c}\\~ao \\'e determinar em cada ponto do c\\'odigo, quais express\\~oes podem ser movidas para o in\\'icio do bloco (ou para blocos antecedentes).\n";
            str += "\\begin{itemize}\n";
            str += "  \\item[$Gen$] Indica quais express\\~oes podem ser movidas para o in\\'icio do bloco (ou para blocos antecedentes).\n";
            str += "  \\item[$Kill$] Indica quais express\\~oes (considerando o universo inteiro) foram mortas por redefini\\c{c}\\~oes (anteriores~\\footnote{S\\'o faz sentido em an\\'alises internas ao bloco.}) de seus operandos que ocorrem dentro do bloco.\n";
            str += "  \\item[$IN$] Indica quais express\\~oes podem ser movidas para blocos antecedentes.\n";
            str += "  \\item[$OUT$] Indica quais express\\~oes de blocos subsequ\\^entes podem ser movidas para o final do bloco atual -- estas express\\~oes podem ou n\\~ao serem antecipadas pelo bloco atual.\n";
            str += "\\end{itemize}\n\n";

            str += "\\begin{table}[ht]\n";
            str += "\\centering\n";
            str += "\\begin{tabular}{l|l|l|l|l}\n";
            str += "\t& Gen & Kill & IN & OUT\\\\\n";
            str += "\\hline\n";
            for (bk = 1; bk < info.Count - 1; bk++)
            {
                int last = info[bk].last;
                str += "$B_{" + bk.ToString() + "}$ & ";
                str += " $" + info[bk].Gen[last].ToBinary() + "$ &" +
                    " $" + info[bk].Kill[last].ToBinary() + "$ &" +
                    " $" + info[bk].IN.ToBinary() + "$ &" +
                    " $" + info[bk].OUT.ToBinary() + "$\\\\\n";
            }
            str += "\\end{tabular}\n";
            str += "\\caption{" + Title + " --- $(" + domain.ToString() + ")$}\n";
            str += "\\end{table}\n\n";

            return str;
        }

        public static string Write(string path, ArrayOf<Info> info, Set domain)
        {
            string name = "AnticipableExpressions.tex";
            string filename = Path.Combine(path, name);

            System.IO.StreamWriter output = new System.IO.StreamWriter(filename);

            if (output != null)
                output.Write(ToLaTeX(info, domain));

            output.Close();

            return name;
        }
    }
}
