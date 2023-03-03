using System;
using System.Collections;
using SetCollection;
using AbstractMachine;
using Cormen;
using System.IO;

namespace IntermediateCode
{
    public class PartialRedundancy
    {
        public struct Info
        {
            public Info(Set U, Block B)
            {
                this.U = U;
                Gen = new BitSet[4][];
                Kill = new BitSet[4][];
                IN = new BitSet[4];
                OUT = new BitSet[4];
                for (int j = 0; j < 4; j++)
                {
                    Gen[j] = new BitSet[B.Size];
                    Kill[j] = new BitSet[B.Size];
                    for (int i = 0; i < B.Size; i++)
                    {
                        Gen[j][i] = new BitSet(U);
                        Kill[j][i] = new BitSet(U);
                    }
                    IN[j] = new BitSet(U);
                    OUT[j] = new BitSet(U);
                }
                last = -1;

                cond1 = null;
                cond2 = null;

                earliest = null;
                latest = null;

                e_use = null;
                e_kill = null;
            }
            public Set U;
            public int last;
            public BitSet[][] Gen;
            public BitSet[][] Kill;
            public BitSet[] IN;
            public BitSet[] OUT;
            public BitSet cond1;
            public BitSet cond2;
            public BitSet earliest;
            public BitSet latest;
            public BitSet e_use;
            public BitSet e_kill;

            public override string ToString()
            {
                string str = "";

                str += IN[3].ToBinary() + " " + OUT[3].ToBinary() + "\n";

                return str;
            }
        };

        private static int FillAnticipableExpressionsInfo(Block block, Set UExp, ref BitSet[] gen, ref BitSet[] kill)
        {
            // An expression e in UExp is anticipable at a program
            // point u if every path from u to End contains a computation of e which is not
            // preceded by an assignment to any operand of e.

            AbstractMachine.IntermediateCode code = block.Code;

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

        public static Info[] Analysis(ArrayOfBlock blocks, Set domain)
        {
            Info[] info = new Info[blocks.Count];
            for (int i = 0; i < blocks.Count; i++)
                info[i] = new Info(domain, blocks[i]);

            #region Informações locais aos blocos
            for (int i = 0; i < blocks.Count; i++)
            {
                info[i].last = FillAnticipableExpressionsInfo(blocks[i], domain, ref info[i].Gen[0], ref info[i].Kill[0]);
                info[i].e_use = info[i].Gen[0][0];
                info[i].e_kill = info[i].Kill[0][0];
            }
            #endregion

            #region Backward Analysis
            for (int i = 0; i < blocks.Count - 1; i++)
                info[i].IN[0].SetToOnes();
            info[blocks.Count - 1].IN[0].SetToZeros();

            bool done = false;
            while (!done)
            {
                done = true;
                for (int i = blocks.Count - 2; i >= 0; i--)
                {
                    int last = info[i].last;

                    info[i].OUT[0].SetToOnes();
                    foreach (Block succ in blocks[i].Sucessor)
                        info[i].OUT[0] = info[i].OUT[0] * info[succ.Id].IN[0];

                    if (blocks[i].Size > 0)
                    {
                        BitSet old = info[i].IN[0];
                        info[i].IN[0] = info[i].e_use + (info[i].OUT[0] - info[i].e_kill);
                        done = done && (old == info[i].IN[0]);
                    }
                }
            }
            #endregion

            #region Available Expressions
            for (int i = 1; i < blocks.Count; i++)
                info[i].OUT[1].SetToOnes();
            info[0].OUT[1].SetToZeros();

            // Forward Analysis
            done = false;
            while (!done)
            {
                done = true;
                for (int i = 1; i < blocks.Count; i++)
                {
                    info[i].IN[1].SetToOnes();
                    foreach (Block pred in blocks[i].Predecessor)
                        info[i].IN[1] = info[i].IN[1] * info[pred.Id].OUT[1];

                    if (blocks[i].Size > 0)
                    {
                        BitSet old = info[i].OUT[1];
                        info[i].OUT[1] = (info[i].IN[0] + info[i].IN[1]) - info[i].e_kill;
                        done = done && (old == info[i].OUT[1]);
                    }
                }
            }
            #endregion

            #region Postponable Expressions
            for (int i = 1; i < blocks.Count; i++)
                info[i].OUT[2].SetToOnes();
            info[0].OUT[2].SetToZeros();

            // earliest
            for (int i = 0; i < blocks.Count; i++)
            {
                for (int j = 0; j < blocks[i].Size; j++)
                    info[i].Gen[2][j] = info[i].Gen[0][j];
                info[i].earliest = info[i].IN[0] - info[i].IN[1];
            }

            // Forward Analysis
            done = false;
            while (!done)
            {
                done = true;
                for (int i = 1; i < blocks.Count; i++)
                {
                    int last = info[i].last;

                    info[i].IN[2].SetToOnes();
                    foreach (Block pred in blocks[i].Predecessor)
                        info[i].IN[2] = info[i].IN[2] * info[pred.Id].OUT[2];

                    if (blocks[i].Size > 0)
                    {
                        BitSet old = info[i].OUT[2];
                        info[i].OUT[2] = (info[i].earliest + info[i].IN[2]) - info[i].e_use;
                        done = done && (old == info[i].OUT[2]);
                    }
                }
            }
            #endregion

            #region Used Expressions
            for (int i = 0; i < blocks.Count - 1; i++)
                info[i].IN[3].SetToZeros();
            info[blocks.Count - 1].IN[3].SetToZeros();

            // latest
            for (int i = 0; i < blocks.Count; i++)
            {
                BitSet tmp = new BitSet(domain);

                tmp.SetToOnes();
                foreach (Block succ in blocks[i].Sucessor)
                    tmp = tmp * (info[succ.Id].earliest + info[succ.Id].IN[2]);

                tmp = info[i].e_use + !tmp;

                info[i].latest = tmp * (info[i].earliest + info[i].IN[2]);
            }

            // Backward Analysis
            done = false;
            while (!done)
            {
                done = true;
                for (int i = blocks.Count - 2; i >= 0; i--)
                {
                    int last = info[i].last;

                    info[i].OUT[3].SetToZeros();
                    foreach (Block succ in blocks[i].Sucessor)
                        info[i].OUT[3] = info[i].OUT[3] + info[succ.Id].IN[3];

                    if (blocks[i].Size > 0)
                    {
                        BitSet old = info[i].IN[3];
                        info[i].IN[3] = (info[i].e_use + info[i].OUT[3]) - info[i].latest;
                        done = done && (old == info[i].IN[3]);
                    }
                }
            }
            #endregion

            return info;
        }

        public static void Optimize(ArrayOfBlock blocks, Info[] info, Set domain)
        { 
            for (int i = 0; i < blocks.Count; i++)
            {
                info[i].cond1 = info[i].latest * info[i].OUT[3];
                info[i].cond2 = info[i].e_use * (!info[i].latest + info[i].OUT[3]);
            }

            for (int i = 0; i < domain.Count; i++)
            {
                Name tmp = new Name();

                for (int bk = 0; bk < blocks.Count - 1; bk++)
                {
                    if (info[bk].cond2[i])
                    {
                        for (int j = 0; j < blocks[bk].Code.Count; j++)
                        {
                            if (blocks[bk].Code[j][0].Op == ((TAC)domain[i]).Op &&
                                blocks[bk].Code[j][0].Arg1 == ((TAC)domain[i]).Arg1 &&
                                blocks[bk].Code[j][0].Arg2 == ((TAC)domain[i]).Arg2)
                            {
                                Address trg = blocks[bk].Code[j].Target;
                                blocks[bk].Code.ReplaceInstruction(j, blocks[bk].Code.CreateCopy(trg, tmp));
                            }
                        }
                    }
                }

                for (int bk = 0; bk < blocks.Count - 1; bk++)
                {
                    if (info[bk].cond1[i])
                    {
                        IntermediateInstruction inst = blocks[bk].Code.CreateBinary(
                            ((TAC)domain[i]).Op,
                            tmp,
                            ((TAC)domain[i]).Arg1,
                            ((TAC)domain[i]).Arg2
                            );
                        blocks[bk].Code.InsertInstruction(0, inst);
                    }
                }
            }
        }

        public static string ToLaTeX(Info[] info, Set domain)
        {
            string str = "";
            int bk;

            string Title = "Elimina\\c{c}\\~ao de Redund\\^ancias Parciais";

            str += "\\section{" + Title + "}\n\n";
            str += "\n";
            str += "\\subsection{Express\\~ao Redundante}\n";
            str += "\n";
            str += "Uma express\\~ao \\'e \\emph{redundante} no ponto $p$ se em cada caminho at\\'e $p$:\n";
            str += "\\begin{enumerate}\n";
            str += "  \\item Ela \\'e avaliada antes de alcan\\c{c}ar $p$, e\n";
            str += "  \\item Nenhum de seus operandos constituintes \\'e redefinido antes de $p$.\n";
            str += "\\end{enumerate}\n";
            str += "\n";
            str += "Por exemplo, na Equa\\c{c}\\~ao~\\ref{eq:ExpRed}, as ocorr\\^encias de express\\~oes em negrito s\\~ao redundantes.\n";
            str += "\n";
            str += "\\begin{equation}\n";
            str += "\\centering\n";
            str += "  \\xymatrix {\n";
            str += "    \\txt{$a \\leftarrow b+c$\\\\$a \\leftarrow \\mathbf{b+c}$} \\ar[dr] & & \\txt{$a \\leftarrow b+c$} \\ar[dl] \\\\\n";
            str += "                   & \\txt{$a \\leftarrow \\mathbf{b+c}$} \\ar[dl] \\ar[dr] & \\\\\n";
            str += "    \\txt{$a \\leftarrow \\mathbf{b+c}$} & & \\txt{$b \\leftarrow 1$\\\\$a \\leftarrow b+c$} \n";
            str += "  }\n";
            str += "\\label{eq:ExpRed}\n";
            str += "\\end{equation}\n";
            str += "\n";
            str += "Uma express\\~ao \\'e \\emph{parcialmente redundante} no ponto $p$ se ela \\'e redundante ao longo de alguns caminhos, mas n\\~ao todos, at\\'e $p$.\n";
            str += "\n";
            str += "Por exemplo, na Equa\\c{c}\\~ao~\\ref{eq:ExpParRed}, a express\\~ao $b+c$ em negrido no diagrama da esquerda \\'e parcialmente redundante.\n";
            str += "A inser\\c{c}\\~ao de uma c\\'opia de $b+c$ depois da defini\\c{c}\\~ao de $b$ pode tornar uma express\\c{c}\\~ao parcialmente redundante em uma totalmente redundante como mostra o diagrama da direita.\n";
            str += "\n";
            str += "\\begin{equation}\n";
            str += "\\centering\n";
            str += "  \\xymatrix {\n";
            str += "    \\txt{$b \\leftarrow b+1$} \\ar[dr] & & \\txt{$a \\leftarrow b+c$} \\ar[dl] & \\txt{$b \\leftarrow b+1$\\\\$a \\leftarrow b+c$} \\ar[dr] & & \\txt{$a \\leftarrow b+c$} \\ar[dl]\\\\\n";
            str += "     & \\txt{$a \\leftarrow \\mathbf{b+c}$} & & & \\txt{$a \\leftarrow \\mathbf{b+c}$} & \\\\\n";
            str += "  }\n";
            str += "\\label{eq:ExpParRed}\n";
            str += "\\end{equation}\n";
            str += "\n";
            str += "\n";

//            str += "C\\'odigo Original:\n\n" + OriginalCode + "\n\n";
//            str += "C\\'odigo Otimizado:\n\n" + OptimizedCode + "\n\n";

            str += "\\begin{table}[ht]\n";
            str += "\\centering\n";
            str += "\\begin{tabular}{l";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "|c";
            str += "|c}\n";
            str += "\t& ";
            for (bk = 0; bk < info.Length - 1; bk++)
            {
                if (bk == 0)
                    str += "ENTRY & ";
                else
                    str += "$B_{" + bk.ToString() + "}$ & ";
            }
            if (bk == info.Length - 1)
                str += "EXIT \\\\\n";
            else
                str += "$B_{" + bk.ToString() + "}$ \\\\\n";
            str += "\\hline\n";
            str += "e\\_gen & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].e_use.ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].e_use.ToBinary() + "\\}$ \\\\\n";
            str += "e\\_kill & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].e_kill.ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].e_kill.ToBinary() + "\\}$ \\\\\n";
            str += "anticipated\\_out & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].OUT[0].ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].OUT[0].ToBinary() + "\\}$ \\\\\n";
            str += "anticipated\\_in & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].IN[0].ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].IN[0].ToBinary() + "\\}$ \\\\\n";
            str += "available\\_in & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].IN[1].ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].IN[1].ToBinary() + "\\}$ \\\\\n";
            str += "available\\_out & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].OUT[1].ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].OUT[1].ToBinary() + "\\}$ \\\\\n";
            str += "earliest & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].earliest.ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].earliest.ToBinary() + "\\}$ \\\\\n";
            str += " & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += " & ";
            str += " \\\\\n";
            str += "postponable\\_in & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].IN[2].ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].IN[2].ToBinary() + "\\}$ \\\\\n";
            str += "postponable\\_out & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].OUT[2].ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].OUT[2].ToBinary() + "\\}$ \\\\\n";
            str += "latest & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].latest.ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].latest.ToBinary() + "\\}$ \\\\\n";
            str += "used\\_out & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].OUT[3].ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].OUT[3].ToBinary() + "\\}$ \\\\\n";
            str += "used\\_in & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].IN[3].ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].IN[3].ToBinary() + "\\}$ \\\\\n";
            str += " & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += " & ";
            str += " \\\\\n";
            str += "$cond\\_1$ & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].cond1.ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].IN[3].ToBinary() + "\\}$ \\\\\n";
            str += "$cond\\_2$ & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].cond2.ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].IN[3].ToBinary() + "\\}$ \\\\\n";
            str += "\\\\\n";
            str += "\\end{tabular}\n";
            str += "\\caption{" + Title + " --- $(" + domain.ToString() + ")$}\n";
            str += "\\end{table}\n\n";

            str += "\n\n";

            return str;
        }

        public static string Write(string path, Info[] info, Set domain)
        {
            string name = "PartialRedundancy1.tex";
            string filename = Path.Combine(path, name);

            System.IO.StreamWriter output = new System.IO.StreamWriter(filename);

            if (output != null)
                output.Write(PartialRedundancy.ToLaTeX(info, domain));

            output.Close();

            return name;
        }
    }

    public class LPartialRedundancy
    {
        public struct Info
        {
            public Info(Set U, Block B)
            {
                this.U = U;
                Gen = new BitSet[4][];
                Kill = new BitSet[4][];
                IN = new BitSet[4];
                OUT = new BitSet[4];
                for (int j = 0; j < 4; j++)
                {
                    Gen[j] = new BitSet[B.Size];
                    Kill[j] = new BitSet[B.Size];
                    for (int i = 0; i < B.Size; i++)
                    {
                        Gen[j][i] = new BitSet(U);
                        Kill[j][i] = new BitSet(U);
                    }
                    IN[j] = new BitSet(U);
                    OUT[j] = new BitSet(U);
                }
                last = -1;

                cond1 = null;
                cond2 = null;

                earliest = null;
                latest = null;

                e_use = null;
                e_kill = null;
            }
            public Set U;
            public int last;
            public BitSet[][] Gen;
            public BitSet[][] Kill;
            public BitSet[] IN;
            public BitSet[] OUT;
            public BitSet cond1;
            public BitSet cond2;
            public BitSet earliest;
            public BitSet latest;
            public BitSet e_use;
            public BitSet e_kill;

            public override string ToString()
            {
                string str = "";

                str += IN[3].ToBinary() + " " + OUT[3].ToBinary() + "\n";

                return str;
            }
        };

        private static int FillAnticipableExpressionsInfo(Block block, Set UExp, ref BitSet[] gen, ref BitSet[] kill)
        {
            // An expression e in UExp is anticipable at a program
            // point u if every path from u to End contains a computation of e which is not
            // preceded by an assignment to any operand of e.

            AbstractMachine.IntermediateCode code = block.Code;

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

        //public static Info[] Analysis(GraphOfBlock blocks, Set domain)
        //{
        //    Info[] info = new Info[blocks.Count];
        //    for (int i = 0; i < blocks.Count; i++)
        //        info[i] = new Info(domain, ((Block)blocks[i].Vertex));

        //    #region Informações locais aos blocos
        //    for (int i = 0; i < blocks.Count; i++)
        //    {
        //        info[i].last = FillAnticipableExpressionsInfo((Block)blocks[i].Vertex, domain, ref info[i].Gen[0], ref info[i].Kill[0]);
        //        info[i].e_use = info[i].Gen[0][0];
        //        info[i].e_kill = info[i].Kill[0][0];
        //    }
        //    #endregion

        //    #region Backward Analysis
        //    for (int i = 0; i < blocks.Count - 1; i++)
        //        info[i].IN[0].SetToOnes();
        //    info[blocks.Count - 1].IN[0].SetToZeros();

        //    bool done = false;
        //    while (!done)
        //    {
        //        done = true;
        //        for (int i = blocks.Count - 2; i >= 0; i--)
        //        {
        //            int last = info[i].last;

        //            info[i].OUT[0].SetToOnes();
        //            foreach (LNode succ in blocks[i].Successor)
        //                info[i].OUT[0] = info[i].OUT[0] * info[((Block)succ.Vertex).Id].IN[0];

        //            if (((Block)blocks[i].Vertex).Size > 0)
        //            {
        //                BitSet old = info[i].IN[0];
        //                info[i].IN[0] = info[i].e_use + (info[i].OUT[0] - info[i].e_kill);
        //                done = done && (old == info[i].IN[0]);
        //            }
        //        }
        //    }
        //    #endregion

        //    #region Available Expressions
        //    for (int i = 1; i < blocks.Count; i++)
        //        info[i].OUT[1].SetToOnes();
        //    info[0].OUT[1].SetToZeros();

        //    // Forward Analysis
        //    done = false;
        //    while (!done)
        //    {
        //        done = true;
        //        for (int i = 1; i < blocks.Count; i++)
        //        {
        //            info[i].IN[1].SetToOnes();
        //            foreach (LNode pred in blocks[i].Predecessor)
        //                info[i].IN[1] = info[i].IN[1] * info[((Block)pred.Vertex).Id].OUT[1];

        //            if (((Block)blocks[i].Vertex).Size > 0)
        //            {
        //                BitSet old = info[i].OUT[1];
        //                info[i].OUT[1] = (info[i].IN[0] + info[i].IN[1]) - info[i].e_kill;
        //                done = done && (old == info[i].OUT[1]);
        //            }
        //        }
        //    }
        //    #endregion

        //    #region Postponable Expressions
        //    for (int i = 1; i < blocks.Count; i++)
        //        info[i].OUT[2].SetToOnes();
        //    info[0].OUT[2].SetToZeros();

        //    // earliest
        //    for (int i = 0; i < blocks.Count; i++)
        //    {
        //        for (int j = 0; j < ((Block)blocks[i].Vertex).Size; j++)
        //            info[i].Gen[2][j] = info[i].Gen[0][j];
        //        info[i].earliest = info[i].IN[0] - info[i].IN[1];
        //    }

        //    // Forward Analysis
        //    done = false;
        //    while (!done)
        //    {
        //        done = true;
        //        for (int i = 1; i < blocks.Count; i++)
        //        {
        //            int last = info[i].last;

        //            info[i].IN[2].SetToOnes();
        //            foreach (LNode pred in blocks[i].Predecessor)
        //                info[i].IN[2] = info[i].IN[2] * info[((Block)pred.Vertex).Id].OUT[2];

        //            if (((Block)blocks[i].Vertex).Size > 0)
        //            {
        //                BitSet old = info[i].OUT[2];
        //                info[i].OUT[2] = (info[i].earliest + info[i].IN[2]) - info[i].e_use;
        //                done = done && (old == info[i].OUT[2]);
        //            }
        //        }
        //    }
        //    #endregion

        //    #region Used Expressions
        //    for (int i = 0; i < blocks.Count - 1; i++)
        //        info[i].IN[3].SetToZeros();
        //    info[blocks.Count - 1].IN[3].SetToZeros();

        //    // latest
        //    for (int i = 0; i < blocks.Count; i++)
        //    {
        //        BitSet tmp = new BitSet(domain);

        //        tmp.SetToOnes();
        //        foreach (LNode succ in blocks[i].Successor)
        //            tmp = tmp * (info[((Block)succ.Vertex).Id].earliest + info[((Block)succ.Vertex).Id].IN[2]);

        //        tmp = info[i].e_use + !tmp;

        //        info[i].latest = tmp * (info[i].earliest + info[i].IN[2]);
        //    }

        //    // Backward Analysis
        //    done = false;
        //    while (!done)
        //    {
        //        done = true;
        //        for (int i = blocks.Count - 2; i >= 0; i--)
        //        {
        //            int last = info[i].last;

        //            info[i].OUT[3].SetToZeros();
        //            foreach (LNode succ in blocks[i].Successor)
        //                info[i].OUT[3] = info[i].OUT[3] + info[((Block)succ.Vertex).Id].IN[3];

        //            if (((Block)blocks[i].Vertex).Size > 0)
        //            {
        //                BitSet old = info[i].IN[3];
        //                info[i].IN[3] = (info[i].e_use + info[i].OUT[3]) - info[i].latest;
        //                done = done && (old == info[i].IN[3]);
        //            }
        //        }
        //    }
        //    #endregion

        //    return info;
        //}

        //public static void Optimize(GraphOfBlock blocks, Info[] info, Set domain)
        //{
        //    for (int i = 0; i < blocks.Count; i++)
        //    {
        //        info[i].cond1 = info[i].latest * info[i].OUT[3];
        //        info[i].cond2 = info[i].e_use * (!info[i].latest + info[i].OUT[3]);
        //    }

        //    for (int i = 0; i < domain.Count; i++)
        //    {
        //        Name tmp = new Name();

        //        for (int bk = 0; bk < blocks.Count - 1; bk++)
        //        {
        //            if (info[bk].cond2[i])
        //            {
        //                for (int j = 0; j < ((Block)blocks[bk].Vertex).Size; j++)
        //                {
        //                    if (((Block)blocks[bk].Vertex)[j][0].Op == ((TAC)domain[i]).Op &&
        //                        ((Block)blocks[bk].Vertex)[j][0].Arg1 == ((TAC)domain[i]).Arg1 &&
        //                        ((Block)blocks[bk].Vertex)[j][0].Arg2 == ((TAC)domain[i]).Arg2)
        //                    {
        //                        Address trg = ((Block)blocks[bk].Vertex)[j].Target;
        //                        ((Block)blocks[bk].Vertex).Code.ReplaceInstruction(j, ((Block)blocks[bk].Vertex).Code.CreateCopy(trg, tmp));
        //                    }
        //                }
        //            }
        //        }

        //        for (int bk = 0; bk < blocks.Count - 1; bk++)
        //        {
        //            if (info[bk].cond1[i])
        //            {
        //                IntermediateInstruction inst = ((Block)blocks[bk].Vertex).Code.CreateBinary(
        //                    ((TAC)domain[i]).Op,
        //                    tmp,
        //                    ((TAC)domain[i]).Arg1,
        //                    ((TAC)domain[i]).Arg2
        //                    );
        //                ((Block)blocks[bk].Vertex).Code.InsertInstruction(0, inst);
        //            }
        //        }
        //    }
        //}

        public static string ToLaTeX(Info[] info, Set domain)
        {
            string str = "";
            int bk;

            string Title = "Elimina\\c{c}\\~ao de Redund\\^ancias Parciais";

            str += "\\section{" + Title + "}\n\n";
            str += "\n";
            str += "\\subsection{Express\\~ao Redundante}\n";
            str += "\n";
            str += "Uma express\\~ao \\'e \\emph{redundante} no ponto $p$ se em cada caminho at\\'e $p$:\n";
            str += "\\begin{enumerate}\n";
            str += "  \\item Ela \\'e avaliada antes de alcan\\c{c}ar $p$, e\n";
            str += "  \\item Nenhum de seus operandos constituintes \\'e redefinido antes de $p$.\n";
            str += "\\end{enumerate}\n";
            str += "\n";
            str += "Por exemplo, na Equa\\c{c}\\~ao~\\ref{eq:ExpRed}, as ocorr\\^encias de express\\~oes em negrito s\\~ao redundantes.\n";
            str += "\n";
            str += "\\begin{equation}\n";
            str += "\\centering\n";
            str += "  \\xymatrix {\n";
            str += "    \\txt{$a \\leftarrow b+c$\\\\$a \\leftarrow \\mathbf{b+c}$} \\ar[dr] & & \\txt{$a \\leftarrow b+c$} \\ar[dl] \\\\\n";
            str += "                   & \\txt{$a \\leftarrow \\mathbf{b+c}$} \\ar[dl] \\ar[dr] & \\\\\n";
            str += "    \\txt{$a \\leftarrow \\mathbf{b+c}$} & & \\txt{$b \\leftarrow 1$\\\\$a \\leftarrow b+c$} \n";
            str += "  }\n";
            str += "\\label{eq:ExpRed}\n";
            str += "\\end{equation}\n";
            str += "\n";
            str += "Uma express\\~ao \\'e \\emph{parcialmente redundante} no ponto $p$ se ela \\'e redundante ao longo de alguns caminhos, mas n\\~ao todos, at\\'e $p$.\n";
            str += "\n";
            str += "Por exemplo, na Equa\\c{c}\\~ao~\\ref{eq:ExpParRed}, a express\\~ao $b+c$ em negrido no diagrama da esquerda \\'e parcialmente redundante.\n";
            str += "A inser\\c{c}\\~ao de uma c\\'opia de $b+c$ depois da defini\\c{c}\\~ao de $b$ pode tornar uma express\\c{c}\\~ao parcialmente redundante em uma totalmente redundante como mostra o diagrama da direita.\n";
            str += "\n";
            str += "\\begin{equation}\n";
            str += "\\centering\n";
            str += "  \\xymatrix {\n";
            str += "    \\txt{$b \\leftarrow b+1$} \\ar[dr] & & \\txt{$a \\leftarrow b+c$} \\ar[dl] & \\txt{$b \\leftarrow b+1$\\\\$a \\leftarrow b+c$} \\ar[dr] & & \\txt{$a \\leftarrow b+c$} \\ar[dl]\\\\\n";
            str += "     & \\txt{$a \\leftarrow \\mathbf{b+c}$} & & & \\txt{$a \\leftarrow \\mathbf{b+c}$} & \\\\\n";
            str += "  }\n";
            str += "\\label{eq:ExpParRed}\n";
            str += "\\end{equation}\n";
            str += "\n";
            str += "\n";

            str += "\\begin{table}[ht]\n";
            str += "\\centering\n";
            str += "\\begin{tabular}{l";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "|c";
            str += "|c}\n";
            str += "\t& ";
            for (bk = 0; bk < info.Length - 1; bk++)
            {
                if (bk == 0)
                    str += "ENTRY & ";
                else
                    str += "$B_{" + bk.ToString() + "}$ & ";
            }
            if (bk == info.Length - 1)
                str += "EXIT \\\\\n";
            else
                str += "$B_{" + bk.ToString() + "}$ \\\\\n";
            str += "\\hline\n";
            str += "e\\_gen & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].e_use.ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].e_use.ToBinary() + "\\}$ \\\\\n";
            str += "e\\_kill & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].e_kill.ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].e_kill.ToBinary() + "\\}$ \\\\\n";
            str += "anticipated\\_out & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].OUT[0].ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].OUT[0].ToBinary() + "\\}$ \\\\\n";
            str += "anticipated\\_in & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].IN[0].ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].IN[0].ToBinary() + "\\}$ \\\\\n";
            str += "available\\_in & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].IN[1].ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].IN[1].ToBinary() + "\\}$ \\\\\n";
            str += "available\\_out & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].OUT[1].ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].OUT[1].ToBinary() + "\\}$ \\\\\n";
            str += "earliest & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].earliest.ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].earliest.ToBinary() + "\\}$ \\\\\n";
            str += " & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += " & ";
            str += " \\\\\n";
            str += "postponable\\_in & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].IN[2].ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].IN[2].ToBinary() + "\\}$ \\\\\n";
            str += "postponable\\_out & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].OUT[2].ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].OUT[2].ToBinary() + "\\}$ \\\\\n";
            str += "latest & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].latest.ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].latest.ToBinary() + "\\}$ \\\\\n";
            str += "used\\_out & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].OUT[3].ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].OUT[3].ToBinary() + "\\}$ \\\\\n";
            str += "used\\_in & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].IN[3].ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].IN[3].ToBinary() + "\\}$ \\\\\n";
            str += " & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += " & ";
            str += " \\\\\n";
            str += "$cond\\_1$ & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].cond1.ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].IN[3].ToBinary() + "\\}$ \\\\\n";
            str += "$cond\\_2$ & ";
            for (bk = 0; bk < info.Length - 1; bk++)
                str += "$\\{" + info[bk].cond2.ToBinary() + "\\}$ & ";
            str += "$\\{" + info[bk].IN[3].ToBinary() + "\\}$ \\\\\n";
            str += "\\\\\n";
            str += "\\end{tabular}\n";
            str += "\\caption{" + Title + " --- $(" + domain.ToString() + ")$}\n";
            str += "\\end{table}\n\n";

            str += "\n\n";

            return str;
        }

        public static string Write(string path, Info[] info, Set domain)
        {
            string name = "PartialRedundancy1.tex";
            string filename = Path.Combine(path, name);

            System.IO.StreamWriter output = new System.IO.StreamWriter(filename);

            if (output != null)
                output.Write(LPartialRedundancy.ToLaTeX(info, domain));

            output.Close();

            return name;
        }
    }
}
