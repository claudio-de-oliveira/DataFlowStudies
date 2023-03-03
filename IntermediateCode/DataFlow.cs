using System.Collections;
using SetCollection;
using IntermediateCode;
using Cormen;
using System.IO;
using System.Collections.Generic;

namespace AbstractMachine
{
    public class DataFlow
    {
        private ArrayOfBlock blocks;
        private ArrayOf<string> strCode;
        private List<string> strOriginalCode;

        public Set UDef;
        public Set UVar;
        public Set UExp;

        public void FillDeclarationInfo2(Set UDef)
        {
            foreach (IntermediateInstruction inst in UDef)
            {
                switch (inst[0].Op)
                {
                    case Operator.COPY:
                    case Operator.ADDRESS:
                    case Operator.FROMMEMORY:
                    case Operator.NEG:
                        if (inst[0].Arg1.Declaration == null)
                            inst[0].Arg1.Declaration = new BitSet(UDef);
                        inst[0].Arg1.Declaration.Add(inst);
                        break;

                    case Operator.FROMARRAY:
                        if (inst[1].Arg1.Declaration == null)
                            inst[1].Arg1.Declaration = new BitSet(UDef);
                        inst[1].Arg1.Declaration.Add(inst);
                        break;
                }
            }
        }

        public ArrayOfBlock Blocks { get { return blocks; } }

        public List<string> OriginalCode { get { return strOriginalCode; } }

        public DataFlow(IntermediateCode iCode)
        {
            int nLines = (int)(3 * iCode.Count);
            strCode = new ArrayOf<string>(nLines);

            strOriginalCode = new List<string>();

            for (int i = 0; i < nLines; i++)
                if (i < iCode.Count)
                {
                    string t = i.ToString() + " & $" + iCode[i].ToString() + "$ & ";
                    strCode.Add(t);
                    strOriginalCode.Add(t);
                }
                else
                    strCode.Add(" & & ");

            #region Construcao do grafo
            blocks = new ArrayOfBlock();

            #region Identifica o início de cada bloco

            // ENTRY
            blocks.Add(new Block(int.MinValue));

            NewBlock(0);

            for (int i = 0; i < iCode.Count; i++)
            {
                if (iCode[i][0].Op == Operator.IFEXP || iCode[i][0].Op == Operator.GOTO ||
                    iCode[i][0].Op == Operator.IFTRUE || iCode[i][0].Op == Operator.IFFALSE ||
                    iCode[i][0].Op == Operator.CALL)
                {
                    NewBlock(((Label)iCode[i][0].Arg2).Value);
                    NewBlock(i + 1);
                }
                else if (iCode[i][0].Op == Operator.RETURN)
                {
                    NewBlock(i + 1);
                }
            }
            if (!(iCode[iCode.Count - 1][0].Op == Operator.IFEXP || iCode[iCode.Count - 1][0].Op == Operator.GOTO ||
                  iCode[iCode.Count - 1][0].Op == Operator.IFTRUE || iCode[iCode.Count - 1][0].Op == Operator.IFFALSE ||
                  iCode[iCode.Count - 1][0].Op == Operator.CALL || iCode[iCode.Count - 1][0].Op == Operator.RETURN))
            {
                NewBlock(iCode.Count);
            }

            #endregion

            #region Copia as instruções para os blocos

            _ = blocks[1].Predecessor.Add(blocks[0]);
            _ = blocks[0].Sucessor.Add(blocks[1]);

            blocks[0].Add(new Nop());

            for (int i = 1; i < blocks.Count - 1; i++)
            {
                int j, trg;

                for (j = blocks[i].Leader; j < blocks[i + 1].Leader - 1; j++)
                    blocks[i].Add(iCode[j]);

                blocks[i].Add(iCode[j]);

                switch (blocks[i].Last[0].Op)
                {
                    case Operator.IFEXP:
                    case Operator.IFTRUE:
                    case Operator.IFFALSE:
                        trg = FindBlock(((Label)blocks[i].Last[0].Arg2).Value);
                        _ = blocks[trg].Predecessor.Add(blocks[i]);
                        _ = blocks[i].Sucessor.Add(blocks[trg]);
                        trg = FindBlock(blocks[i + 1].Leader);
                        _ = blocks[trg].Predecessor.Add(blocks[i]);
                        _ = blocks[i].Sucessor.Add(blocks[trg]);
                        break;
                    case Operator.CALL:
                    case Operator.GOTO:
                        trg = FindBlock(((Label)blocks[i].Last[0].Arg2).Value);
                        _ = blocks[trg].Predecessor.Add(blocks[i]);
                        _ = blocks[i].Sucessor.Add(blocks[trg]);
                        break;
                    default:
                        trg = FindBlock(blocks[i + 1].Leader);
                        _ = blocks[trg].Predecessor.Add(blocks[i]);
                        _ = blocks[i].Sucessor.Add(blocks[trg]);
                        break;
                }
            }

            blocks[blocks.Count - 1].Add(new Nop());

            #region Substitui os labels de instruções por labels de blocos
            for (int i = 1; i < blocks.Count - 1; i++)
            {
                Block current = blocks[i];

                IntermediateInstruction last = current.Last;

                if (last.GetType() != typeof(Nop))
                {
                    switch (last[0].Op)
                    {
                        case Operator.CALL:
                        case Operator.GOTO:
                        case Operator.IFEXP:
                        case Operator.IFTRUE:
                        case Operator.IFFALSE:
                            for (int k = 0; k < blocks.Count; k++)
                            {
                                if (((Label)(last[0].Arg2)).Value == blocks[k].Leader)
                                {
                                    last[0].Arg2 = new Label(blocks[k]);
                                    break;
                                }
                            }
                            break;
                        default:
                            break;
                    }
                }
            }
            #endregion

            for (int i = 0; i < blocks.Count; i++)
                blocks[i].Id = i;
            #endregion

            int m = 0;
            for (int h = 0; h < blocks.Count - 1; h++)
                for (int i = 0; i < blocks[h].Code.Count; i++)
                    if (i == 0)
                        strCode[m++] += "@" + h.ToString() + ": & $" + blocks[h][i].ToString() + "$ & ";
                    else
                        strCode[m++] += " & $" + blocks[h][i].ToString() + "$ & ";
            for (int h = m + 1; h < nLines; h++)
                strCode[m++] += " & & ";

            //////////////////////////////
            // Insere um bloco vazio nas arestas entrando em um bloco com mais do que um predecessor
            blocks.Split1();
            //////////////////////////////

            BitArray impress = new BitArray(blocks.Count);
            impress.SetAll(false);
            m = 0;
            {
                for (int h = 0; h < blocks.Count - 1; h++)
                {
                    for (int g = h + 1; g < blocks.Count - 1; g++)
                        if (!impress[g] && blocks[h].Leader == blocks[g].Leader)
                        {
                            strCode[m++] += "@" + g.ToString() + ": & & ";
                            impress[g] = true;
                        }

                    if (!impress[h])
                    {
                        for (int i = 0; i < blocks[h].Code.Count; i++)
                            if (i == 0)
                                strCode[m++] += "@" + h.ToString() + ": & $" + blocks[h][i].ToString() + "$ & ";
                            else
                                strCode[m++] += " & $" + blocks[h][i].ToString() + "$ & ";

                        impress[h] = true;
                    }
                }
                for (int h = m; h < nLines; h++)
                    strCode[m++] += " & & ";
            }

            #endregion

            UVar = Address.Symbols;
            UDef = new Set();
            UExp = new Set();

            for (int i = 0; i < blocks.Count - 1; i++)
                FillDeclarationInfo(blocks[i], ref UDef, ref UExp);
            FillDeclarationInfo2(UDef);
        }

        public ArrayOf<string> Optimize(string path)
        {
            ArrayOf<string> fileList = new ArrayOf<string>();

            // Reachable Definition
            ReachableDefinition RD = new ReachableDefinition();
            ArrayOf<Info> rdInfo = RD.Analysis(blocks, UDef);
            fileList.Add(ReachableDefinition.Write(path, rdInfo, UDef));
            ////

            // Live Variable
            LiveVariable LV = new LiveVariable();
            ArrayOf<Info> lvInfo = LV.Analysis(blocks, UVar);
            fileList.Add(LiveVariable.Write(path, lvInfo, UVar));
            ////
            
            // Available Expressions
            AvailableExpressions AvailExp = new AvailableExpressions();
            ArrayOf<Info> availInfo = AvailExp.Analysis(blocks, UExp);
            fileList.Add(AvailableExpressions.Write(path, availInfo, UExp));
            ////
            
            // Anticipable Expressions
            AnticipableExpressions AnticExp = new AnticipableExpressions();
            ArrayOf<Info> anticInfo = AnticExp.Analysis(blocks, UExp);
            fileList.Add(AnticipableExpressions.Write(path, anticInfo, UExp));
            ////
            
            // Partially Available Expressions
            PartiallyAvailableExpressions PAE = new PartiallyAvailableExpressions();
            ArrayOf<Info> paeInfo = PAE.Analysis(blocks, UExp);
            fileList.Add(PartiallyAvailableExpressions.Write(path, paeInfo, UExp));
            ////
            
            // Dead Variable
            DeadVariable DV = new DeadVariable();
            ArrayOf<Info> dvInfo = DV.Analysis(blocks, UVar);
            fileList.Add(DeadVariable.Write(path, dvInfo, UVar));
            ////
            
            // Definitions For Copy Propagation
            DefinitionsForCopyPropagation DefCP = new DefinitionsForCopyPropagation();
            ArrayOf<Info> dcpInfo = DefCP.Analysis(blocks, UDef);
            fileList.Add(DefinitionsForCopyPropagation.Write(path, dcpInfo, UDef));
            ////

            // Partial Redundancy Elimination
            //////////////////////////////
            // Garante que toda expressão aperece no início de um bloco
            blocks.Split();
            //////////////////////////////

            PartialRedundancy.Info[] preInfo = PartialRedundancy.Analysis(blocks, UExp);
            PartialRedundancy.Optimize(blocks, preInfo, UExp);
            fileList.Add(PartialRedundancy.Write(path, preInfo, UExp));
            ////

            int nLines = strCode.Count;

            BitArray impress = new BitArray(blocks.Count);
            int m = 0;
            {
                for (int h = 0; h < blocks.Count - 1; h++)
                {
                    for (int g = h + 1; g < blocks.Count - 1; g++)
                        if (!impress[g] && blocks[h].Leader == blocks[g].Leader)
                        {
                            strCode[m++] += "@" + g.ToString() + ": & & ";
                            impress[g] = true;
                        }

                    if (!impress[h])
                    {
                        for (int i = 0; i < blocks[h].Code.Count; i++)
                            if (i == 0)
                                strCode[m++] += "@" + h.ToString() + ": & $" + blocks[h][i].ToString() + "$ & ";
                            else
                                strCode[m++] += " & $" + blocks[h][i].ToString() + "$ & ";

                        impress[h] = true;
                    }
                }
                for (int h = m; h < nLines; h++)
                    strCode[m++] += " & & ";
            }

            // Constant Propagation
            ConstantPropagation.Info[] cpInfo = ConstantPropagation.Analysis(blocks, UVar);
            ConstantPropagation.Optimize(blocks, cpInfo, UVar);
            fileList.Add(ConstantPropagation.Write(path, cpInfo, UVar));
            ////

            {
                for (int o = 0; o < blocks.Count - 1; o++)
                {
                    for (int p = o + 1; p < blocks.Count; p++)
                    {
                        if (blocks[o].Leader > blocks[p].Leader)
                        {
                            Block block = blocks[o];
                            blocks[o] = blocks[p];
                            blocks[p] = block;
                        }
                    }
                }
                for (int o = 0; o < blocks.Count; o++)
                    blocks[o].Id = o;
            }

            impress = new BitArray(blocks.Count);
            m = 0;
            {
                for (int h = 0; h < blocks.Count - 1; h++)
                {
                    for (int g = h + 1; g < blocks.Count - 1; g++)
                        if (!impress[g] && blocks[h].Leader == blocks[g].Leader)
                        {
                            strCode[m++] += "@" + g.ToString() + ": & & ";
                            impress[g] = true;
                        }

                    if (!impress[h])
                    {
                        for (int i = 0; i < blocks[h].Code.Count; i++)
                            if (i == 0)
                                strCode[m++] += "@" + h.ToString() + ": & $" + blocks[h][i].ToString() + "$ & ";
                            else
                                strCode[m++] += " & $" + blocks[h][i].ToString() + "$ & ";

                        impress[h] = true;
                    }
                }
                for (int h = m; h < nLines; h++)
                    strCode[m++] += " & & ";
            }

            string strTable = "";
            strTable += "\\begin{table}\n";
            strTable += "\\begin{scriptsize}\n";
            strTable += "\\begin{tabular}{ll|ll|ll|ll|ll|ll}\n";
            for (int i = 0; i < strCode.Count; i++)
                strTable += strCode[i] += "\\\\\n";
            strTable += "\\end{tabular}\n";
            strTable += "\\end{scriptsize}\n";
            strTable += "\\end{table}\n";

            fileList.Add(Write(path, "Resumo.tex", strTable));

            return fileList;
        }

        public static string Write(string path, string name, string text)
        {
            string filename = Path.Combine(path, name);

            System.IO.StreamWriter output = new System.IO.StreamWriter(filename);

            if (output != null)
                output.Write(text);

            output.Close();

            return name;
        }


        public void FillDeclarationInfo(Block block, ref Set UDef, ref Set UExp)
        {
            AbstractMachine.IntermediateCode code = block.Code;

            for (int i = 0; i < code.Count; i++)
            {
                if (code[i].GetType() != typeof(Nop))
                {
                    switch (code[i][0].Op)
                    {
                        case Operator.MUL:
                        case Operator.DIV:
                        case Operator.ADD:
                        case Operator.SUB:
                        case Operator.DEC:
                        case Operator.INC:
                            UExp.Add(code[i][0]);
                            UDef.Add(code[i]);
                            break;

                        case Operator.IFEXP:
                            UExp.Add(code[i][1]);
                            break;

                        case Operator.COPY:
                        case Operator.ADDRESS:
                        case Operator.FROMMEMORY:
                        case Operator.NEG:
                            UDef.Add(code[i]);
                            break;

                        case Operator.FROMARRAY:
                            UDef.Add(code[i]);
                            break;
                    }
                }
            }
        }

        public int FindBlock(int leader)
        {
            for (int i = 1; i < blocks.Count; i++)
                if (leader == blocks[i].Leader)
                    return i;
            return -1;
        }

        private void NewBlock(int val)
        {
            for (int i = 1; i < blocks.Count; i++)
                if (blocks[i].Leader == val)
                    return;

            Block block = new Block(val);

            int pos = blocks.Add(block);

            // Mantem os blocos classificados 
            for (int i = pos - 1; i >= 0; i--)
            {
                if (blocks[i].Leader > val)
                {
                    Block tmp = blocks[i];
                    blocks[i] = blocks[i + 1];
                    blocks[i + 1] = tmp;
                }
                else
                    break;
            }
        }

        private Block ENTRY { get { return (Block)blocks[0]; } }

        private Block EXIT { get { return (Block)blocks[blocks.Count - 1]; } }

        #region Rotinas para impressão
        public string CodeToString()
        {
            int max = int.MinValue;
            string str = "";
            int bk, c;

            for (bk = 1; bk < blocks.Count - 1; bk++)
                if (max < blocks[bk].Size)
                    max = blocks[bk].Size;

            string[] code = new string[max];

            for (c = 0; c < max; c++)
                code[c] = "";

            str += "\\begin{table}[ht]\n";
            str += "\\begin{scriptsize}\n";
            str += "\\begin{tabular}{";
            for (bk = 1; bk < blocks.Count - 2; bk++)
                str += "l|";
            str += "l}\n";
            for (bk = 1; bk < blocks.Count - 2; bk++)
            {
                if (bk == 0)
                    str += "ENTRY & ";
                else
                    str += "$B_{" + bk.ToString() + "}$ & ";
            }
            if (bk == blocks.Count - 1)
                str += "EXIT \\\\\n";
            else
                str += "$B_{" + bk.ToString() + "}$ \\\\\n";
            str += "\\hline\n";

            for (bk = 1; bk < blocks.Count - 2; bk++)
                str += "$" + blocks[bk].Predecessor.ToString() + "$ & ";
            str += "$" + blocks[bk].Predecessor.ToString() + "$ \\\\\n";

            for (bk = 1; bk < blocks.Count - 2; bk++)
                str += "$" + blocks[bk].Sucessor.ToString() + "$ & ";
            str += "$" + blocks[bk].Sucessor.ToString() + "$ \\\\\n";
            str += "\\hline\\\n";

            for (c = 0; c < max; c++)
            {
                for (bk = 1; bk < blocks.Count - 2; bk++)
                    if (c < blocks[bk].Size)
                        code[c] += "$" + blocks[bk][c].ToString() + "$ & ";
                    else
                        code[c] += " & ";
                if (c < blocks[bk].Size)
                    code[c] += "$" + blocks[bk][c].ToString() + "$ \\\\\n";
                else
                    code[c] += " \\\\\n";
                str += code[c];
            }

            str += "\\end{tabular}\n";
            str += "\\end{scriptsize}\n";
            str += "\\end{table}\n\n";

            return str;
        }

        public void Write(string path, string fname, ArrayOf<string> inputs)
        {
            string filename = Path.Combine(path, fname);

            System.IO.StreamWriter output = new System.IO.StreamWriter(filename);

            if (output != null)
            {
                string str =
                    "\\documentclass[landscape]{article}\n" +
                    "\\usepackage{graphicx}\n" +
                    "\n" +
                    "%\\usepackage[brazil]{babel}\n" +
                    "\\usepackage[latin1]{inputenc}\n" +
                    "\\usepackage[T1]{fontenc}\n" +
                    "\\usepackage[all]{xy}\n" +
                    "\n" +
                    "\\usepackage {vmargin}           % para setar formato da página + facilmente\n" +
                    "\\usepackage {color}\n" +
                    "\n" +
                    "% Dimensões a ocupar na página (package Vmargin)\n" +
                    "\\setpapersize [landscape]{A4}\n" +
                    "\\setmarginsrb {25mm} % margem esquerda\n" +
                    "              {25mm} % margem topo\n" +
                    "              {20mm} % margem direita\n" +
                    "              {20mm} % margem pé\n" +
                    "              {2ex}  % altura do espaço para cabeçalho\n" +
                    "              {2ex}  % espaço entre fim do cabeçalho e início do texto\n" +
                    "              {2ex}  % altura do espaço para rodapé\n" +
                    "              {2ex}  % espaço entre fim do texto e fim do rodapé\n" +
                    "\n" +
                    "\\begin{document}\n" +
                    "\n";

                foreach (string inp in inputs)
                {
                    str += "\\input " + inp + "\n";
                    str += "\\clearpage\n\n";
                }

                {
                    Queue Q = new Queue(blocks.Count);

                    blocks.DFS(Q);

                    var tmp = blocks.ToCode(Q);

                    str += blocks.ToLaTeX();
                }

                str += "\\end{document}\n\n";

                output.Write(str);

                output.Close();
            }
        }
        #endregion
    }
}
