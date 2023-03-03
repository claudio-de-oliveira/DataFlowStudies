using System;
using SetCollection;
using AbstractMachine;
using Cormen;
using System.IO;

namespace IntermediateCode
{
    public class ConstantPropagation
    {
        public class MAP
        {
            ArrayOf<Value> m;
            Set domain;

            public MAP(Set domain)
            {
                this.domain = domain;

                m = new ArrayOf<Value>();
                for (int i = 0; i < domain.Count; i++)
                    m.Add(Undef.Create());
            }

            public static MAP Meet(MAP m1, MAP m2)
            {
                MAP m = new MAP(m1.domain);

                foreach (Address addr in m1.domain)
                {
                    if (m1[addr].GetType() == typeof(Nac) || m2[addr].GetType() == typeof(Nac))
                        m[addr] = Nac.Create();
                    else if (m1[addr].GetType() == typeof(Constant) || m2[addr].GetType() == typeof(Constant))
                    {
                        if (m1[addr].GetType() == typeof(Constant) && m2[addr].GetType() == typeof(Undef))
                            m[addr] = m1[addr];
                        else if (m2[addr].GetType() == typeof(Constant) && m1[addr].GetType() == typeof(Undef))
                            m[addr] = m2[addr];
                        else if (((Constant)m1[addr]).Value == ((Constant)m2[addr]).Value)
                            m[addr] = Constant.Create(((Constant)m1[addr]).Value);
                        else
                            m[addr] = Nac.Create();
                    }
                    else
                        m[addr] = Undef.Create();
                }

                return m;
            }

            public static bool operator ==(MAP lhs, MAP rhs)
            {
                if ((object)lhs == null && (object)rhs == null)
                    return true;
                return lhs.Equals(rhs);
            }
            public static bool operator !=(MAP s1, MAP s2)
            { return !(s1 == s2); }

            public override bool Equals(object obj)
            {
                foreach (Address addr in domain)
                    if (this[addr] != ((MAP)obj)[addr])
                        return false;
                return true;
            }

            public override int GetHashCode()
            { return base.GetHashCode(); }

            public Value this[Address addr]
            {
                get
                {
                    if (addr.GetType() == typeof(Name))
                        for (int i = 0; i < domain.Count; i++)
                            if ((Address)domain[i] == addr)
                                return m[i];
                    return (Value)addr;
                }
                set
                {
                    for (int i = 0; i < domain.Count; i++)
                    {
                        if ((Address)domain[i] == addr)
                        {
                            m[i] = value;
                            break;
                        }
                    }
                }
            }

            public override string ToString()
            {
                string str = "(";
                int i;

                for (i = 0; i < domain.Count - 1; i++)
                    str += m[i].ToString() + ",";
                str += m[i].ToString() + ")";

                return str;
            }
        }

        public struct Info
        {
            public Info(Set U, Block B)
            {
                map = new MAP[B.Size + 1];
                for (int i = 0; i < B.Size + 1; i++)
                    map[i] = new MAP(U);
                last = 0;
            }
            public MAP[] map;
            public int last;
        };

        public static Info[] Analysis(ArrayOfBlock blocks, Set domain)
        {
            #region Inicializacao
            Info[] info = new Info[blocks.Count];
            for (int i = 0; i < blocks.Count; i++)
                info[i] = new Info(domain, blocks[i]);

            for (int i = 0; i < blocks.Count; i++)
            {
                foreach (Address addr in domain)
                    info[i].map[0][addr] = Undef.Create();
            }
            #endregion

            // Forward Analysis
            bool done = false;
            while (!done)
            {
                done = true;
                for (int i = 1; i < blocks.Count; i++)
                {
                    MAP old = info[i].map[0];
                    foreach (Block pred in blocks[i].Predecessor)
                        info[i].map[0] = MAP.Meet(info[i].map[0], info[pred.Id].map[info[pred.Id].last]);
                    done = done && (old == info[i].map[0]);

                    info[i].last = FillConstantPropagationInfo(blocks[i], domain, info[i].map);
                }
            }

            return info;
        }

        public static void Optimize(ArrayOfBlock blocks, Info[] info, Set domain)
        {
            for (int i = 1; i < blocks.Count - 1; i++)
                ConstantPropagationOptimalize(blocks[i], domain, info[i].map);
        }

        private static void ConstantPropagationOptimalize(Block block, Set UVar, MAP[] map)
        {
            AbstractMachine.IntermediateCode code = block.Code;

            for (int i = 0; i < code.Count; i++)
            {
                if (code[i].GetType() != typeof(Nop))
                {
                    switch (code[i][0].Op)
                    {
                        case Operator.COPY:
                            if (code[i][0].Arg2.GetType() == typeof(Name))
                                if (map[i + 1][code[i][0].Arg2].GetType() == typeof(Constant))
                                    code[i][0].Arg2 = map[i + 1][code[i][0].Arg2];
                            break;
                        case Operator.MUL:
                        case Operator.DIV:
                        case Operator.ADD:
                        case Operator.SUB:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                                if (map[i + 1][code[i][0].Arg1].GetType() == typeof(Constant))
                                    code[i][0].Arg1 = map[i + 1][code[i][0].Arg1];
                            if (code[i][0].Arg2.GetType() == typeof(Name))
                                if (map[i + 1][code[i][0].Arg2].GetType() == typeof(Constant))
                                    code[i][0].Arg2 = map[i + 1][code[i][0].Arg2];
                            break;
                        case Operator.INC:
                        case Operator.DEC:
                        case Operator.NEG:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                                if (map[i + 1][code[i][0].Arg1].GetType() == typeof(Constant))
                                    code[i][0].Arg1 = map[i + 1][code[i][0].Arg1];
                            break;
                        case Operator.GOTO:
                            break;
                        case Operator.IFTRUE:
                        case Operator.IFFALSE:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                                if (map[i + 1][code[i][0].Arg1].GetType() == typeof(Constant))
                                    code[i][0].Arg1 = map[i + 1][code[i][0].Arg1];
                            break;
                        case Operator.IFEXP:
                            if (code[i][1].Arg1.GetType() == typeof(Name))
                                if (map[i + 1][code[i][1].Arg1].GetType() == typeof(Constant))
                                    code[i][1].Arg1 = map[i + 1][code[i][1].Arg1];
                            if (code[i][1].Arg2.GetType() == typeof(Name))
                                if (map[i + 1][code[i][1].Arg2].GetType() == typeof(Constant))
                                    code[i][1].Arg2 = map[i + 1][code[i][1].Arg2];
                            break;
                        case Operator.PARAM:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                                if (map[i + 1][code[i][0].Arg1].GetType() == typeof(Constant))
                                    code[i][0].Arg1 = map[i + 1][code[i][0].Arg1];
                            break;
                        case Operator.CALL:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                                if (map[i + 1][code[i][0].Arg1].GetType() == typeof(Constant))
                                    code[i][0].Arg1 = map[i + 1][code[i][0].Arg1];
                            if (code[i][0].Arg2.GetType() == typeof(Name))
                                if (map[i + 1][code[i][0].Arg2].GetType() == typeof(Constant))
                                    code[i][0].Arg2 = map[i + 1][code[i][0].Arg2];
                            break;
                        case Operator.RETURN:
                            if (code[i][0].Arg1 != null && (code[i][0].Arg1.GetType() == typeof(Name)))
                                if (map[i + 1][code[i][0].Arg1].GetType() == typeof(Constant))
                                    code[i][0].Arg1 = map[i + 1][code[i][0].Arg1];
                            break;
                        case Operator.ADDRESS:
                            break;
                        case Operator.FROMMEMORY:
                        case Operator.TOMEMORY:
                            if (code[i][0].Arg2.GetType() == typeof(Name))
                                if (map[i + 1][code[i][0].Arg2].GetType() == typeof(Constant))
                                    code[i][0].Arg2 = map[i + 1][code[i][0].Arg2];
                            break;

                        case Operator.FROMARRAY:
                            if (code[i][0].Arg1.GetType() == typeof(Name))
                                if (map[i + 1][code[i][0].Arg1].GetType() == typeof(Constant))
                                    code[i][0].Arg1 = map[i + 1][code[i][0].Arg1];
                            if (code[i][0].Arg2.GetType() == typeof(Name))
                                if (map[i + 1][code[i][0].Arg2].GetType() == typeof(Constant))
                                    code[i][0].Arg2 = map[i + 1][code[i][0].Arg2];
                            break;
                        case Operator.TOARRAY:
                            if (code[i][1].Arg1.GetType() == typeof(Name))
                                if (map[i + 1][code[i][1].Arg1].GetType() == typeof(Constant))
                                    code[i][1].Arg1 = map[i + 1][code[i][0].Arg1];
                            break;
                    }
                }
            }
        }

        private static void Transfer(IntermediateInstruction inst, MAP inMap, ref MAP outMap)
        {
            if (inst.GetType() != typeof(Nop))
            {
                switch (inst[0].Op)
                {
                    case Operator.MUL:
                        outMap[inst.Target] = inMap[inst[0].Arg1] * inMap[inst[0].Arg2];
                        break;
                    case Operator.DIV:
                        outMap[inst.Target] = inMap[inst[0].Arg1] / inMap[inst[0].Arg2];
                        break;
                    case Operator.ADD:
                        outMap[inst.Target] = inMap[inst[0].Arg1] + inMap[inst[0].Arg2];
                        break;
                    case Operator.SUB:
                        outMap[inst.Target] = inMap[inst[0].Arg1] - inMap[inst[0].Arg2];
                        break;
                    case Operator.INC:
                        outMap[inst.Target] = ++inMap[inst[0].Arg1];
                        break;
                    case Operator.DEC:
                        outMap[inst.Target] = --inMap[inst[0].Arg1];
                        break;
                    case Operator.NEG:
                        outMap[inst.Target] = -inMap[inst[0].Arg1];
                        break;
                    case Operator.COPY:
                        outMap[inst.Target] = inMap[inst[0].Arg2];
                        break;
                }
            }
        }

        private static int FillConstantPropagationInfo(Block block, Set UVar, MAP[] map)
        {
            AbstractMachine.IntermediateCode code = block.Code;

            for (int i = 0; i < code.Count; i++)
            {
                map[i + 1] = MAP.Meet(map[i], map[i + 1]);
                Transfer(code[i], map[i], ref map[i + 1]);
            }

            return code.Count;
        }

        public static string ToLaTeX(Info[] info, Set domain)
        {
            string str = "";
            int bk;

            string Title = "Propaga\\c{c}\\~ao de Constantes";

            str += "\\section{" + Title + "}\n\n";

            str += "\\begin{itemize}\n";
            str += "  \\item[$Gen$] ...\n";
            str += "  \\item[$Kill$] ...\n";
            str += "  \\item[$In$] ...\n";
            str += "  \\item[$In$] ...\n";
            str += "\\end{itemize}\n\n";

            str += "\\begin{table}[ht]\n";
            str += "\\centering\n";
            str += "\\begin{tabular}{l|l|l}\n";
            str += "\t& IN & OUT\\\\\n";
            str += "\\hline\n";
            for (bk = 1; bk < info.Length - 1; bk++)
            {
                str += "$B_{" + bk.ToString() + "}$ & ";
                str += " $" + info[bk].map[0].ToString() + "$ &" +
                    " $" + info[bk].map[info[bk].last].ToString() + "$\\\\\n";
            }
            str += "\\end{tabular}\n";
            str += "\\caption{" + Title + " --- $(" + domain.ToString() + ")$}\n";
            str += "\\end{table}\n\n";

            return str;
        }

        public static string Write(string path, Info[] info, Set domain)
        {
            string name = "ConstantPropagation.tex";
            string filename = Path.Combine(path, name);

            System.IO.StreamWriter output = new System.IO.StreamWriter(filename);

            if (output != null)
                output.Write(ConstantPropagation.ToLaTeX(info, domain));

            output.Close();

            return name;
        }
    }
}
