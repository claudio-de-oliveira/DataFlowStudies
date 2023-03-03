using System;
using System.Collections;
using System.Linq;
using System.Text;
using SetCollection;
using IntermediateCode;
using CustomException;

namespace AbstractMachine
{
    public enum Meet
    { 
        UNION, INTERSECTION 
    };

    public struct Info
    {
        public Info(Set U)
        {
            Gen = new BitSet(U);
            Kill = new BitSet(U);
            IN = new BitSet(U);
            OUT = new BitSet(U);
        }
        public BitSet Gen;
        public BitSet Kill;
        public BitSet IN;
        public BitSet OUT;
    };

    abstract class Optimization
    {
        protected Set domain;
        protected ArrayList blocks;
        protected ArrayList Gen;
        protected ArrayList Kill;
        protected ArrayList IN;
        protected ArrayList OUT;

        protected string Title;
        protected Meet meet;

        public Optimization(ArrayList blocks, Set domain, Meet meet, string title)
        {
            int i;

            Gen = new ArrayList();
            Kill = new ArrayList();
            IN = new ArrayList();
            OUT = new ArrayList();

            for (i = 0; i < blocks.Count; i++)
            {
                Gen.Add(new BitSet(domain));
                Kill.Add(new BitSet(domain));
                IN.Add(new BitSet(domain));
                OUT.Add(new BitSet(domain));
            }

            this.meet = meet;

            this.blocks = blocks;
            this.domain = domain;

            Title = title;
        }

        public abstract void Analysis();
        public abstract void Initialize();
        public abstract void TransferFunction();

        public abstract void Analysis(ref Info[] info);
        public abstract void Initialize(ref Info[] info);
        public abstract void TransferFunction(ref Info[] info);

        public BitSet GetGen(int block)
        {
            if (block < 0 || block >= blocks.Count)
                throw new CustomException.TesteException("Index out of range");
            return (BitSet)Gen[block];
        }
        public BitSet GetKill(int block)
        {
            if (block < 0 || block >= blocks.Count)
                throw new CustomException.TesteException("Index out of range");
            return (BitSet)Kill[block];
        }
        public BitSet GetIN(int block)
        {
            if (block < 0 || block >= blocks.Count)
                throw new CustomException.TesteException("Index out of range");
            return (BitSet)IN[block];
        }
        public BitSet GetOUT(int block)
        {
            if (block < 0 || block >= blocks.Count)
                throw new CustomException.TesteException("Index out of range");
            return (BitSet)OUT[block];
        }

        protected void ForwardAnalysis(ref Info[] info)
        {
            TransferFunction(ref info);

            Initialize(ref info);

            // Forward Analysis
            bool done = false;
            while (!done)
            {
                done = true;
                for (int i = 1; i < blocks.Count; i++)
                {
                    if (meet == Meet.UNION)
                    {
                        info[i].IN.SetToZeros();
                        foreach (Block pred in ((Block)blocks[i]).Predecessor)
                            info[i].IN = (BitSet)info[i].IN + (BitSet)info[pred.Id].OUT;
                    }
                    else if (meet == Meet.INTERSECTION)
                    {
                        ((BitSet)info[i].IN).SetToOnes();
                        foreach (Block pred in ((Block)blocks[i]).Predecessor)
                            info[i].IN = (BitSet)info[i].IN * (BitSet)info[pred.Id].OUT;
                    }

                    BitSet old = (BitSet)info[i].OUT;
                    info[i].OUT = (BitSet)info[i].Gen + ((BitSet)info[i].IN - (BitSet)info[i].Kill);
                    done = done && (old == (BitSet)info[i].OUT);
                }
            }
        }

        protected void ForwardAnalysis()
        {
            TransferFunction();

            Initialize();

            // Forward Analysis
            bool done = false;
            while (!done)
            {
                done = true;
                for (int i = 1; i < blocks.Count; i++)
                {
                    if (meet == Meet.UNION)
                    {
                        ((BitSet)IN[i]).SetToZeros();
                        foreach (Block pred in ((Block)blocks[i]).Predecessor)
                            IN[i] = (BitSet)IN[i] + (BitSet)OUT[pred.Id];
                    }
                    else if (meet == Meet.INTERSECTION)
                    {
                        ((BitSet)IN[i]).SetToOnes();
                        foreach (Block pred in ((Block)blocks[i]).Predecessor)
                            IN[i] = (BitSet)IN[i] * (BitSet)OUT[pred.Id];
                    }

                    BitSet old = (BitSet)OUT[i];
                    OUT[i] = (BitSet)Gen[i] + ((BitSet)IN[i] - (BitSet)Kill[i]);
                    done = done && (old == (BitSet)OUT[i]);
                }
            }
        }

        protected void BackwardAnalysis(ref Info[] info)
        {
            TransferFunction(ref info);

            Initialize(ref info);

            // Backward Analysis
            bool done = false;
            while (!done)
            {
                done = true;
                for (int i = blocks.Count - 2; i >= 0; i--)
                {
                    if (meet == Meet.UNION)
                    {
                        ((BitSet)info[i].OUT).SetToZeros();
                        foreach (Block succ in ((Block)blocks[i]).Sucessor)
                            info[i].OUT = (BitSet)info[i].OUT + (BitSet)info[succ.Id].IN;
                    }
                    else if (meet == Meet.INTERSECTION)
                    {
                        ((BitSet)info[i].OUT).SetToOnes();
                        foreach (Block succ in ((Block)blocks[i]).Sucessor)
                            info[i].OUT = (BitSet)info[i].OUT * (BitSet)info[succ.Id].IN;
                    }

                    BitSet old = (BitSet)info[i].IN;
                    info[i].IN = (BitSet)info[i].Gen + ((BitSet)info[i].OUT - (BitSet)info[i].Kill);
                    done = done && (old == (BitSet)info[i].IN);
                }
            }
        }

        protected void BackwardAnalysis()
        {
            TransferFunction();

            Initialize();

            // Backward Analysis
            bool done = false;
            while (!done)
            {
                done = true;
                for (int i = blocks.Count - 2; i >= 0; i--)
                {
                    if (meet == Meet.UNION)
                    {
                        ((BitSet)OUT[i]).SetToZeros();
                        foreach (Block succ in ((Block)blocks[i]).Sucessor)
                            OUT[i] = (BitSet)OUT[i] + (BitSet)IN[succ.Id];
                    }
                    else if (meet == Meet.INTERSECTION)
                    {
                        ((BitSet)OUT[i]).SetToOnes();
                        foreach (Block succ in ((Block)blocks[i]).Sucessor)
                            OUT[i] = (BitSet)OUT[i] * (BitSet)IN[succ.Id];
                    }

                    BitSet old = (BitSet)IN[i];
                    IN[i] = (BitSet)Gen[i] + ((BitSet)OUT[i] - (BitSet)Kill[i]);
                    done = done && (old == (BitSet)IN[i]);
                }
            }
        }

        public override string ToString()
        {
            string str = Title + "\n";

            int i;

            for (i = 0; i < Title.Length; i++)
                str += "=";
            str += "\n";
            str += "Dominio: " + domain.ToString() + "\n\n";

            if (Gen.Count > 0)
            {
                str += "      ";
                str += "Gen";
                for (i = 3; i < ((BitSet)Gen[0]).Universe.Count; i++)
                    str += " ";
                str += " ";
                str += "Kill";
                for (i = 4; i < ((BitSet)Gen[0]).Universe.Count; i++)
                    str += " ";
                str += "\t";
                str += "OUT";
                for (i = 3; i < ((BitSet)Gen[0]).Universe.Count; i++)
                    str += " ";
                str += " IN\n";
                for (int bk = 1; bk < blocks.Count - 1; bk++)
                {
                    string tmp = String.Format("B{0:000}  ", bk);
                    str += tmp + ((BitSet)Gen[bk]).ToBinary();
                    str += " ";
                    str += ((BitSet)Kill[bk]).ToBinary();
                    str += "\t";
                    str += ((BitSet)OUT[bk]).ToBinary();
                    str += " ";
                    str += ((BitSet)IN[bk]).ToBinary();
                    str += "\n";
                }
            }

            return str;
        }
    }

    public class DataFlow
    {
        private ArrayList blocks;

        class ReachableDefinition : Optimization
        {
            public ReachableDefinition(DataFlow df, string title)
                : base(df.blocks, df.UDef, Meet.UNION, title)
            {
            }

            public override void Analysis(ref Info[] info)
            {
                ForwardAnalysis(ref info);
            }

            public override void Analysis()
            {
                ForwardAnalysis();
            }

            public override void Initialize(ref Info[] info)
            {
                // Já inicializado pelos construtores
            }

            public override void Initialize()
            {
                // Já inicializado pelos construtores
            }

            public override void TransferFunction(ref Info[] info)
            {
                for (int i = 0; i < blocks.Count; i++)
                {
                    BitSet kill = new BitSet(domain);
                    BitSet gen = new BitSet(domain);
                    ((Block)blocks[i]).FillReachableDefinitionsInfo(domain, ref gen, ref kill);
                    info[i].Kill = kill;
                    info[i].Gen = gen;
                }
            }

            public override void TransferFunction()
            {
                for (int i = 0; i < blocks.Count; i++)
                {
                    BitSet kill = new BitSet(domain);
                    BitSet gen = new BitSet(domain);
                    ((Block)blocks[i]).FillReachableDefinitionsInfo(domain, ref gen, ref kill);
                    Kill[i] = kill;
                    Gen[i] = gen;
                }
            }
        }

        class DefinitionsForCopyPropagation : Optimization
        {
            public DefinitionsForCopyPropagation(DataFlow df, string title)
                : base(df.blocks, df.UDef, Meet.INTERSECTION, title)
            {
            }

            public override void Analysis(ref Info[] info)
            {
                ForwardAnalysis(ref info);
            }

            public override void Analysis()
            {
                ForwardAnalysis();
            }

            public override void Initialize(ref Info[] info)
            {
                // Já inicializado pelos construtores
            }

            public override void Initialize()
            {
                // Já inicializado pelos construtores
            }

            public override void TransferFunction(ref Info[] info)
            {
                for (int i = 0; i < blocks.Count; i++)
                {
                    BitSet kill = new BitSet(domain);
                    BitSet gen = new BitSet(domain);
                    ((Block)blocks[i]).FillDefinitionsForCopyPropagationInfo(domain, ref gen, ref kill);
                    info[i].Kill = kill;
                    info[i].Gen = gen;
                }
            }
            public override void TransferFunction()
            {
                for (int i = 0; i < blocks.Count; i++)
                {
                    BitSet kill = new BitSet(domain);
                    BitSet gen = new BitSet(domain);
                    ((Block)blocks[i]).FillDefinitionsForCopyPropagationInfo(domain, ref gen, ref kill);
                    Kill[i] = kill;
                    Gen[i] = gen;
                }
            }
        }

        class LiveVariable : Optimization
        {
            public LiveVariable(DataFlow df, string title)
                : base(df.blocks, df.UVar, Meet.UNION, title)
            {
                // Nothing more todo
            }

            public override void Analysis(ref Info[] info)
            {
                BackwardAnalysis(ref info);
            }

            public override void Analysis()
            {
                BackwardAnalysis();
            }

            public override void Initialize(ref Info[] info)
            {
                // Já inicializado pelos construtores
            }

            public override void Initialize()
            {
                // Já inicializado pelos construtores
            }

            public override void TransferFunction(ref Info[] info)
            {
                for (int i = 0; i < blocks.Count; i++)
                {
                    BitSet kill = new BitSet(domain);
                    BitSet gen = new BitSet(domain);
                    ((Block)blocks[i]).FillLiveVariablesInfo(domain, ref gen, ref kill);
                    info[i].Kill = kill;
                    info[i].Gen = gen;
                }
            }
            public override void TransferFunction()
            {
                for (int i = 0; i < blocks.Count; i++)
                {
                    BitSet kill = new BitSet(domain);
                    BitSet gen = new BitSet(domain);
                    ((Block)blocks[i]).FillLiveVariablesInfo(domain, ref gen, ref kill);
                    Kill[i] = kill;
                    Gen[i] = gen;
                }
            }
        }

        class DeadVariable : Optimization
        {
            public DeadVariable(DataFlow df, string title)
                : base(df.blocks, df.UVar, Meet.INTERSECTION, title)
            {
                // Nothing more todo
            }

            public override void Analysis(ref Info[] info)
            {
                BackwardAnalysis(ref info);
            }

            public override void Analysis()
            {
                BackwardAnalysis();
            }

            public override void Initialize(ref Info[] info)
            {
                for (int i = 1; i < blocks.Count; i++)
                    ((BitSet)info[i].IN).SetToOnes();
            }

            public override void Initialize()
            {
                for (int i = 1; i < blocks.Count; i++)
                    ((BitSet)IN[i]).SetToOnes();
            }

            public override void TransferFunction(ref Info[] info)
            {
                for (int i = 0; i < blocks.Count; i++)
                {
                    BitSet kill = new BitSet(domain);
                    BitSet gen = new BitSet(domain);
                    ((Block)blocks[i]).FillDeadVariablesInfo(domain, ref gen, ref kill);
                    info[i].Kill = kill;
                    info[i].Gen = gen;
                }
            }
            public override void TransferFunction()
            {
                for (int i = 0; i < blocks.Count; i++)
                {
                    BitSet kill = new BitSet(domain);
                    BitSet gen = new BitSet(domain);
                    ((Block)blocks[i]).FillDeadVariablesInfo(domain, ref gen, ref kill);
                    Kill[i] = kill;
                    Gen[i] = gen;
                }
            }
        }

        class AvailableExpressions : Optimization
        {
            protected ArrayList Redundant;

            public AvailableExpressions(DataFlow df, string title)
                : base(df.blocks, df.UExp, Meet.INTERSECTION, title)
            {
                Redundant = new ArrayList();

                for (int i = 0; i < blocks.Count; i++)
                    Redundant.Add(new BitSet(domain));
            }

            public BitSet GetRedundant(int block)
            {
                if (block < 0 || block >= blocks.Count)
                    throw new CustomException.TesteException("Index out of range");
                return (BitSet)Redundant[block];
            }

            public override void Analysis(ref Info[] info)
            {
                ForwardAnalysis(ref info);

                for (int B = 0; B < blocks.Count; B++)
                    Redundant[B] = (BitSet)Gen[B] * (BitSet)IN[B];
            }

            public override void Initialize(ref Info[] info)
            {
                ((BitSet)info[0].OUT).SetToZeros();
                for (int i = 1; i < blocks.Count; i++)
                    ((BitSet)info[i].OUT).SetToOnes();
            }

            public override void Analysis()
            {
                ForwardAnalysis();

                for (int B = 0; B < blocks.Count; B++)
                    Redundant[B] = (BitSet)Gen[B] * (BitSet)IN[B];
            }

            public override void Initialize()
            {
                ((BitSet)OUT[0]).SetToZeros();
                for (int i = 1; i < blocks.Count; i++)
                    ((BitSet)OUT[i]).SetToOnes();
            }

            public override void TransferFunction(ref Info[] info)
            {
                for (int i = 0; i < blocks.Count; i++)
                {
                    BitSet kill = new BitSet(domain);
                    BitSet gen = new BitSet(domain);
                    ((Block)blocks[i]).FillAvailableExpressionsInfo(domain, ref gen, ref kill);
                    info[i].Kill = kill;
                    info[i].Gen = gen;
                }
            }
            public override void TransferFunction()
            {
                for (int i = 0; i < blocks.Count; i++)
                {
                    BitSet kill = new BitSet(domain);
                    BitSet gen = new BitSet(domain);
                    ((Block)blocks[i]).FillAvailableExpressionsInfo(domain, ref gen, ref kill);
                    Kill[i] = kill;
                    Gen[i] = gen;
                }
            }
        }

        class PartiallyAvailableExpressions : Optimization
        {
            protected ArrayList ParRedund;

            public PartiallyAvailableExpressions(DataFlow df, string title)
                : base(df.blocks, df.UExp, Meet.UNION, title)
            {
                // Nothing more todo

                ParRedund = new ArrayList();

                for (int i = 0; i < blocks.Count; i++)
                    ParRedund.Add(new BitSet(domain));
            }

            public BitSet GetParRedund(int block)
            {
                if (block < 0 || block >= blocks.Count)
                    throw new CustomException.TesteException("Index out of range");
                return (BitSet)ParRedund[block];
            }

            public override void Analysis(ref Info[] info)
            {
                ForwardAnalysis(ref info);

                for (int B = 0; B < blocks.Count; B++)
                    ParRedund[B] = (BitSet)info[B].Gen * (BitSet)info[B].IN;
            }

            public override void Initialize(ref Info[] info)
            {
                //                for (int i = 1; i < blocks.Count; i++)
                //                    ((BitSet)OUT[i]).SetToOnes();
            }

            public override void Analysis()
            {
                ForwardAnalysis();

                for (int B = 0; B < blocks.Count; B++)
                    ParRedund[B] = (BitSet)Gen[B] * (BitSet)IN[B];
            }

            public override void Initialize()
            {
//                for (int i = 1; i < blocks.Count; i++)
//                    ((BitSet)OUT[i]).SetToOnes();
            }

            public override void TransferFunction(ref Info[] info)
            {
                for (int i = 0; i < blocks.Count; i++)
                {
                    BitSet kill = new BitSet(domain);
                    BitSet gen = new BitSet(domain);
                    ((Block)blocks[i]).FillAvailableExpressionsInfo(domain, ref gen, ref kill);
                    info[i].Kill = kill;
                    info[i].Gen = gen;
                }
            }
            public override void TransferFunction()
            {
                for (int i = 0; i < blocks.Count; i++)
                {
                    BitSet kill = new BitSet(domain);
                    BitSet gen = new BitSet(domain);
                    ((Block)blocks[i]).FillAvailableExpressionsInfo(domain, ref gen, ref kill);
                    Kill[i] = kill;
                    Gen[i] = gen;
                }
            }
        }

        class AnticipableExpressions : Optimization
        {
            public AnticipableExpressions(DataFlow df, string title)
                : base(df.blocks, df.UExp, Meet.INTERSECTION, title)
            {
                // Nothing more todo
            }

            public override void Analysis(ref Info[] info)
            {
                BackwardAnalysis(ref info);
            }

            public override void Initialize(ref Info[] info)
            {
                for (int i = 0; i < blocks.Count - 1; i++)
                    ((BitSet)info[i].IN).SetToOnes();
                ((BitSet)info[blocks.Count - 1].IN).SetToZeros();
            }

            public override void Analysis()
            {
                BackwardAnalysis();
            }

            public override void Initialize()
            {
                for (int i = 0; i < blocks.Count - 1; i++)
                    ((BitSet)IN[i]).SetToOnes();
                ((BitSet)IN[blocks.Count - 1]).SetToZeros();
            }

            public override void TransferFunction(ref Info[] info)
            {
                for (int i = 0; i < blocks.Count; i++)
                {
                    BitSet kill = new BitSet(domain);
                    BitSet gen = new BitSet(domain);
                    ((Block)blocks[i]).FillAnticipableExpressionsInfo(domain, ref gen, ref kill);
                    info[i].Kill = kill;
                    info[i].Gen = gen;
                }
            }
            public override void TransferFunction()
            {
                for (int i = 0; i < blocks.Count; i++)
                {
                    BitSet kill = new BitSet(domain);
                    BitSet gen = new BitSet(domain);
                    ((Block)blocks[i]).FillAnticipableExpressionsInfo(domain, ref gen, ref kill);
                    Kill[i] = kill;
                    Gen[i] = gen;
                }
            }
        }

//        private ReachableDefinition iReachableDefinition;
//        private LiveVariable iLiveVariable;
//        private AvailableExpressions iAvailableExpressions;
//        private AnticipableExpressions iAnticipableExpressions;
//        private PartiallyAvailableExpressions iPartiallyAvailableExpressions;
//        private DeadVariable iDeadVariable;
//        private DefinitionsForCopyPropagation iDefinitionsForCopyPropagation;
//
//
        public Set UDef;
        public Set UVar;
        public Set UExp;

        private Info[] ReachableDefinitionInfo;
        private Info[] LiveVariableInfo;
        private Info[] AvailableExpressionsInfo;
        private Info[] AnticipableExpressionsInfo;
        private Info[] PartiallyAvailableExpressionsInfo;
        private Info[] DeadVariableInfo;
        private Info[] DefinitionsForCopyPropagationInfo;

        public DataFlow(IntermediateCode iCode)
        {
            blocks = new ArrayList();

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
            }
            if (!(iCode[iCode.Count - 1][0].Op == Operator.IFEXP || iCode[iCode.Count - 1][0].Op == Operator.GOTO ||
                  iCode[iCode.Count - 1][0].Op == Operator.IFTRUE || iCode[iCode.Count - 1][0].Op == Operator.IFFALSE ||
                  iCode[iCode.Count - 1][0].Op == Operator.CALL))
            {
                NewBlock(iCode.Count);
            }

            #endregion

            #region Copia as instruções para os blocos

            int pos = ((Block)blocks[1]).Predecessor.Add(blocks[0]);
            pos = ((Block)blocks[0]).Sucessor.Add(blocks[1]);

            for (int i = 1; i < blocks.Count - 1; i++)
            {
                int j, trg;

                for (j = ((Block)blocks[i]).Leader; j < ((Block)blocks[i + 1]).Leader - 1; j++)
                    ((Block)blocks[i]).Add(iCode[j]);

                ((Block)blocks[i]).Add(iCode[j]);

                switch (((Block)blocks[i]).Last[0].Op)
                {
                    case Operator.IFEXP:
                    case Operator.IFTRUE:
                    case Operator.IFFALSE:
                        trg = FindBlock(((Label)((Block)blocks[i]).Last[0].Arg2).Value);
                        pos = ((Block)blocks[trg]).Predecessor.Add(blocks[i]);
                        pos = ((Block)blocks[i]).Sucessor.Add(blocks[trg]);
                        trg = FindBlock(((Block)blocks[i + 1]).Leader);
                        pos = ((Block)blocks[trg]).Predecessor.Add(blocks[i]);
                        pos = ((Block)blocks[i]).Sucessor.Add(blocks[trg]);
                        break;
                    case Operator.CALL:
                    case Operator.GOTO:
                        trg = FindBlock(((Label)((Block)blocks[i]).Last[0].Arg2).Value);
                        pos = ((Block)blocks[trg]).Predecessor.Add(blocks[i]);
                        pos = ((Block)blocks[i]).Sucessor.Add(blocks[trg]);
                        break;
                    default:
                        trg = FindBlock(((Block)blocks[i + 1]).Leader);
                        pos = ((Block)blocks[trg]).Predecessor.Add(blocks[i]);
                        pos = ((Block)blocks[i]).Sucessor.Add(blocks[trg]);
                        break;
                }
            }
            #endregion

            // Incorpora o indexador do vetor blocks dentro de cada block
            for (int i = 0; i < blocks.Count; i++)
                ((Block)blocks[i]).Id = i;

            #region Substitui os labels de instruções por labels de blocos
            for (int i = 1; i < blocks.Count - 1; i++)
            {
                Block current = (Block)blocks[i];

                IntermediateInstruction last = current.Last;

                switch (last[0].Op)
                {
                    case Operator.CALL:
                    case Operator.GOTO:
                        for (int k = 0; k < blocks.Count; k++)
                        {
                            if (((Label)(last[0].Arg2)).Value == ((Block)blocks[k]).Leader)
                            {
                                last[0].Arg2 = new Label(k);
                                break;
                            }
                        }
                        break;
                    case Operator.IFEXP:
                    case Operator.IFTRUE:
                    case Operator.IFFALSE:
                        for (int k = 0; k < blocks.Count; k++)
                        {
                            if (((Label)(last[0].Arg2)).Value == ((Block)blocks[k]).Leader)
                            {
                                last[0].Arg2 = new Label(k);
                                break;
                            }
                        }
                        break;
                    case Operator.RETURN:
                        break;
                    default:
                        break;
                }
            }
            #endregion

            UVar = Address.Symbols;
            UDef = new Set();
            UExp = new Set();

            UExp.Add(new TAC(Operator.MUL, (Address)Name.Symbols[0], (Address)Name.Symbols[1]));
            UExp.Add(new TAC(Operator.ADD, (Address)Name.Symbols[0], (Address)Name.Symbols[1]));
            UExp.Add(new TAC(Operator.SUB, (Address)Name.Symbols[0], (Address)Name.Symbols[1]));
            UExp.Add(new TAC(Operator.SUB, (Address)Name.Symbols[0], (Address)Name.Symbols[2]));
            UExp.Add(new TAC(Operator.ADD, (Address)Name.Symbols[1], (Address)Name.Symbols[2]));

            // Primeiro chama FillDeclarationInfo
            for (int i = 1; i < blocks.Count - 1; i++)
                ((Block)blocks[i]).FillDeclarationInfo(ref UDef, ref UExp);

            ReachableDefinitionInfo = new Info[blocks.Count];
            LiveVariableInfo = new Info[blocks.Count];
            AvailableExpressionsInfo = new Info[blocks.Count];
            AnticipableExpressionsInfo = new Info[blocks.Count];
            PartiallyAvailableExpressionsInfo = new Info[blocks.Count];
            DeadVariableInfo = new Info[blocks.Count];
            DefinitionsForCopyPropagationInfo = new Info[blocks.Count];

            for (int i = 0; i < blocks.Count; i++)
            {
                ReachableDefinitionInfo[i] = new Info(UDef);
                LiveVariableInfo[i] = new Info(UVar);
                AvailableExpressionsInfo[i] = new Info(UExp);
                AnticipableExpressionsInfo[i] = new Info(UExp);
                PartiallyAvailableExpressionsInfo[i] = new Info(UExp);
                DeadVariableInfo[i] = new Info(UVar);
                DefinitionsForCopyPropagationInfo[i] = new Info(UDef);
            }

            iReachableDefinition.Analysis(ref ReachableDefinitionInfo);
            iLiveVariable.Analysis(ref LiveVariableInfo);
            iAvailableExpressions.Analysis(ref AvailableExpressionsInfo);
            iAnticipableExpressions.Analysis(ref AnticipableExpressionsInfo);
            iPartiallyAvailableExpressions.Analysis(ref PartiallyAvailableExpressionsInfo);
            iDeadVariable.Analysis(ref DeadVariableInfo);
            iDefinitionsForCopyPropagation.Analysis(ref DefinitionsForCopyPropagationInfo);

//
//            iReachableDefinition = 
//                new ReachableDefinition(this, "ANALISE DE ALCANCABILIDADE DE DEFINICOES");
//            iLiveVariable = 
//                new LiveVariable(this, "ANALISE DE VIVACIDADE DE VARIAVEIS");
//            iAvailableExpressions = 
//                new AvailableExpressions(this, "ANALISE DE DISPONIBILIDADE DE EXPRESSOES");
//            iAnticipableExpressions = 
//                new AnticipableExpressions(this, "ANALISE DE DISPONIBILIDADE DE EXPRESSOES ANTICIPAVEIS");
//            iPartiallyAvailableExpressions = 
//                new PartiallyAvailableExpressions(this, "ANALISE DE DISPONIBILIDADE PARCIAL DE EXPRESSOES");
//            iDeadVariable = 
//                new DeadVariable(this, "ANALISE DE MORTALIDADE DE VARIAVEIS");
//            iDefinitionsForCopyPropagation = 
//                new DefinitionsForCopyPropagation(this, "ANALISE DE ALCANCABILIDADE DE DEFINICOES PARA PROPAGACAO DE COPIAS");
//
//            iReachableDefinition.Analysis(ref ReachableDefinitionInfo);
//            iLiveVariable.Analysis(ref LiveVariableInfo);
//            iAvailableExpressions.Analysis(ref AvailableExpressionsInfo);
//            iAnticipableExpressions.Analysis(ref AnticipableExpressionsInfo);
//            iPartiallyAvailableExpressions.Analysis(ref PartiallyAvailableExpressionsInfo);
//            iDeadVariable.Analysis(ref DeadVariableInfo);
//            iDefinitionsForCopyPropagation.Analysis(ref DefinitionsForCopyPropagationInfo);
//
//            ArrayList earliest = new ArrayList();
//            for (int i = 1; i < blocks.Count - 1; i++)
//            {
//                pos = earliest.Add(new BitSet(UExp));
//                earliest[pos] = iAnticipableExpressions.GetIN(i) - iAvailableExpressions.GetIN(i);
//            }
//
//            ArrayList latest = new ArrayList();
//            for (int i = 1; i < blocks.Count - 1; i++)
//            {
//                BitSet tmp = new BitSet(UExp);
//                pos = latest.Add(new BitSet(UExp));
//                foreach (Block S in ((Block)blocks[i]).Sucessor)
//                    tmp = tmp * (earliest[S.Id] + ((Optimization)postponable[S.Id]).IN);
//                tmp = iAvailableExpressions.GetGen(i) + !tmp;
//                latest[pos] = (earliest[i] + ((Optimization)postponable[i]).IN) * tmp;
//            }

        }

        public int FindBlock(int leader)
        {
            for (int i = 1; i < blocks.Count; i++)
                if (leader == ((Block)blocks[i]).Leader)
                    return i;
            return -1;
        }

        private void NewBlock(int val)
        {
            for (int i = 1; i < blocks.Count; i++)
                if (((Block)blocks[i]).Leader == val)
                    return ;

            Block block = new Block(val);

            int pos = blocks.Add(block);

            // Mantem os blocos classificados 
            for (int i = pos - 1; i >= 0; i--)
            {
                if (((Block)blocks[i]).Leader > val)
                {
                    Block tmp = (Block)blocks[i];
                    blocks[i] = blocks[i + 1];
                    blocks[i + 1] = tmp;
                }
                else
                    break;
            }
        }

        public override string ToString()
        {
            string str = "";
            int i;
            string Title;

            for (int bk = 0; bk < blocks.Count; bk++)
                str += blocks[bk].ToString();

            Title = "ANALISE DE ALCANCABILIDADE DE DEFINICOES";
            for (i = 0; i < Title.Length; i++)
                str += "=";
            str += "\n";
            str += "Dominio: " + UDef.ToString() + "\n\n";

            // if (ReachableDefinitionInfo[0].Gen.Count > 0)
            {
                str += "      ";
                str += "Gen";
                for (i = 3; i < ReachableDefinitionInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += " ";
                str += "Kill";
                for (i = 4; i < ReachableDefinitionInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += "\t";
                str += "OUT";
                for (i = 3; i < ReachableDefinitionInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += " IN\n";
                for (int bk = 1; bk < blocks.Count - 1; bk++)
                {
                    string tmp = String.Format("B{0:000}  ", bk);
                    str += tmp + ReachableDefinitionInfo[bk].Gen.ToBinary() + " " +
                        ReachableDefinitionInfo[bk].Kill.ToBinary() + " " +
                        ReachableDefinitionInfo[bk].IN.ToBinary() + " " +
                        ReachableDefinitionInfo[bk].OUT.ToBinary() + "\n";
                }
            }

            Title = "ANALISE DE VIVACIDADE DE VARIAVEIS";
            for (i = 0; i < Title.Length; i++)
                str += "=";
            str += "\n";
            str += "Dominio: " + UVar.ToString() + "\n\n";

            // if (LiveVariableInfo[0].Gen.Count > 0)
            {
                str += "      ";
                str += "Gen";
                for (i = 3; i < LiveVariableInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += " ";
                str += "Kill";
                for (i = 4; i < LiveVariableInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += "\t";
                str += "OUT";
                for (i = 3; i < LiveVariableInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += " IN\n";
                for (int bk = 1; bk < blocks.Count - 1; bk++)
                {
                    string tmp = String.Format("B{0:000}  ", bk);
                    str += tmp + LiveVariableInfo[bk].Gen.ToBinary() + " " +
                        LiveVariableInfo[bk].Kill.ToBinary() + " " +
                        LiveVariableInfo[bk].IN.ToBinary() + " " +
                        LiveVariableInfo[bk].OUT.ToBinary() + "\n";
                }
            }

            Title = "ANALISE DE DISPONIBILIDADE DE EXPRESSOES";
            for (i = 0; i < Title.Length; i++)
                str += "=";
            str += "\n";
            str += "Dominio: " + UExp.ToString() + "\n\n";

            // if (AvailableExpressionsInfo[0].Gen.Count > 0)
            {
                str += "      ";
                str += "Gen";
                for (i = 3; i < AvailableExpressionsInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += " ";
                str += "Kill";
                for (i = 4; i < AvailableExpressionsInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += "\t";
                str += "OUT";
                for (i = 3; i < AvailableExpressionsInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += " IN\n";
                for (int bk = 1; bk < blocks.Count - 1; bk++)
                {
                    string tmp = String.Format("B{0:000}  ", bk);
                    str += tmp + AvailableExpressionsInfo[bk].Gen.ToBinary() + " " +
                        AvailableExpressionsInfo[bk].Kill.ToBinary() + " " +
                        AvailableExpressionsInfo[bk].IN.ToBinary() + " " +
                        AvailableExpressionsInfo[bk].OUT.ToBinary() + "\n";
                }
            }

            Title = "ANALISE DE DISPONIBILIDADE DE EXPRESSOES ANTICIPAVEIS";
            for (i = 0; i < Title.Length; i++)
                str += "=";
            str += "\n";
            str += "Dominio: " + UExp.ToString() + "\n\n";

            // if (AnticipableExpressionsInfo[0].Gen.Count > 0)
            {
                str += "      ";
                str += "Gen";
                for (i = 3; i < AnticipableExpressionsInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += " ";
                str += "Kill";
                for (i = 4; i < AnticipableExpressionsInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += "\t";
                str += "OUT";
                for (i = 3; i < AnticipableExpressionsInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += " IN\n";
                for (int bk = 1; bk < blocks.Count - 1; bk++)
                {
                    string tmp = String.Format("B{0:000}  ", bk);
                    str += tmp + AnticipableExpressionsInfo[bk].Gen.ToBinary() + " " +
                        AnticipableExpressionsInfo[bk].Kill.ToBinary() + " " +
                        AnticipableExpressionsInfo[bk].IN.ToBinary() + " " +
                        AnticipableExpressionsInfo[bk].OUT.ToBinary() + "\n";
                }
            }

            Title = "ANALISE DE DISPONIBILIDADE PARCIAL DE EXPRESSOES";
            for (i = 0; i < Title.Length; i++)
                str += "=";
            str += "\n";
            str += "Dominio: " + UExp.ToString() + "\n\n";

            // if (PartiallyAvailableExpressionsInfo[0].Gen.Count > 0)
            {
                str += "      ";
                str += "Gen";
                for (i = 3; i < PartiallyAvailableExpressionsInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += " ";
                str += "Kill";
                for (i = 4; i < PartiallyAvailableExpressionsInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += "\t";
                str += "OUT";
                for (i = 3; i < PartiallyAvailableExpressionsInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += " IN\n";
                for (int bk = 1; bk < blocks.Count - 1; bk++)
                {
                    string tmp = String.Format("B{0:000}  ", bk);
                    str += tmp + PartiallyAvailableExpressionsInfo[bk].Gen.ToBinary() + " " +
                        PartiallyAvailableExpressionsInfo[bk].Kill.ToBinary() + " " +
                        PartiallyAvailableExpressionsInfo[bk].IN.ToBinary() + " " +
                        PartiallyAvailableExpressionsInfo[bk].OUT.ToBinary() + "\n";
                }
            }

            Title = "ANALISE DE MORTALIDADE DE VARIAVEIS";
            for (i = 0; i < Title.Length; i++)
                str += "=";
            str += "\n";
            str += "Dominio: " + UExp.ToString() + "\n\n";

            // if (DeadVariableInfo[0].Gen.Count > 0)
            {
                str += "      ";
                str += "Gen";
                for (i = 3; i < DeadVariableInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += " ";
                str += "Kill";
                for (i = 4; i < DeadVariableInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += "\t";
                str += "OUT";
                for (i = 3; i < DeadVariableInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += " IN\n";
                for (int bk = 1; bk < blocks.Count - 1; bk++)
                {
                    string tmp = String.Format("B{0:000}  ", bk);
                    str += tmp + DeadVariableInfo[bk].Gen.ToBinary() + " " +
                        DeadVariableInfo[bk].Kill.ToBinary() + " " +
                        DeadVariableInfo[bk].IN.ToBinary() + " " +
                        DeadVariableInfo[bk].OUT.ToBinary() + "\n";
                }
            }

            Title = "ANALISE DE ALCANCABILIDADE DE DEFINICOES PARA PROPAGACAO DE COPIAS";
            for (i = 0; i < Title.Length; i++)
                str += "=";
            str += "\n";
            str += "Dominio: " + UExp.ToString() + "\n\n";

            // if (DefinitionsForCopyPropagationInfo[0].Gen.Count > 0)
            {
                str += "      ";
                str += "Gen";
                for (i = 3; i < DefinitionsForCopyPropagationInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += " ";
                str += "Kill";
                for (i = 4; i < DefinitionsForCopyPropagationInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += "\t";
                str += "OUT";
                for (i = 3; i < DefinitionsForCopyPropagationInfo[0].Gen.Universe.Count; i++)
                    str += " ";
                str += " IN\n";
                for (int bk = 1; bk < blocks.Count - 1; bk++)
                {
                    string tmp = String.Format("B{0:000}  ", bk);
                    str += tmp + DefinitionsForCopyPropagationInfo[bk].Gen.ToBinary() + " " +
                        DefinitionsForCopyPropagationInfo[bk].Kill.ToBinary() + " " +
                        DefinitionsForCopyPropagationInfo[bk].IN.ToBinary() + " " +
                        DefinitionsForCopyPropagationInfo[bk].OUT.ToBinary() + "\n";
                }
            }

//            str += "\n";
//            str += "\n";
//            str += iReachableDefinition.ToString();
//            str += "\n";
//            str += "\n";
//            str += iLiveVariable.ToString();
//            str += "\n";
//            str += "\n";
//            str += iAvailableExpressions.ToString();
//            str += "\n";
//            str += "\n";
//            str += iAnticipableExpressions.ToString();
//            str += "\n";
//            str += "\n";
//            str += iPartiallyAvailableExpressions.ToString();
//            str += "\n";
//            str += "\n";
//            str += iDeadVariable.ToString();
//            str += "\n";
//            str += "\n";
//            str += iDefinitionsForCopyPropagation.ToString();
//            str += "\n";
//            str += "\n";
//
//            str += "      ";
//            str += "Red";
//            for (i = 3; i < UExp.Count; i++)
//                str += " ";
//            str += "\t";
//            str += "PRed";
//            for (i = 4; i < UExp.Count; i++)
//                str += " ";
//            str += "\n";
//
//            for (int B = 1; B < blocks.Count - 1; B++)
//            {
//                BitSet Redundant = iAvailableExpressions.GetRedundant(B);
//                BitSet ParRedund = iPartiallyAvailableExpressions.GetParRedund(B);
//
//                string tmp = String.Format("B{0:000}  ", B);
//
//                str += tmp + Redundant.ToBinary();
//                str += "\t";
//                str += ParRedund.ToBinary();
//                str += "\n";
//            }

            return str;
        }

        private Block ENTRY
        { get { return (Block)blocks[0]; } }

        private Block EXIT
        { get { return (Block)blocks[blocks.Count - 1]; } }
    }
}
