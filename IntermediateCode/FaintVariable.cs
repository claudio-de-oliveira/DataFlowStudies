using System;
using System.Collections;
using AbstractMachine;
using SetCollection;

namespace IntermediateCode
{
    class FaintVariable
    {
        private BitSet[] constGen;
        private BitSet[] depGen;
        private BitSet[] constKill;
        private BitSet[] depKill;
        private ArrayOfBlock blocks;
        private Set universe;

        public FaintVariable(ArrayOfBlock blocks, Set universe)
        {
            constGen = new BitSet[blocks.Count];
            depGen = new BitSet[blocks.Count];
            constKill = new BitSet[blocks.Count];
            depKill = new BitSet[blocks.Count];
            for (int bk = 0; bk < blocks.Count; bk++)
            {
                constGen[bk] = new BitSet(universe);
                depGen[bk] = new BitSet(universe);
                constKill[bk] = new BitSet(universe);
                depKill[bk] = new BitSet(universe);
            }
            this.universe = universe;
            this.blocks = blocks;
        }

        private void Analysis(ArrayOfBlock blocks)
        {
            bool done = false;

            while (!done)
            {
                done = true;

                for (int bk = blocks.Count - 2; bk > 0; bk--)
                {

                }
            }
        }

        private void TransferFunction()
        {
            for (int bk = 0; bk < blocks.Count; bk++)
            {
                AbstractMachine.IntermediateCode code = blocks[bk].Code;

                for (int i = code.Count - 1; i >= 0; i--)
                {
                    if (code[i].GetType() != typeof(Nop))
                    {
                        switch (code[i][0].Op)
                        {
                            case Operator.MUL:
                            case Operator.DIV:
                            case Operator.ADD:
                            case Operator.SUB:
                                if (code[i].Target != code[i][0].Arg1 && code[i].Target != code[i][0].Arg2)
                                    constGen[bk].Add(code[i].Target);
                                break;

                            case Operator.DEC:
                            case Operator.INC:
                            case Operator.NEG:
                                if (code[i].Target != code[i][0].Arg2)
                                    constGen[bk].Add(code[i].Target);
                                break;

                            case Operator.COPY:
                                constGen[bk].Add(code[i].Target);
                                break;

                            case Operator.ADDRESS:
                                constGen[bk].Add(code[i].Target);
                                break;

                            case Operator.FROMMEMORY:
                                constGen[bk].Add(code[i].Target);
                                break;

                            case Operator.TOMEMORY:
                                break;

                            case Operator.IFTRUE:
                            case Operator.IFFALSE:
                            case Operator.IFEXP:
                                break;

                            case Operator.PARAM:
                                break;

                            case Operator.RETURN:
                                break;

                            case Operator.FROMARRAY:
                                constGen[bk].Add(code[i].Target);
                                break;

                            case Operator.TOARRAY:
                                break;
                        }
                    }
                }
            }
        }
    }
}
