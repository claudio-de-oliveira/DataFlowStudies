using AbstractMachine;

namespace TesteIC
{
    internal class Teste3
    {
        public static AbstractMachine.IntermediateCode CreateCode()
        {
            AbstractMachine.IntermediateCode iCode = new AbstractMachine.IntermediateCode();

            Name a = new Name("a");
            Name b = new Name("b");
            Name c = new Name("c");
            Name d = new Name("d");

            // n1
            iCode.AddInstruction(iCode.CreateCopy(a, Constant.Create(4))); // 0
            iCode.AddInstruction(iCode.CreateCopy(b, Constant.Create(5))); // 1
            iCode.AddInstruction(iCode.CreateIfTrue(d, new Label(7))); // 2
            // n2
            iCode.AddInstruction(iCode.CreateCopy(b, Constant.Create(5))); // 3
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, c, a, b)); // 4
            iCode.AddInstruction(iCode.CreateIfTrue(d, new Label(9))); // 5
            // n3
            iCode.AddInstruction(iCode.CreateGoto(new Label(16))); // 6
            // n4
            iCode.AddInstruction(iCode.CreateCopy(a, Constant.Create(4))); // 7
            iCode.AddInstruction(iCode.CreateGoto(new Label(9))); // 8
            // n5
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, c, a, b)); // 9
            iCode.AddInstruction(iCode.CreateCopy(a, Constant.Create(5))); // 10
            iCode.AddInstruction(iCode.CreateCopy(b, c)); // 11
            iCode.AddInstruction(iCode.CreateCopy(d, b)); // 12
            iCode.AddInstruction(iCode.CreateGoto(new Label(14))); // 13
            // n6
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, c, a, b)); // 14
            iCode.AddInstruction(iCode.CreateIfTrue(d, new Label(9))); // 15
            // n7
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, c, a, b)); // 16

            return iCode;
        }
    }
}
