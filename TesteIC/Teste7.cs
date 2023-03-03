using AbstractMachine;

namespace TesteIC
{
    internal class Teste7
    {
        public static AbstractMachine.IntermediateCode CreateCode()
        {
            AbstractMachine.IntermediateCode iCode = new AbstractMachine.IntermediateCode();

            Name a = new Name("a");
            Name b = new Name("b");
            Name c = new Name("c");
            Name d = new Name("d");
            Name e = new Name("e");

            // n1
            iCode.AddInstruction(iCode.CreateCopy(b, Constant.Create(1))); // 0
            iCode.AddInstruction(iCode.CreateIfTrue(Constant.Create(0), new Label(4))); // 1
            // n2
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, a, b, c)); // 2
            iCode.AddInstruction(iCode.CreateGoto(new Label(6))); // 3
            // n3
            iCode.AddInstruction(iCode.CreateCopy(b, Constant.Create(7))); // 4
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, d, b, c)); // 5
            // n4
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, e, b, c)); // 6
            // n5
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, a, b, c)); // 7
            iCode.AddInstruction(iCode.CreateIfTrue(Constant.Create(0), new Label(7))); // 8
            // n6
            iCode.AddInstruction(iCode.CreateIfTrue(Constant.Create(0), new Label(12))); // 9
            // n7
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, a, b, c)); // 10
            iCode.AddInstruction(iCode.CreateGoto(new Label(13))); // 11
            // n8
            iCode.AddInstruction(iCode.CreateGoto(new Label(13))); // 12
            // n9
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, d, b, c)); // 13

            return iCode;
        }
    }
}
