using AbstractMachine;

namespace TesteIC
{
    internal class Teste6
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
            iCode.AddInstruction(iCode.CreateIfTrue(Constant.Create(0), new Label(3))); // 0
            // n2
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, a, b, c)); // 1
            iCode.AddInstruction(iCode.CreateGoto(new Label(4))); // 2
            // n3
            iCode.AddInstruction(iCode.CreateCopy(e, Constant.Create(7))); // 3
            // n4
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, d, b, c)); // 4

            return iCode;
        }
    }
}
