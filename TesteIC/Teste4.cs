using AbstractMachine;

namespace TesteIC
{
    internal class Teste4
    {
        public static AbstractMachine.IntermediateCode CreateCode()
        {
            AbstractMachine.IntermediateCode iCode = new AbstractMachine.IntermediateCode();

            Name a = new Name("a");
            Name b = new Name("b");
            Name c = new Name("c");
            Name x = new Name("x");

            // n1
            iCode.AddInstruction(iCode.CreateCopy(b, Constant.Create(0))); // 0
            iCode.AddInstruction(iCode.CreateIfTrue(Constant.Create(0), new Label(4))); // 1
            // n2
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, a, b, c)); // 2
            iCode.AddInstruction(iCode.CreateGoto(new Label(5))); // 3
            // n3
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, x, b, Constant.Create(1))); // 4
            // n4
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, a, b, c)); // 5

            return iCode;
        }
    }
}
