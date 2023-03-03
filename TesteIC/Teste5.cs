using AbstractMachine;

namespace TesteIC
{
    internal class Teste5
    {
        public static AbstractMachine.IntermediateCode CreateCode()
        {
            AbstractMachine.IntermediateCode iCode = new AbstractMachine.IntermediateCode();

            Name a = new Name("a");
            Name b = new Name("b");
            Name c = new Name("c");

            // n1
            iCode.AddInstruction(iCode.CreateCopy(b, Constant.Create(0))); // 0
            iCode.AddInstruction(iCode.CreateCopy(c, Constant.Create(1))); // 1
            // n2
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, a, b, c)); // 2
            iCode.AddInstruction(iCode.CreateIfTrue(Constant.Create(0), new Label(2))); // 3

            return iCode;
        }
    }
}
