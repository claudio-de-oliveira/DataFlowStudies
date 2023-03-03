using AbstractMachine;

namespace TesteIC
{
    internal class Teste2
    {
        public static AbstractMachine.IntermediateCode CreateCode()
        {
            AbstractMachine.IntermediateCode iCode = new AbstractMachine.IntermediateCode();

            Name a = new Name("a");
            Name b = new Name("b");
            Name c = new Name("c");
            Name d = new Name("d");

            // n1
            iCode.AddInstruction(iCode.CreateCopy(b, Constant.Create(4))); // 0
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, a, b, c)); // 1
            iCode.AddInstruction(iCode.CreateBinary(Operator.MUL, d, a, b)); // 2
            iCode.AddInstruction(iCode.CreateIfTrue(Constant.Create(1), new Label(6))); // n3 3 
            // n2
            iCode.AddInstruction(iCode.CreateBinary(Operator.SUB, b, a, c)); // 4
            iCode.AddInstruction(iCode.CreateGoto(new Label(20))); // n8 5
            // n3
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, c, b, c)); // 6
            iCode.AddInstruction(iCode.CreateIfTrue(Constant.Create(1), new Label(12))); // n5 7
            // n4
            iCode.AddInstruction(iCode.CreateBinary(Operator.MUL, c, a, b)); // 8
            Name tmp1 = new Name();
            iCode.AddInstruction(iCode.CreateBinary(Operator.SUB, tmp1, a, b)); // 9
            iCode.AddInstruction(iCode.CreateParam(tmp1)); // 10
            iCode.AddInstruction(iCode.CreateGoto(new Label(17))); // n7 11
            // n5
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, d, a, b)); // 12
            iCode.AddInstruction(iCode.CreateGoto(new Label(14))); // n6 13
            // n6
            Name tmp2 = new Name();
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, tmp2, b, c)); // 14
            iCode.AddInstruction(iCode.CreateParam(tmp2)); // 15
            iCode.AddInstruction(iCode.CreateIfTrue(Constant.Create(1), new Label(12))); // n5 16
            // n7
            Name tmp3 = new Name();
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, tmp3, a, b)); // 17
            iCode.AddInstruction(iCode.CreateParam(tmp3)); // 18
            iCode.AddInstruction(iCode.CreateIfTrue(Constant.Create(1), new Label(6))); // n3 19
            // n8
            Name tmp4 = new Name();
            iCode.AddInstruction(iCode.CreateBinary(Operator.SUB, tmp4, a, c)); // 20
            iCode.AddInstruction(iCode.CreateParam(tmp4)); // 21
            Name tmp5 = new Name();
            iCode.AddInstruction(iCode.CreateBinary(Operator.ADD, tmp5, b, c)); // 22
            iCode.AddInstruction(iCode.CreateParam(tmp5)); // 23

            return iCode;
        }
    }
}
