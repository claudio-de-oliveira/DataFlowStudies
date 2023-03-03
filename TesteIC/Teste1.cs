using AbstractMachine;

namespace TesteIC
{
    internal class Teste1
    {
        public static AbstractMachine.IntermediateCode CreateCode()
        {
            AbstractMachine.IntermediateCode iCode = new AbstractMachine.IntermediateCode();

            Name i = new Name("i");
            Name j = new Name("j");
            Name n = new Name("n");
            Name a = new Name("a");
            Name v = new Name("v");
            Name x = new Name("x");

            /* 0*/
            iCode.AddInstruction(iCode.CreateCopy(i, Constant.Create(0)));
            /* 1*/
            iCode.AddInstruction(iCode.CreateCopy(j, Constant.Create(0)));
            Name tmp1 = new Name();
            /* 2*/
            iCode.AddInstruction(iCode.CreateBinary(Operator.MUL, tmp1, Constant.Create(4), n));
            /* 3*/
            iCode.AddInstruction(iCode.CreateFromArray(v, tmp1, a));

            /* 4*/
            iCode.AddInstruction(iCode.CreateUnary(Operator.INC, i, i));
            Name tmp2 = new Name();
            /* 5*/
            iCode.AddInstruction(iCode.CreateBinary(Operator.MUL, tmp2, Constant.Create(4), i));
            Name tmp3 = new Name();
            /* 6*/
            iCode.AddInstruction(iCode.CreateFromArray(tmp3, tmp2, a));
            /* 7*/
            iCode.AddInstruction(iCode.CreateIfExp(Operator.LT, tmp3, v, new Label(4)));

            /* 8*/
            iCode.AddInstruction(iCode.CreateUnary(Operator.DEC, j, j));
            Name tmp4 = new Name();
            /* 9*/
            iCode.AddInstruction(iCode.CreateBinary(Operator.MUL, tmp4, Constant.Create(4), j));
            Name tmp5 = new Name();
            /*10*/
            iCode.AddInstruction(iCode.CreateFromArray(tmp5, tmp4, a));
            /*11*/
            iCode.AddInstruction(iCode.CreateIfExp(Operator.GT, tmp5, v, new Label(8)));

            /*12*/
            iCode.AddInstruction(iCode.CreateIfExp(Operator.GE, i, j, new Label(17)));

            /*13*/
            iCode.AddInstruction(iCode.CreateCopy(x, tmp3));
            /*14*/
            iCode.AddInstruction(iCode.CreateToArray(a, tmp2, tmp5));
            /*15*/
            iCode.AddInstruction(iCode.CreateToArray(a, tmp4, x));
            /*16*/
            iCode.AddInstruction(iCode.CreateGoto(new Label(4)));

            /*17*/
            iCode.AddInstruction(iCode.CreateCopy(x, tmp3));
            Name tmp14 = new Name();
            /*18*/
            iCode.AddInstruction(iCode.CreateFromArray(tmp14, tmp1, a));
            /*19*/
            iCode.AddInstruction(iCode.CreateToArray(a, tmp2, tmp14));
            /*20*/
            iCode.AddInstruction(iCode.CreateToArray(a, tmp1, x));

            return iCode;
        }
    }
}
