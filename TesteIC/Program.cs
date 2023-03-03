using System.IO;

using AbstractMachine;
using Cormen;

namespace TesteIC
{
    class Program
    {
        private static void Optimize(DataFlow df, string path, string texfile)
        {
            string fullpath = Path.Combine(path, texfile);
            DirectoryInfo di = Directory.CreateDirectory(fullpath);
            ArrayOf<string> fList = df.Optimize(di.FullName);
            df.Write(di.FullName, texfile + ".tex", fList);
        }

        static void Main(string[] args)
        {
            var userProfile = System.Environment.GetEnvironmentVariable("USERPROFILE");
            var path = Path.Combine(userProfile, "Result-AFD");

            if (!Directory.Exists(path))
                Directory.CreateDirectory(path);

            AbstractMachine.IntermediateCode code;
            DataFlow df;

            code = Teste1.CreateCode();
            df = new DataFlow(code);
            Optimize(df, path, "teste1");
            Address.Reinitilize();

            code = Teste2.CreateCode();
            df = new DataFlow(code);
            Optimize(df, path, "teste2");
            Address.Reinitilize();

            code = Teste3.CreateCode();
            df = new DataFlow(code);
            Optimize(df, path, "teste3");
            Address.Reinitilize();

            code = Teste4.CreateCode();
            df = new DataFlow(code);
            Optimize(df, path, "teste4");
            Address.Reinitilize();

            code = Teste5.CreateCode();
            df = new DataFlow(code);
            Optimize(df, path, "teste5");
            Address.Reinitilize();

            code = Teste6.CreateCode();
            df = new DataFlow(code);
            Optimize(df, path, "teste6");
            Address.Reinitilize();

            code = Teste7.CreateCode();
            df = new DataFlow(code);
            Optimize(df, path, "teste7");
            Address.Reinitilize();
        }
    }
}
