using System;
using System.Collections;
using AbstractMachine;

namespace AbstractMachine
{
    public enum EdgeCategory
    {
        ADVANCING = 1,
        RETREATING,
        CROSS,
        BACKEDGE
    };

    public class Transition
    {
        private Block target;
        private EdgeCategory category;

        public Transition(Block to)
        {
            target = to;
        }

        public Block Target
        {
            get { return target; }
            set { target = value; }
        }

        public EdgeCategory Category
        {
            get { return category; }
            set { category = value; }
        }
    }

    public class DepthFirstSpanningTree
    {
        private ArrayList[] transitions;
        private ArrayList loops;

        public DepthFirstSpanningTree(ArrayOfBlock blocks)
        {
            int c = blocks.Count;
            
            transitions = new ArrayList[c];
            loops = new ArrayList();

            for (int i = 0; i < blocks.Count; i++)
                transitions[i] = new ArrayList();
            int val = 0;
            Search(blocks[0], ref c, ref val);

            BitSet[] D = blocks.Dominators();
            
            for (int i = 0; i < blocks.Count; i++)
            {
                foreach (Transition T in transitions[i])
                {
                    if (blocks[i].dfs_entry < T.Target.dfs_entry && blocks[i].dfs_exit > T.Target.dfs_exit)
                        T.Category = EdgeCategory.ADVANCING;
                    else if (blocks[i].dfs_entry > T.Target.dfs_entry && blocks[i].dfs_exit < T.Target.dfs_exit)
                    {
                        T.Category = EdgeCategory.RETREATING;
                        foreach (Block head in D[i])
                        {
                            if (head == T.Target)
                            {
                                T.Category = EdgeCategory.BACKEDGE;

                                for (int bk = 0; bk < blocks.Count; bk++)
                                    blocks[bk].Visited = false;
                                T.Target.Visited = true;

                                ArrayOfBlock loop = new ArrayOfBlock();
                                loop.Add(T.Target);
                                loop.Add(blocks[i]);
                                Search2(blocks[i], ref loop);

                                loops.Add(loop);

                                break;
                            }
                        }
                    }
                    else
                        T.Category = EdgeCategory.CROSS;
                }
            }
        }

        private void Search2(Block blk, ref ArrayOfBlock loop)
        {
            blk.Visited = true;
            foreach (Block pred in blk.Predecessor)
            {
                if (pred.Visited == false)
                {
                    loop.Add(pred);
                    Search2(pred, ref loop);
                }
            }
        }

        private void Search(Block blk, ref int c, ref int val)
        {
            blk.Visited = true;
            blk.dfs_entry = val;
            val++;
            foreach (Block succ in blk.Sucessor)
            {
                if (succ.Visited == false)
                {
                    Transition tr = new Transition(succ);
                    transitions[blk.Id].Add(tr);
                    Search(succ, ref c, ref val);
                }
                else 
                {
                    Transition tr = new Transition(succ);
                    transitions[blk.Id].Add(tr);
                }
                val++;
                blk.dfs_exit = val;
            }
            blk.dfn = c;
            c--;
        }
    }
}
