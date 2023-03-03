using System;
using SetCollection;
using Cormen;

namespace AbstractMachine
{
    class Edge
    {
        private Region source, target;

        public Edge(Region source, Region target)
        {
            this.source = source;
            this.target = target;
        }

        public Region Source
        {
            get { return source; }
            set { source = value; }
        }
        public Region Target
        {
            get { return target; }
            set { target = value; }
        }

    }

    public class RegionHierarchie
    {
        private ArrayOf<Transition>[] transitions;
        public static ArrayOf<Region> Regions = new ArrayOf<Region>();
        private ArrayOf<Transition> edges;

        public RegionHierarchie(ArrayOfBlock blocks)
        {
            for (int i = 0; i < blocks.Count; i++)
                Regions.Add(new LeafRegion(blocks[i]));
            edges = new ArrayOf<Transition>();

            ArrayOf<ArrayOfBlock> loops = DepthFirstSpanningTree(blocks);
        }

        protected ArrayOf<ArrayOfBlock> DepthFirstSpanningTree(ArrayOfBlock blocks)
        {
            int c = blocks.Count;
            ArrayOf<ArrayOfBlock> loops = new ArrayOf<ArrayOfBlock>();

            transitions = new ArrayOf<Transition>[c];
            loops = new ArrayOf<ArrayOfBlock>();

            for (int i = 0; i < blocks.Count; i++)
                transitions[i] = new ArrayOf<Transition>();
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

            return loops;
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

        protected BitSet[] Dominators(ArrayOfBlock blocks)
        {
            BitSet[] IN = new BitSet[blocks.Count];
            BitSet[] OUT = new BitSet[blocks.Count];
            Set universe = new Set(blocks);

            OUT[0] = new BitSet(universe);
            IN[0] = new BitSet(universe);
            OUT[0].SetToZeros();
            OUT[0][0] = true;
            for (int bk = 1; bk < blocks.Count; bk++)
            {
                OUT[bk] = new BitSet(universe);
                IN[bk] = new BitSet(universe);
                OUT[bk].SetToOnes();
            }

            bool done = false;

            while (!done)
            {
                done = true;

                for (int bk = 1; bk < blocks.Count; bk++)
                {
                    IN[bk].SetToOnes();
                    foreach (Block pred in blocks[bk].Predecessor)
                        IN[bk] = IN[bk] * OUT[pred.Id];
                    string str1 = IN[bk].ToBinary();

                    BitSet old = OUT[bk];
                    for (int i = 0; i < universe.Count; i++)
                        OUT[bk][i] = IN[bk][i];
                    OUT[bk][bk] = true;
                    done = done && (OUT[bk] == old);
                }
            }

            return OUT;
        }

        private void Search(Block blk, ref int c)
        {
            blk.Visited = true;
            foreach (Block succ in blk.Sucessor)
            {
                if (succ.Visited == false)
                {
                    blk.childs.Add(succ);
                    Search(succ, ref c);
                }
            }
            blk.dfn = c;
            c--;
        }

        public void Search(ArrayOfBlock blocks)
        {
            int c = blocks.Count;
            Search(blocks[0], ref c);
        }
    }

    public class Region
    {
        protected Region()
        {
            // Nothing more todo
        }
    }

    public class LeafRegion : Region
    {
        private Block block;

        public LeafRegion(Block block)
        {
            this.block = block;
        }
    }

    public class BodyRegion : Region 
    {
        private ArrayOf<Region> regions;
        private ArrayOf<Transition> edges;

        public BodyRegion(ArrayOf<Region> regions)
        {
            this.regions = regions;
        }
    }

    public class LoopRegion : Region
    {
        private BodyRegion body;
        private Edge edge;

        public LoopRegion(BodyRegion body)
        {
            this.body = body;
        }
    }
}
