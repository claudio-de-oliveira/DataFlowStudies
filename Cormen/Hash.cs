using System;
using System.Collections;

namespace Cormen
{
    public abstract class KeyedData
    {
        public abstract string Key
        { get; }
    }

    public class HashTable
    {
        #region Chain
        private class Chain
        {
            #region Node
            private class Node
            {
                private KeyedData data;
                private Node next;

                public Node Next
                {
                    get { return next; }
                    set { next = value; }
                }

                public KeyedData Data
                {
                    get { return data; }
                    set { data = value; }
                }
            }
            #endregion

            private Node head;

            public Chain()
            {
                head = null;
            }

            public object GetHead()
            {
                return head;
            }

            public KeyedData GetNext(ref object pos)
            {
                KeyedData data = ((Node)pos).Data;
                pos = ((Node)pos).Next;
                return data;
            }

            public void Add(KeyedData data)
            {
                Node node = new Node();

                node.Data = data;
                node.Next = head;
                head = node;
            }

            public KeyedData Search(string key)
            {
                object pos = GetHead();
                KeyedData data = null;

                while (pos != null)
                {
                    data = GetNext(ref pos);
                    if (data.Key == key)
                        return data;
                }

                return null;
            }

            public KeyedData Remove(string key)
            {
                KeyedData data = null;

                if (head == null)
                    return null;

                if (((Node)head).Data.Key == key)
                {
                    head = ((Node)head).Next;
                }
                else
                {
                    Node current = (Node)head;
                    Node next = current.Next;

                    while (next != null)
                    {
                        if (next.Data.Key == key)
                        {
                            data = next.Data;
                            current.Next = next.Next;
                            return data;
                        }
                        else
                        {
                            current = next;
                            next = next.Next;
                        }
                    }
                }

                return data;
            }

            public override string ToString()
            {
                string str = "";
                for (Node node = head; node != null; node = node.Next)
                    str += node.Data.Key + " ";
                return str;
            }

            public IEnumerator GetEnumerator()
            {
                for (Node node = head; node != null; node = node.Next)
                {
                    yield return node.Data;
                }
            }
        }
        #endregion

        private int m, p, a, b;
        private Chain[] slots;
        private int count;

        protected int HashValue(string key)
        { 
            if (key == "")
                return 0;

            int k = key[0];

            for (int i = 1; i < key.Length; i++)
                k ^= key[i];

            return ((a * k + b) % p) % m;
        }

        private int NextPrime(int m)
        { 
            ArrayList primes = new ArrayList();
            bool isPrime = false;

            for (int num = 3; true; num += 2)
            {
                isPrime = true;

                foreach (int i in primes)
                {
                    if (num % i == 0)
                    {
                        isPrime = false;
                        break;
                    }
                    if (i > Math.Sqrt(num))
                        break;
                }

                if (isPrime)
                {
                    if (num > m)
                        return num;
                    else
                        primes.Add(num);
                }
            }
        }

        public HashTable(int m)
        {
            this.m = m;
            slots = new Chain[m];
            p = NextPrime(256);
            if (m == 0)
            {
                a = b = 0;
            }
            else
            {
                a = 17;
                b = 10;
            }
            count = 0;
        }

        public void Insert(KeyedData data)
        {
            int h = HashValue(data.Key);

            if (slots[h] != null && slots[h].Search(data.Key) != null)
            {
                Console.WriteLine("Key " + data.Key + " already inserted.");
                return;
            }

            if (slots[h] == null)
                slots[h] = new Chain();
            else
                Console.WriteLine("Igual");

            slots[h].Add(data);

            count++;
        }

        public KeyedData Search(string key)
        {
            int h = HashValue(key);

            if (slots[h] == null)
                return null;

            return slots[h].Search(key);
        }

        public KeyedData Remove(string key)
        {
            int h = HashValue(key);

            if (slots[h] == null)
                return null;

            count--;

            return slots[h].Remove(key);
        }

        public override string ToString()
        {
            int i;
            string str = "";

            for (i = 0; i < slots.Length; i++)
            {
                if (slots[i] != null)
                    str += slots[i].ToString() + "\n";
                else
                    str += "\n";
            }

            return str;
        }

        public IEnumerator GetEnumerator()
        {
            for (int i = 0; i < slots.Length; i++)
                if (slots[i] != null)
                    foreach (KeyedData key in slots[i])
                        yield return key;
        }

        public int Count
        {
            get { return count; }
        }
    }

    public class PerfectHash
    {
        #region Chain
        private class Chain
        {
            #region Node
            private class Node
            {
                private KeyedData data;
                private Node next;

                public Node Next
                {
                    get { return next; }
                    set { next = value; }
                }

                public KeyedData Data
                {
                    get { return data; }
                    set { data = value; }
                }
            }
            #endregion

            private Node head;

            public Chain()
            {
                head = null;
            }

            public object GetHead()
            {
                return head;
            }

            public KeyedData GetNext(ref object pos)
            {
                KeyedData data = ((Node)pos).Data;
                pos = ((Node)pos).Next;
                return data;
            }

            public void Add(KeyedData data)
            {
                Node node = new Node();

                node.Data = data;
                node.Next = head;
                head = node;
            }

            public KeyedData Search(string key)
            {
                object pos = GetHead();
                KeyedData data = null;

                while (pos != null)
                {
                    data = GetNext(ref pos);
                    if (data.Key == key)
                        return data;
                }

                return null;
            }

            public KeyedData Remove(string key)
            {
                KeyedData data = null;

                if (head == null)
                    return null;

                if (((Node)head).Data.Key == key)
                {
                    head = ((Node)head).Next;
                }
                else
                {
                    Node current = (Node)head;
                    Node next = current.Next;

                    while (next != null)
                    {
                        if (next.Data.Key == key)
                        {
                            data = next.Data;
                            current.Next = next.Next;
                            return data;
                        }
                        else
                        {
                            current = next;
                            next = next.Next;
                        }
                    }
                }

                return data;
            }

            public override string ToString()
            {
                string str = "";
                for (Node node = head; node != null; node = node.Next)
                    str += node.Data.Key + " ";
                return str;
            }
        }
        #endregion

        private int m, p, a, b;
        private Chain[] slots;

        protected int HashValue(string key)
        { 
            if (key == "")
                return 0;

            int k = key[0];

            for (int i = 1; i < key.Length; i++)
                k ^= key[i];

            return ((a * k + b) % p) % m;
        }

        private int NextPrime(int m)
        { 
            ArrayList primes = new ArrayList();
            bool isPrime = false;

            for (int num = 3; true; num += 2)
            {
                isPrime = true;

                foreach (int i in primes)
                {
                    if (num % i == 0)
                    {
                        isPrime = false;
                        break;
                    }
                    if (i > Math.Sqrt(num))
                        break;
                }

                if (isPrime)
                {
                    if (num > m)
                        return num;
                    else
                        primes.Add(num);
                }
            }
        }

        public PerfectHash(ArrayList keys)
        {
            int i;

            m = keys.Count / 2;

            int[] mCount = new int[m];

            for (i = 0; i < m; i++)
                mCount[i] = 0;

            for (i = 0; i < keys.Count; i++)
                mCount[HashValue((string)keys[i])]++;

            slots = new Chain[m];

            p = NextPrime(m);
            a = 17;
            b = 10;
        }

        private void Insert(KeyedData data)
        {
            int h = HashValue(data.Key);

            if (slots[h] != null && slots[h].Search(data.Key) != null)
            {
                Console.WriteLine("Key " + data.Key + " already inserted.");
                return;
            }

            if (slots[h] == null)
                slots[h] = new Chain();
            else
                Console.WriteLine("Igual");

            slots[h].Add(data);
        }

        public KeyedData Search(string key)
        {
            int h = HashValue(key);

            if (slots[h] == null)
                return null;

            return slots[h].Search(key);
        }

        public override string ToString()
        {
            int i;
            string str = "";

            for (i = 0; i < slots.Length; i++)
            {
                if (slots[i] != null)
                    str += slots[i].ToString() + "\n";
                else
                    str += "\n";
            }

            return str;
        }
    }
}
