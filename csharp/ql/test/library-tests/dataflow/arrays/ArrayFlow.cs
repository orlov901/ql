using System;
using System.Collections.Generic;

public class A
{
    public void M1()
    {
        var a = new A();
        var @as = new[] { a };
        Sink(@as[0]); // flow
        SinkElem(@as); // flow
        Sink(First(@as)); // flow
    }

    public void M2(A other)
    {
        var a = new A();
        var @as = new[] { other };
        Sink(@as[0]); // no flow
        SinkElem(@as); // no flow
        Sink(First(@as)); // no flow
    }

    public void M3()
    {
        var a = new A();
        var @as = new A[1];
        @as[0] = a;
        Sink(@as[0]); // flow
        SinkElem(@as); // flow
        Sink(First(@as)); // flow
    }

    public void M4(A other)
    {
        var a = new A();
        var @as = new A[1];
        @as[0] = other;
        Sink(@as[0]); // no flow
        SinkElem(@as); // no flow
        Sink(First(@as)); // no flow
    }

    public void M5()
    {
        var a = new A();
        var list = new List<A>();
        list[0] = a;
        Sink(list[0]); // flow
        SinkListElem(list); // flow
        Sink(ListFirst(list)); // flow
    }

    public void M6(A other)
    {
        var list = new List<A>();
        list[0] = other;
        Sink(list[0]); // no flow
        SinkListElem(list); // no flow
        Sink(ListFirst(list)); // no flow
    }

    public void M7()
    {
        var a = new A();
        var list = new List<A>() { a };
        Sink(list[0]); // flow
        SinkListElem(list); // flow
        Sink(ListFirst(list)); // flow
    }

    public void M8(A other)
    {
        var list = new List<A>() { other };
        Sink(list[0]); // no flow
        SinkListElem(list); // no flow
        Sink(ListFirst(list)); // no flow
    }

    public void M9()
    {
        var a = new A();
        var list = new List<A>();
        list.Add(a);
        Sink(list[0]); // flow
        SinkListElem(list); // flow
        Sink(ListFirst(list)); // flow
    }

    public void M10(A other)
    {
        var list = new List<A>();
        list.Add(other);
        Sink(list[0]); // no flow
        SinkListElem(list); // no flow
        Sink(ListFirst(list)); // no flow
    }

    public void M11()
    {
        var a = new A();
        var dict = new Dictionary<int, A>();
        dict[0] = a;
        Sink(dict[0]); // flow (MISSING)
        SinkDictElem(dict); // flow (MISSING)
        Sink(DictFirst(dict)); // flow (MISSING)
    }

    public void M12(A other)
    {
        var dict = new Dictionary<int, A>();
        dict[0] = other;
        Sink(dict[0]); // no flow
        SinkDictElem(dict); // no flow
        Sink(DictFirst(dict)); // no flow
    }

    public void M13()
    {
        var a = new A();
        var dict = new Dictionary<int, A>() { { 0, a } };
        Sink(dict[0]); // flow (MISSING)
        SinkDictElem(dict); // flow (MISSING)
        Sink(DictFirst(dict)); // flow (MISSING)
    }

    public void M14(A other)
    {
        var dict = new Dictionary<int, A>() { { 0, other } };
        Sink(dict[0]); // no flow
        SinkDictElem(dict); // no flow
        Sink(DictFirst(dict)); // no flow
    }

    public static void Sink<T>(T t) { }

    public static void SinkElem<T>(T[] ts) => Sink(ts[0]);

    public static void SinkListElem<T>(IList<T> list) => Sink(list[0]);

    public static void SinkDictElem<T>(IDictionary<int, T> dict) => Sink(dict[0]);

    public static T First<T>(T[] ts) => ts[0];

    public static T ListFirst<T>(IList<T> list) => list[0];

    public static T DictFirst<T>(IDictionary<int, T> dict) => dict[0];
}
