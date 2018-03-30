// https://issues.dlang.org/show_bug.cgi?id=18136
void main()
{
    import std.regex;
    import std.algorithm : joiner, map;
    string[] messages;

    auto matchToRefs(M)(M m)
    {
        return m.captures[0].splitter(regex(`foo`));
    }

    auto issueRE = regex("foo");
    messages.map!(
        m => m.matchAll(issueRE)
              .map!matchToRefs
    ).joiner;
}
