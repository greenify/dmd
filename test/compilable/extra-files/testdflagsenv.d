/+dub.sdl:
+/
void main(){
    import std.stdio;
    version(Foo)
    {
        "foo".writeln;
    }
    else
    {
        "bar".writeln;
    }
}
