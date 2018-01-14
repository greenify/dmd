/**
 * Documentation:  https://dlang.org/phobos/dmd_visitor_stoppable.html
 * Coverage:    https://codecov.io/gh/dlang/dmd/src/master/src/dmd/visitor/stoppable.d
 */
module dmd.visitor.stoppable;

import dmd.visitor.semantic;

extern (C++) class StoppableVisitor : SemanticVisitor
{
    alias visit = SemanticVisitor.visit;
public:
    bool stop;

    final extern (D) this()
    {
    }
}