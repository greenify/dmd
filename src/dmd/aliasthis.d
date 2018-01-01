/**
 * Compiler implementation of the
 * $(LINK2 http://www.dlang.org, D programming language).
 *
 * Copyright:   Copyright (c) 1999-2017 by The D Language Foundation, All Rights Reserved
 * Authors:     $(LINK2 http://www.digitalmars.com, Walter Bright)
 * License:     $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 * Source:      $(LINK2 https://github.com/dlang/dmd/blob/master/src/dmd/aliasthis.d, _aliasthis.d)
 */

module dmd.aliasthis;

// Online documentation: https://dlang.org/phobos/dmd_aliasthis.html

import core.stdc.stdio;
import dmd.aggregate;
import dmd.arraytypes;
import dmd.astbase;
import dmd.dscope;
import dmd.dsymbol;
import dmd.errors;
import dmd.expression;
import dmd.expressionsem;
import dmd.func : resolveFuncCall;
import dmd.globals;
import dmd.identifier;
import dmd.mtype;
import dmd.opover;
import dmd.root.outbuffer;
import dmd.root.stringtable;
import dmd.tokens;
import dmd.visitor;

/***********************************************************
 * alias ident this;
 */
extern (C++) final class AliasThis : Dsymbol
{
    Identifier ident;

    extern (D) this(Loc loc, Identifier ident)
    {
        super(null);    // it's anonymous (no identifier)
        this.loc = loc;
        this.ident = ident;
    }

    override Dsymbol syntaxCopy(Dsymbol s)
    {
        assert(!s);
        return new AliasThis(loc, ident);
    }

    void semantic(Scope* sc)
    {
        Dsymbol p = sc.parent.pastMixin();
        AggregateDeclaration ad = p.isAggregateDeclaration();
        if (!ad)
        {
            error(loc, "alias this can only be a member of aggregate, not %s %s", p.kind(), p.toChars());
            return;
        }
        assert(ad.members);
        Dsymbol s = ad.search(loc, ident);
        if (!s)
        {
            s = sc.search(loc, ident, null);
            if (s)
                error(loc, "%s is not a member of %s", s.toChars(), ad.toChars());
            else
                error(loc, "undefined identifier %s", ident.toChars());
            return;
        }
        auto td = s.isVarDeclaration() ? s.isVarDeclaration().toAlias().isTupleDeclaration() : null;
        if (ad.aliasThisSymbols.dim > 0 && td && !(ad.aliasThisSymbols)[0].equals(td))
        {
            error(loc, "there can be only one tuple alias this", ident.toChars());
        }
        else if (ad.aliasThisSymbols.dim > 0 && !td)
        {
            if (ad.aliasThisSymbols[0].isVarDeclaration() && ad.aliasThisSymbols[0].isVarDeclaration().toAlias().isTupleDeclaration())
            {
                error(loc, "there can be only one tuple alias this", ident.toChars());
            }
        }
        if (ad.type.ty == Tstruct && (cast(TypeStruct)ad.type).sym != ad)
        {
            AggregateDeclaration ad2 = (cast(TypeStruct)ad.type).sym;
            assert(ad2.type == Type.terror);
            // TODO:
            //ad.aliasThisSymbols = ad2.aliasThisSymbols;
            return;
        }
        /* disable the alias this conversion so the implicit conversion check
         * doesn't use it.
         */
        // TODO:
        //if (!ad.aliasThisSymbols)
            //ad.aliasThisSymbols = new Dsymbols();
        Dsymbol sx = s;
        if (sx.isAliasDeclaration())
            sx = sx.toAlias();
        auto d = sx.isDeclaration();
        if (d && !d.isTupleDeclaration())
        {
            Type t = d.type;
            assert(t);
            if (d.isFuncDeclaration())
            {
                t = t.nextOf(); //t is return value;
                //t may be NULL, if d is a auto function
            }
            if (t)
            {
                /* disable the alias this conversion so the implicit conversion check
                 * doesn't use it.
                 */
                uint oldatlock = ad.type.aliasthislock;
                ad.type.aliasthislock |= RECtracing;
                bool match = ad.type.implicitConvTo(t) > MATCH.nomatch;
                ad.type.aliasthislock = oldatlock;
                if (match)
                {
                    .error(loc, "alias this is not reachable as %s already converts to %s", ad.toChars(), t.toChars());
                }
                for (size_t i = 0; i < ad.aliasThisSymbols.dim; ++i)
                {
                    Dsymbol sx2 = ad.aliasThisSymbols[i];
                    if (sx2.isAliasDeclaration())
                        sx2 = sx2.toAlias();
                    auto d2 = sx2.isDeclaration();
                    if (d2 && !d2.isTupleDeclaration())
                    {
                        Type t2 = d2.type;
                        assert(t2);
                        if (t2.equals(t))
                        {
                            .error(loc, "alias %s this tries to override another alias this with type %s", ident.toChars(), t2.toChars());
                        }
                    }
                }
            }
        }
        ad.aliasThisSymbols.push(s);
    }

    const(char)* kind()
    {
        return "alias this";
    }

    AliasThis isAliasThis()
    {
        return this;
    }

    override void accept(Visitor v)
    {
        v.visit(this);
    }
}

/**
 * Returns expression for the `num`-th alias this symbol ot `e`.
 */
extern (C++) Expression resolveAliasThis(Scope* sc, Expression e, size_t num)
{
    AggregateDeclaration ad = isAggregate(e.type);
    if (ad && ad.aliasThisSymbols.dim > 0)
    {
        Loc loc = e.loc;
        Type tthis = (e.op == TOKtype ? e.type : null);
        e = new DotIdExp(loc, e, ad.aliasThisSymbols[num].ident);
        //e = e.semantic(sc); // TODO
        if (tthis && ad.aliasThisSymbols[num].needThis())
        {
            if (e.op == TOKvar)
            {
                if (auto f = (cast(VarExp)e).var.isFuncDeclaration())
                {
                    // Bugzilla 13009: Support better match for the overloaded alias this.
                    Type t;
                    bool hasOverloads;
                    f = f.overloadModMatch(loc, tthis, hasOverloads); // TODO
                    if (f && t)
                    {
                        e = new VarExp(loc, f, 0); // use better match
                        e = new CallExp(loc, e);
                        goto L1;
                    }
                }
            }
            /* non-@property function is not called inside typeof(),
             * so resolve it ahead.
             */
            {
                int save = sc.intypeof;
                sc.intypeof = 1; // bypass "need this" error check
                e = resolveProperties(sc, e);
                sc.intypeof = save;
            }
        L1:
            e = new TypeExp(loc, new TypeTypeof(loc, e));
            //e = e.semantic(sc); TODO
        }
        e = resolveProperties(sc, e);
    }
    return e;
}

/**
 * iterateAliasThis resolves alias this subtypes for `e` and applies it to `dg`.
 * dg should return true, if appropriate subtype has been found.
 * Otherwise it should returns 0.
 * Also dg can get context through secong parameter `ctx`, which was passed through
 * fourth argument of iterateAliasThis.  `dg` can return result expression through
 * `outexpr` parameter, and if it is not NULL, it will be pushed to `ret` array.
 * At the first stage iterateAliasThis iterates direct "alias this"-es and pushes non-null
 * `outexpr`-es to `ret`. If `dg` for one of direct "alias this"-es returns true then
 * `iterateAliasThis` breaks at this stage and returns true through return value and
 * returned by `dg` expression array through `ret`.
 * Even if true returned by first `dg` call, remaining direct "alias this"-es will be processed.
 *
 * If neither of the direct aliases did not return true iterateAliasThis
 * is recursive applied to direct aliases and base classes and interfaces.
 * If one of those `iterateAliasThis` calls returns true our `iterateAliasThis` will return true.
 * Otherwise it will return 0.
 *
 * The last argument is needed for internal using and should be NULL in user call.
 * It contains a hash table of visited types and used for avoiding of infinity recursion if
 * processed type has a circular alias this subtyping:
 * class A
 * {
 *      B b;
 *      alias b this;
 * }
 *
 * class B
 * {
 *      C c;
 *      alias c this;
 * }
 *
 * class C
 * {
 *      A a;
 *      alias a this;
 * }
 */
extern (C++) bool iterateAliasThis(Scope* sc, Expression e, IterateAliasThisDg dg,
        void* ctx, ref Expressions ret, bool gagerrors = false, StringTable* directtypes = null)
{
    //printf("iterateAliasThis: %s\n", e->toChars());
    Dsymbols aliasThisSymbols;
    Type baseType = e.type.toBasetype();
    if (baseType.ty == Tstruct)
    {
        TypeStruct ts = cast(TypeStruct)baseType;
        // TODO
        //aliasThisSymbols = ts.sym.aliasThisSymbols;
    }
    else if (baseType.ty == Tclass)
    {
        TypeClass ts = cast(TypeClass)baseType;
        if (ts.sym.aliasThisSymbols.dim > 0)
        {
            // TODO
            //aliasThisSymbols = ts.sym.aliasThisSymbols;
        }
    }
    else
    {
        return false;
    }
    if (!directtypes)
    {
        directtypes = new StringTable();
        directtypes._init();
    }
    import core.stdc.string : strlen;
    StringValue* depth_counter = directtypes.lookup(e.type.deco, strlen(e.type.deco));
    if (!depth_counter)
    {
        void* ptrvalue;
        depth_counter = directtypes.insert(e.type.deco, strlen(e.type.deco), ptrvalue);
        depth_counter.ptrvalue = cast(void*)e;
    }
    else if (depth_counter.ptrvalue)
    {
        return false; //This type has already been visited.
    }
    else
    {
        depth_counter.ptrvalue = cast(void*)e;
    }
    bool r = false;
    for (size_t i = 0; i < aliasThisSymbols.dim; ++i)
    {
        uint olderrors = 0;
        if (gagerrors)
            olderrors = global.startGagging();
        Expression e1 = resolveAliasThis(sc, e, i);
        if (gagerrors && global.endGagging(olderrors))
            continue;
        if (e1.type.ty == Terror)
            continue;
        assert(e1.type.deco);
        Expression e2 = null;
        int success = dg(sc, e1, ctx, e2);
        r = r || success;
        if (e2)
        {
            ret.push(e2);
        }
        if (!success)
        {
            r = iterateAliasThis(sc, e1, dg, ctx, ret, gagerrors, directtypes) || r;
        }
    }
    if (e.type.ty == Tclass)
    {
        auto cd = (cast(TypeClass)e.type).sym;
        assert(cd.baseclasses);
        for (size_t i = 0; i < cd.baseclasses.dim; ++i)
        {
            // TODO
            //auto bd = (*cd.baseclasses)[i].base;
            //Type bt = bd.type;
            //auto e1 = e.castTo(sc, bt);
            //r = iterateAliasThis(sc, e1, dg, ctx, ret, gagerrors, directtypes) || r;
        }
    }
    depth_counter.ptrvalue = null;
    return r;
}

/***
 * Returns (through `ret`) all subtypes of `t`, which can be implied via
 * alias this mechanism.
 * The `islvalues` contains the array of bool values: the one value for a
 * one `ret` value.
 * This value is true if appropriate type from `ret` refers to L-value symbol,
 * otherwise this value if false.
 */
extern (C++) void getAliasThisTypes(Type t, Types* ret, Bools* islvalues = null)
{
    assert(ret);
    size_t a_count = 0;
    AggregateDeclaration ad = isAggregate(t);
    if (ad && ad.aliasThisSymbols.dim > 0)
        a_count = ad.aliasThisSymbols.dim;
    for (size_t i = 0; i < a_count; i++)
    {
        bool islvalue = false;
        Type a = aliasThisOf(t, i, &islvalue);
        if (!a)
            continue;
        bool duplicate = false;
        for (size_t j = 0; j < ret.dim; ++j)
        {
            if ((*ret)[j].equals(a))
            {
                duplicate = true;
                break;
            }
        }
        if (!duplicate)
        {
            ret.push(a);
            if (islvalues)
            {
                islvalues.push(islvalue);
            }
            getAliasThisTypes(a, ret);
        }
    }
    if (auto cd = ad ? ad.isClassDeclaration() : null)
    {
        for (size_t i = 0; i < cd.baseclasses.dim; i++)
        {
            // TODO
            //auto bd = (*cd.baseclasses)[i].base;
            //Type bt = (*cd.baseclasses)[i].type;
            //if (!bt)
                //bt = bd.type;
            //getAliasThisTypes(bt, ret, islvalues);
        }
    }
}

/**
 * Walks over `from` basetype tree and search types,
 * which can be converted (without alias this subtyping) to `to`.
 * If there are many ways to convert `from` to `to`, this function
 * raises an error and prints all those ways.
 * To prevent infinity loop in types with circular subtyping,
 * pattern "check a flag, lock a flag, do work is a flag wasn't locked, return flag back" is used.
 * `root_from`, `fullSymbolName`, `state` and `matchname` are needed for internal
 * using and should be NULL if the initial call.
 * `root_from` contains the initial `from` type and it is needed for correct error
 * message creating.
 * `fullSymbolName` contains the current symbol name like `TypeA.symbolX.symbolY` and needed
 * for the error message creating.
 * `state` contains current state of the lookup: no matches, there is one match,
 * there are many matches: even if we have found two matches and we are know that
 * we will raise the error, we should find remaining matches for the correct error message.
 * `matchname` contains the full name of the found alias this symbol. It is needed,
 * if we will find anothers matches and will need to raise an error.
 **/
extern (C++) MATCH implicitConvToWithAliasThis(Loc loc, Type from, Type to, Type root_from = null, OutBuffer* fullSymbolName = null, int* state = null, OutBuffer* matchname = null)
{
    //printf("implicitConvToWithAliasThis, %s -> %s\n", from->toChars(), to->toChars());
    if (from.aliasthislock & RECtracing)
        return MATCH.nomatch;
    uint oldatlock = from.aliasthislock;
    from.aliasthislock |= RECtracing;
    if (!fullSymbolName)
    {
        fullSymbolName = new OutBuffer();
        fullSymbolName.writestring(from.toChars());
    }
    int st = 0; //0 - no match
    //1 - match
    //2 - many matches
    if (!state)
        state = &st;
    if (!matchname)
    {
        matchname = new OutBuffer();
    }
    if (!root_from)
    {
        root_from = from;
    }
    size_t a_count = 0;
    AggregateDeclaration ad = isAggregate(from);
    if (!ad)
        return MATCH.nomatch;
    AggregateDeclaration err_ad = isAggregate(root_from);
    assert(err_ad);
    if (ad && ad.aliasThisSymbols.dim > 0)
        a_count = ad.aliasThisSymbols.dim;
    MATCH mret = MATCH.nomatch;
    for (size_t i = 0; i < a_count; i++)
    {
        bool islvalue = false;
        Type a = aliasThisOf(from, i, &islvalue);
        if (!a)
            continue;
        uint tatt = a.aliasthislock;
        a.aliasthislock |= RECtracing;
        MATCH m = a.implicitConvTo(to);
        a.aliasthislock = tatt;
        if (m != MATCH.nomatch)
        {
            if (*state == 0)
            {
                // the first match
                *state = 1;
                mret = m;
                matchname.printf("%s.%s", fullSymbolName.peekString(), ad.aliasThisSymbols[i].toChars());
            }
            else if (*state == 1)
            {
                // the second match
                *state = 2;
                err_ad.error(loc, "There are many candidates for cast %s to %s; Candidates:", root_from.toChars(), to.toChars());
                err_ad.error(loc, " => %s", matchname.extractString());
                matchname.printf("%s.%s", fullSymbolName.peekString(), ad.aliasThisSymbols[i].toChars());
                err_ad.error(loc, " => %s", matchname.extractString());
            }
            else
            {
                matchname.printf("%s.%s", fullSymbolName.peekString(), ad.aliasThisSymbols[i].toChars());
                err_ad.error(loc, " => %s", matchname.extractString());
            }
        }
        else if (!(a.aliasthislock & RECtracing))
        {
            OutBuffer next_buff;
            next_buff.printf("%s.%s", fullSymbolName.peekString(), ad.aliasThisSymbols[i].toChars());
            MATCH m2 = implicitConvToWithAliasThis(loc, a, to, root_from, &next_buff, state, matchname);
            if (mret == MATCH.nomatch)
                mret = m2;
        }
    }
    if (auto cd = ad ? ad.isClassDeclaration() : null)
    {
        for (size_t i = 0; i < cd.baseclasses.dim; i++)
        {
            // TODO
            //auto bd = (*cd.baseclasses)[i].base;
            //Type bt = (*cd.baseclasses)[i].type;
            //if (!bt)
                //bt = bd.type;
            //if (!(bt.aliasthislock & RECtracing))
            //{
                //OutBuffer next_buff;
                //next_buff.printf("(cast(%s)%s)", bt.toChars(), fullSymbolName.peekString());
                //MATCH m2 = implicitConvToWithAliasThis(loc, bt, to, root_from, &next_buff, state, matchname);
                //if (mret == MATCH.nomatch)
                    //mret = m2;
            //}
        }
    }
    from.aliasthislock = oldatlock;
    return mret;
}

/**
 * Returns the type of the `idx`-th alias this symbol of the type `t`.
 * If the `islvalue` is not null, `aliasThisOf` sets `*islvalue` to true
 * if alias this symbol may be resolved to a L-value (if it variable of ref-property),
 * otherwise it sets `*islvalue` to false.
 */
extern (C++) Type aliasThisOf(Type t, size_t idx, bool* islvalue = null)
{
    bool dummy;
    if (!islvalue)
        islvalue = &dummy;
    *islvalue = false;
    AggregateDeclaration ad = isAggregate(t);
    if (ad && ad.aliasThisSymbols.dim > idx)
    {
        Dsymbol s = ad.aliasThisSymbols[idx];
        if (s.isAliasDeclaration())
            s = s.toAlias();
        auto d = s.isDeclaration();
        if (d && !d.isTupleDeclaration())
        {
            assert(d.type);
            Type t2 = d.type;
            if (d.isVarDeclaration() && d.needThis())
            {
                t2 = t2.addMod(t.mod);
                *islvalue = true; //Variable is always l-value
            }
            else if (d.isFuncDeclaration())
            {
                auto fd = resolveFuncCall(Loc(), null, d, null, t, null, 1);
                if (fd && fd.errors)
                    return Type.terror;
                if (fd && !fd.type.nextOf() && !fd.functionSemantic())
                    fd = null;
                if (fd)
                {
                    t2 = fd.type.nextOf();
                    if (!t2) // issue 14185
                        return Type.terror;
                    t2 = t2.substWildTo(t.mod == 0 ? MODmutable : t.mod);
                    if ((cast(TypeFunction)fd.type).isref)
                        *islvalue = true;
                }
                else
                    return Type.terror;
            }
            return t2;
        }
        auto ed = s.isEnumDeclaration();
        if (ed)
        {
            Type t2 = ed.type;
            return t2;
        }
        auto td = s.isTemplateDeclaration();
        if (td)
        {
            assert(td._scope);
            auto fd = resolveFuncCall(Loc(), null, td, null, t, null, 1);
            if (fd && fd.errors)
                return Type.terror;
            if (fd && fd.functionSemantic())
            {
                Type t2 = fd.type.nextOf();
                t2 = t2.substWildTo(t.mod == 0 ? MODmutable : t.mod);
                if ((cast(TypeFunction)fd.type).isref)
                    *islvalue = true;
                return t2;
            }
            else
                return Type.terror;
        }
        //printf("%s\n", s->kind());
    }
    return null;
}

extern (C++) bool iterateAliasThis2(F, Exp)(F f, Exp exp, Scope* sc, Expression e, IterateAliasThisDg dg, void* ctx)
{
    if (f.aliasthislock)
        return false;

    Expressions results;
    iterateAliasThis(sc, e, dg, ctx, results);
    if (results.dim == 1)
    {
        *f = results[0];
        return true;
    }
    else if (results.dim > 1)
    {
        exp.error("Unable to unambiguously resolve %s. Candidates:", exp.toChars());
        for (size_t j = 0; j < results.dim; ++j)
        {
            exp.error("%s", results[j].toChars());
        }
        *f  = new ErrorExp();
        return true;
    }
    return false;
}
