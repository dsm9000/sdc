/**
 * Copyright 2010-2011 Bernard Helyer.
 * Copyright 2010 Jakob Ovrum.
 * This file is part of SDC. SDC is licensed under the GPL.
 * See LICENCE or sdc.d for more details.
 */ 
module sdc.tokenstream;

import std.stdio;
import std.string;

import sdc.source;
import sdc.compilererror;
public import sdc.token;


class TokenStream
{
    Source source;
    string filename;
    
    this(Source source)
    {
        filename = source.location.filename;
        this.source = source;
        auto start = new Token();
        start.type = TokenType.Begin;
        start.value = "START";
        mTokens ~= start;
    }
    
    this()
    {
    }
    
    void addToken(Token token)
    {
        mTokens ~= token;
        token.location.length = token.value.length;
    }
    
    Token lastAdded() @property
    {
        return mTokens[$ - 1];
    }
    
    Token getToken()
    {
        auto retval = mTokens[mIndex];
        if (mIndex < mTokens.length - 1) {
            mIndex++;
        }
        return retval;
    }
    
    Token peek() @property
    {
        return mTokens[mIndex];
    }
    
    Token previous() @property
    {
        return mTokens[mIndex - 1];
    }
    
    Token lookahead(size_t n)
    {
        if (n == 0) {
            return peek();
        }
        auto index = mIndex + n;
        if (index >= mTokens.length) {
            auto token = new Token();
            token.type = TokenType.End;
            token.value = "EOF";
            token.location = lastAdded.location;
            return token;
        }
        
        return mTokens[index];
    }
    
    Token lookbehind(size_t n)
    {
        return mTokens[mIndex - n];
    }
    
    void printTo(File file)
    {
        foreach (t; mTokens) {
            file.writefln("%s (%s @ %s)", t.value, tokenToString[t.type], t.location);
        }
    }
    
    Token[] mTokens;
    size_t mIndex;
}
