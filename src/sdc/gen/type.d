/**
 * Copyright 2010 Bernard Helyer
 * This file is part of SDC. SDC is licensed under the GPL.
 * See LICENCE or sdc.d for more details.
 */
module sdc.gen.type;

import std.string;

import llvm.c.Core;

import sdc.compilererror;
import sdc.location;
import ast = sdc.ast.all;
import sdc.gen.sdcmodule;
import sdc.gen.value;


enum DType
{
    None,
    Bool,
    Int,
    Complex,
    Function,
    Struct,
}

pure bool isComplexDType(DType dtype)
{
    return dtype >= DType.Complex;
}

abstract class Type
{
    DType dtype;
    
    this(Module mod)
    {
        mModule = mod;
    }
    
    LLVMTypeRef llvmType()
    {
        return mType;
    }
    
    /// An opEquals appropriate for simple types.
    override bool opEquals(Object o)
    {
        auto asType = cast(Type) o;
        if (!asType) return false;
        
        return this.mType == asType.mType;
    }
    
    Value getValue(Location location);
    
    protected Module mModule;
    protected LLVMTypeRef mType;
}

class BoolType : Type
{
    this(Module mod)
    {
        super(mod);
        dtype = DType.Bool;
        mType = LLVMInt1TypeInContext(mod.context);
    }
    
    override Value getValue(Location location) { return new BoolValue(mModule, location); }
}

class IntType : Type
{
    this(Module mod)
    {
        super(mod);
        dtype = DType.Int;
        mType = LLVMInt32TypeInContext(mod.context);
    }
    
    override Value getValue(Location location) { return new IntValue(mModule, location); }
}

class FunctionType : Type
{
    Type returnType;
    Type[] argumentTypes;
    
    this(Module mod, ast.FunctionDeclaration funcDecl)
    {
        super(mod);
        dtype = DType.Function;
        mFunctionDeclaration = funcDecl;
    }
    
    void declare()
    {
        returnType = astTypeToBackendType(mFunctionDeclaration.retval, mModule);
        LLVMTypeRef[] params;
        foreach (param; mFunctionDeclaration.parameters) {
            auto type = astTypeToBackendType(param.type, mModule);
            argumentTypes ~= type;
            params ~= type.llvmType;
        }
        mType = LLVMFunctionType(returnType.llvmType, params.ptr, params.length, false);
    }
    
    override Value getValue(Location location) { return null; }

    protected ast.FunctionDeclaration mFunctionDeclaration;
}

class StructType : Type
{
    this(Module mod)
    {
        super(mod);
        dtype = DType.Struct;
    }
    
    void declare()
    {
        LLVMTypeRef[] types;
        foreach (member; members) {
            types ~= member.llvmType;
        }
        mType = LLVMStructTypeInContext(mModule.context, types.ptr, types.length, false);
    }
    
    override Value getValue(Location location)
    {
        return new StructValue(mModule, location, this);
    }
    
    void addMemberVar(string id, Type t)
    {
        memberPositions[id] = members.length;
        members ~= t;
    }
    
    Type[] members;
    int[string] memberPositions;
}

unittest
{
    auto mod = new Module("unittest_module");
    auto a = new IntType(mod);
    auto b = new IntType(mod);
    assert(a !is b);
    assert(a == b);
    auto c = new BoolType(mod);
    assert(a != c);
    mod.dispose();
}
