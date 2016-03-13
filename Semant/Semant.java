package Semant;
import Translate.Exp;
import Types.Type;

public class Semant {
  Env env;
  public Semant(ErrorMsg.ErrorMsg err) {
    this(new Env(err));
  }
  Semant(Env e) {
    env = e;
  }

  public void transProg(Absyn.Exp exp) {
    transExp(exp);
  }

  private void error(int pos, String msg) {
    env.errorMsg.error(pos, msg);
  }

  static final Types.VOID   VOID   = new Types.VOID();
  static final Types.INT    INT    = new Types.INT();
  static final Types.STRING STRING = new Types.STRING();
  static final Types.NIL    NIL    = new Types.NIL();

  private Exp checkInt(ExpTy et, int pos) {
    if (!INT.coerceTo(et.ty))
      error(pos, "integer required");
    return et.exp;
  }

  private Exp checkComparable(ExpTy et, int pos) {
    if(!(INT.coerceTo(et.ty) || STRING.coerceTo(et.ty)))
      error(pos, "integer or string required");
    return et.exp;
  }

  private Exp checkEquable(ExpTy et, int pos) {
    //need to avoid making a record/array
    Type type = et.ty.actual();
    if(!(type instanceof Types.INT || type instanceof Types.STRING || type instanceof Types.RECORD || type instanceof Types.ARRAY))
      error(pos, "integer, string, record, or array required");
    return et.exp;
  }
  
  private void checkIdentical(ExpTy first, ExpTy second, int pos) {
    if(!first.ty.actual().coerceTo(second.ty.actual()))
      error(pos, "incompatible operands to inequality operator");
  }
  
  //same thing as above method, but different error message
  private void checkIdenticalE(ExpTy first, ExpTy second, int pos) {
      if(!first.ty.actual().coerceTo(second.ty.actual()))
      error(pos, "incompatible operands to equality operator");
  }

  ExpTy transExp(Absyn.Exp e) {
    ExpTy result;

    if (e == null)
      return new ExpTy(null, VOID);
    else if (e instanceof Absyn.OpExp)
      result = transExp((Absyn.OpExp)e);
    else if (e instanceof Absyn.LetExp)
      result = transExp((Absyn.LetExp)e);
    else if (e instanceof Absyn.IfExp)
      result = transExp((Absyn.IfExp)e);
    else if (e instanceof Absyn.IntExp)
      result = new ExpTy(null, INT);
    else if (e instanceof Absyn.StringExp)
      result = new ExpTy(null, STRING);
    else if (e instanceof Absyn.NilExp)
      result = new ExpTy(null, NIL);
    else if (e instanceof Absyn.ArrayExp)
      result = transExp((Absyn.ArrayExp)e);
    else if (e instanceof Absyn.VarExp)
      result = transExp((Absyn.VarExp)e);
    else if (e instanceof Absyn.RecordExp)
      result = transExp((Absyn.RecordExp)e);
    else if (e instanceof Absyn.SeqExp)
      result = transExp((Absyn.SeqExp)e);
    else if (e instanceof Absyn.AssignExp)
      result = transExp((Absyn.AssignExp)e);
    else if (e instanceof Absyn.CallExp)
      result = transExp((Absyn.CallExp)e);
    else if (e instanceof Absyn.WhileExp)
      result = transExp((Absyn.WhileExp)e);
    else if (e instanceof Absyn.ForExp)
      result = transExp((Absyn.ForExp)e);
    else throw new Error("Failed for "+e.getClass().getName());
    e.type = result.ty;
    return result;
  }
  
  ExpTy transExp(Absyn.ForExp e) {
    //TODO: figure out how to detect for iterator assignment
    ExpTy init = transExp(e.var.init);
    ExpTy hi = transExp(e.hi);
    //both must be integers
    if(!init.ty.coerceTo(INT))
      error(e.var.pos, "integer required");
    if(!hi.ty.coerceTo(INT))
      error(e.hi.pos, "integer required");
    //begin scope in which iterator is defined
    env.venv.beginScope();
    //set up the variable in that scope
    transDec(e.var);
    //traverse the body
    ExpTy body = transExp(e.body);
    //result must be void
    if(!body.ty.coerceTo(VOID))
      error(e.body.pos, "body must be void type");
    return new ExpTy(null,VOID);
  }
  
  ExpTy transExp(Absyn.WhileExp e) {
    ExpTy test = transExp(e.test);
    if(!test.ty.coerceTo(INT)) {
      error(e.pos, "test must be int type");
      return null;
    }
    ExpTy body = transExp(e.body);
    if(!body.ty.coerceTo(VOID))
      error(e.body.pos, "result type mismatch");
    return new ExpTy(null, VOID);
  }
  
  ExpTy transExp(Absyn.CallExp e) {
    //TODO: typecheck everything
    FunEntry function = (FunEntry)env.venv.get(e.func);
    //If the function isn't known, we've got a problem
    if(function==null) {
        error(e.pos, "undeclared function: "+e.func);
        return new ExpTy(null, VOID);
    }
    //Traverse callExp's parameters, typecheck them against the function's parameters
    Absyn.ExpList callList = e.args;
    Types.RECORD paramList = function.formals;
    while(callList!=null && paramList!=null) {
      ExpTy callType = transExp(callList.head);
      Types.NAME paramType = (Types.NAME)paramList.fieldType;
      if(!callType.ty.actual().coerceTo(paramType.actual()))
          error(callList.head.pos, "argument type mismatch");
      paramList = paramList.tail;
      callList = callList.tail;
    }
    if(paramList!=null)
      error(e.pos, "missing argument for "+paramList.fieldName);
    if(callList!=null)
      error(callList.head.pos, "too many arguments");
    return new ExpTy(null, function.result);
  }

  ExpTy transExp(Absyn.AssignExp e) {
    ExpTy rValue = transExp(e.exp);
    ExpTy lValue = transVar(e.var);
    if(!rValue.ty.coerceTo(lValue.ty))
      error(e.pos, "assignment type mismatch");
    return new ExpTy(null, VOID);
  }
  
  ExpTy transExp(Absyn.RecordExp e) {
    Types.NAME lookup = (Types.NAME)env.tenv.get(e.typ);
    if(lookup==null) {
        error(e.pos, "undeclared type: "+e.typ);
        return new ExpTy(null, VOID);
    }
    //transexp through all the initializations of the record
    transField(e.fields);
    return new ExpTy(null, lookup);
  }
  
  //recursively visit nodes in list
  //TODO: actually typecheck
  void transField(Absyn.FieldExpList fe) {
      if(fe==null) return;
      transExp(fe.init);
      transField(fe.tail);
  }
  
  ExpTy transExp(Absyn.SeqExp e) {
    //if this is an empty seqexp, return void type
    if(e.list == null)
      return new ExpTy(null,VOID);
    //returns the type of the last expression in the list
    return transExpList(e.list);
  }
  
  ExpTy transExpList(Absyn.ExpList el) {
    ExpTy headType = transExp(el.head);
    if(el.tail==null) 
      return headType;
    return transExpList(el.tail);
  }
  
  ExpTy transExp(Absyn.ArrayExp e) {
    //extract and typecheck the array information
    Types.NAME type = (Types.NAME)env.tenv.get(e.typ);
    ExpTy size = transExp(e.size);
    ExpTy init = transExp(e.init);
    if(!(type.actual() instanceof Types.ARRAY))
        error(e.pos, "not an array");
    else {
        Types.ARRAY array = (Types.ARRAY)type.actual();
        if(!array.element.coerceTo(init.ty))
            error(e.init.pos, "element type mismatch");
    }
    return new ExpTy(null, type);
  }

  ExpTy transExp(Absyn.VarExp e) {
    //probably needs more stuff here...?
    return transVar(e.var);
  }
  
  //uh i guess time to add all these in
  ExpTy transVar(Absyn.Var v) {
    if(v instanceof Absyn.SimpleVar)
      return transVar((Absyn.SimpleVar)v);
    if(v instanceof Absyn.FieldVar)
      return transVar((Absyn.FieldVar)v);
    if(v instanceof Absyn.SubscriptVar)
      return transVar((Absyn.SubscriptVar)v);
    else throw new Error("Failed for "+v.getClass().getName());
  }
  
  ExpTy transVar(Absyn.SubscriptVar v) {
    ExpTy var = transVar(v.var);
    ExpTy index = transExp(v.index);
    if(!(var.ty.actual() instanceof Types.ARRAY)) {
        error(v.pos, "array required");
        return new ExpTy(null, VOID);
    }
    if(!index.ty.actual().coerceTo(INT))
        error(v.pos, "index not integer");
    return new ExpTy(null, ((Types.ARRAY)var.ty.actual()).element);
  }
  
  ExpTy transVar(Absyn.FieldVar v) {
    //must be record type
    Types.Type var = transVar(v.var).ty.actual();
    if(!(var instanceof Types.RECORD)) {
        error(v.var.pos, "record required");
        return new ExpTy(null, VOID);
    }
    Symbol.Symbol compare = v.field;
    //find record entry we need
    Types.RECORD it = (Types.RECORD)var;
    while(it!=null) {
        Symbol.Symbol compare2 = it.fieldName;
        if(compare==compare2) {
            //we found it folks
            break;
        }
        it=it.tail;
    }
    if(it==null) {
      error(v.pos, "undeclared field: "+compare);
      return new ExpTy(null, VOID);
    }
    return new ExpTy(null, it.fieldType.actual());
  }
  
  ExpTy transVar(Absyn.SimpleVar v) {
      Entry entry = (Entry)env.venv.get(v.name);
      if(entry==null) {
          error(v.pos, "undeclared variable: "+v.name);
          return new ExpTy(null, VOID);
      }
      return new ExpTy(null, ((VarEntry)entry).ty);
  }
  
  ExpTy transExp(Absyn.IfExp e) {
    ExpTy test = transExp(e.test);
    //check for int
    checkInt(test, e.test.pos);
    //the test is an integer, get type of then clause
    ExpTy then = transExp(e.thenclause);
    //check if we have an else clause
    if(e.elseclause != null) {
      ExpTy els = transExp(e.elseclause);
      //need to be same type
      if(!(els.ty.coerceTo(then.ty)))
        error(e.pos, "result type mismatch");
      return els;
    }
    if(then.ty!=VOID) {
      error(e.pos, "result type mismatch");
      //returning proper type
      return new ExpTy(null, VOID);
    }
    return then;
  }

  ExpTy transExp(Absyn.OpExp e) {
    ExpTy left = transExp(e.left);
    ExpTy right = transExp(e.right);

    switch (e.oper) {
    case Absyn.OpExp.PLUS:
      checkInt(left, e.left.pos);
      checkInt(right, e.right.pos);
      return new ExpTy(null, INT);
    case Absyn.OpExp.MINUS:
      checkInt(left, e.left.pos);
      checkInt(right, e.right.pos);
      return new ExpTy(null, INT);
    case Absyn.OpExp.MUL:
      checkInt(left, e.left.pos);
      checkInt(right, e.right.pos);
      return new ExpTy(null, INT);
    case Absyn.OpExp.DIV:
      checkInt(left, e.left.pos);
      checkInt(right, e.right.pos);
      return new ExpTy(null, INT);
    case Absyn.OpExp.GT:
    case Absyn.OpExp.LT:
    case Absyn.OpExp.GE:
    case Absyn.OpExp.LE:
      checkComparable(left, e.left.pos);
      checkComparable(right, e.right.pos);
      checkIdentical(left, right, e.pos);
      return new ExpTy(null, INT);
    case Absyn.OpExp.EQ:
    case Absyn.OpExp.NE:
      checkEquable(left, e.left.pos);
      checkEquable(left, e.left.pos);
      checkIdenticalE(left, right, e.pos);
      return new ExpTy(null, INT);
    default:
      throw new Error("unknown operator");
    }
  }

  ExpTy transExp(Absyn.LetExp e) {
    env.venv.beginScope();
    env.tenv.beginScope();
    for (Absyn.DecList d = e.decs; d != null; d = d.tail) {
      transDec(d.head);
    }
    ExpTy body = transExp(e.body);
    env.venv.endScope();
    env.tenv.endScope();
    return new ExpTy(null, body.ty);
  }

  Exp transDec(Absyn.Dec d) {
    if (d instanceof Absyn.VarDec)
      return transDec((Absyn.VarDec)d);
    if (d instanceof Absyn.TypeDec)
      return transDec((Absyn.TypeDec)d);
    if (d instanceof Absyn.FunctionDec)
      return transDec((Absyn.FunctionDec)d);
    throw new Error("Failed for "+d.getClass().getName());
  }
  
  Exp transDec(Absyn.FunctionDec d) {
    //Make an entry for the function, needs parameters and a result
    //TODO: error checking
    Types.RECORD formals = makeRecord(d.params);
    //if return type is non-null, translate it
    Types.Type returnType = VOID;
    if(d.result != null)
        returnType = transTy(d.result);
    d.entry = new FunEntry(formals, returnType);
    env.venv.put(d.name, d.entry);
    //go through the chain of function declarations here, put the names in the environment before parsing the body (for recursion)
    if(d.next!=null)
      transDec(d.next);
    //inside the body, create a new environment
    env.venv.beginScope();
    //add parameters to this scope
    while(formals!=null) {
      env.venv.put(formals.fieldName, new VarEntry(formals.fieldType));
      formals = formals.tail;
    }
    //traverse the function body
    ExpTy resultType = transExp(d.body);
    //I bet .actual() isn't required here...
    if(!returnType.actual().coerceTo(resultType.ty))
      //I guess the error marker should be at the body of the function? w/e
      error(d.body.pos, "result type mismatch");
    //end scope
    env.venv.endScope();
    return null;
  }

  Exp transDec(Absyn.TypeDec d) {
    //Make a NAME for this type
    Types.NAME name = new Types.NAME(d.name);
    //first, define the name in the environment (handles recursive types)
    env.tenv.put(d.name, name);
    d.entry = name;
    //Go through the names of the types in the typedec chain before processing the types (to handle for recursive types)
    if(d.next != null)
      transDec(d.next);
    //typecheck the body, not necessarily a record
    Types.Type bodyType = transTy(d.ty);
    //Bind the name to the type that is declared
    name.bind(bodyType);
    //TODO: ERROR
    return null;
  }

  Types.Type transTy(Absyn.Ty t) {
    //using instanceof, translate param Absyn.Ty into appropriate Types.Type
    if(t instanceof Absyn.RecordTy)
      return transTy((Absyn.RecordTy) t);
    if(t instanceof Absyn.ArrayTy)
      return transTy((Absyn.ArrayTy) t);
    if(t instanceof Absyn.NameTy)
      return transTy((Absyn.NameTy) t);
    throw new Error("Failed for "+t.getClass().getName());
  }
  
  Types.NAME transTy(Absyn.NameTy t) {
      //theoretically should be a name
      Types.NAME type = (Types.NAME)env.tenv.get(t.name);
      //if null, report error
      if(type==null) {
          error(t.pos, "type "+t.name+" is not known");
      }
      return type;
  }

  Types.ARRAY transTy(Absyn.ArrayTy t) {
    //look up the type of the array in the type environment
    Types.Type type = (Types.Type)env.tenv.get(t.typ);
    //if the lookup fails, something bad happened
    if(type == null) {
      error(t.pos, "array type not known");
      return null;
    }
    return new Types.ARRAY(type);
  }

  Types.RECORD transTy(Absyn.RecordTy t) {
    //recursviely make records
    return makeRecord(t.fields);
  }
  
  //helper function to make record type out of fields
  Types.RECORD makeRecord(Absyn.FieldList fl) {
      if(fl==null)
          return null;
      Symbol.Symbol fieldName = fl.name;
      Symbol.Symbol fieldType = fl.typ;
      Types.NAME type = (Types.NAME)env.tenv.get(fieldType);
      if(type==null)
          error(fl.pos, "undeclared type: "+fieldType);
      return new Types.RECORD(fieldName, type, makeRecord(fl.tail));
  }

  Exp transDec(Absyn.VarDec d) {
    ExpTy init = transExp(d.init);
    Types.Type varType = VOID;
    if(d.typ!=null) {
        varType = (Types.NAME)env.tenv.get(d.typ.name);
        if(varType==null) {
          error(d.pos, "unknown type: "+d.typ.name);
          return null;
        }
      //NIL is allowed
      if(!varType.actual().coerceTo(init.ty) && init.ty != NIL) {
        error(d.pos, "assignment type mismatch");
      }
    } else {
      //it didn't declare a type, better just grab the init type...
      varType = init.ty;
    }
    d.entry = new VarEntry(varType);
    env.venv.put(d.name, d.entry);
    return null;
  }
}
