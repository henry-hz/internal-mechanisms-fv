datatype Expr = Const(nat)
              | Var(string)
              | Node(op: Op, args: List<Expr>)

datatype Op = Add | Mul

datatype List<T> = Nil | Cons(head: T, tail: List<T>)


function AST_Example(): Expr {
  // 10 * (x + 7 * y)
  Node(Mul,
    Cons(Const(10),
    Cons(Node(Add,
      Cons(Var("x"),
      Cons(Node(Mul,
        Cons(Const(7),
        Cons(Var("y"),
        Nil))),
      Nil))),
    Nil)))
}

function Eval(e: Expr, env: map<string, nat>): nat {
  match e
  case Const(c) => c
  case Var(s) => if s in env.Keys then env[s] else 0
  case Node(op, args) => EvalList(args, op, env)
}

function EvalList(args: List<Expr>, op: Op,
                  env: map<string, nat>): nat
{
  match args
  case Nil =>
    (match op case Add => 0 case Mul => 1)
  case Cons(e, tail) =>
    var v0, v1 := Eval(e, env), EvalList(tail, op, env);
    match op
    case Add => v0 + v1
    case Mul => v0 * v1
}
