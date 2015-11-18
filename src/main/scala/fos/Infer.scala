package fos

object Infer {
  case class TypeScheme(params: List[TypeVar], tp: Type)
  type Env = List[(String, TypeScheme)]
  type Constraint = (Type /* X */, Type /* tpe */) // Constraint: "X=tpe"

  case class TypeError(msg: String) extends Exception(msg)


  object getFreshTypeVar {
    val counter = Stream.from(1).iterator
    def apply () = "T"+counter.next
    override def toString = throw new UnsupportedOperationException
  }


  def collect(env: Env, t: Term): (Type, List[Constraint]) = t match {
    case True() => (BoolType, Nil)
    case False() => (BoolType, Nil)
    case Zero() => (NatType, Nil)
    case Pred(t1) => {
      val (myT, myC) = collect(env, t1)
      (NatType, (myT, NatType) :: myC)
    }
    case Succ(t1) => {
      val (myT, myC) = collect(env, t1)
      (NatType, (myT, NatType) :: myC)
    }
    case IsZero(t1) => {
      val (myT, myC) = collect(env, t1)
      (BoolType, (myT, NatType) :: myC)
    }
    case If(t1, t2, t3) => {
      val (myT1, myC1) = collect(env, t1)
      val (myT2, myC2) = collect(env, t2)
      val (myT3, myC3) = collect(env, t3)
      (myT2, (myT1, BoolType) :: (myT2, myT3) :: myC1 ::: myC2 ::: myC3)
    }
    case Var(x) if env.toMap.contains(x) => {
      val myT = env.toMap.getOrElse(x, throw new RuntimeException("cannot happen"))
      (myT.tp, Nil /* TODO */)
    }
    case Abs(x, _@EmptyTypeTree(), t1) => {
      val freshType = TypeVar(getFreshTypeVar())
      val scheme = TypeScheme(Nil /* TODO */, freshType)
      val (myT2, myC) = collect((x, scheme) :: env, t1)
      (FunType(freshType, myT2), myC)
    }
    case Abs(x, tp, t1) => {
      val scheme = TypeScheme(Nil /* TODO */, tp.tpe)
      val (myT2, myC) = collect((x, scheme) :: env, t1)
      (FunType(tp.tpe, myT2), myC)
    }
    case App(t1, t2) => {
      val (myT1, myC1) = collect(env, t1)
      val (myT2, myC2) = collect(env, t2)
      val freshType = TypeVar(getFreshTypeVar())
      (freshType, (myT1, FunType(myT2, freshType)) :: myC1 ::: myC2)
    }
  }

  def inT(s: String, t: Type): Boolean = t match {
    case TypeVar(x) => x == s
    case FunType(t1, t2) => inT(s, t1) || inT(s, t2)
    case _ => false
  }

  def subst(x: String, t: Type, f: Type) = f match {
    case TypeVar(s) if s == x => t
    case s => s
  }

  def unify(c: List[Constraint]): Type => Type = c match {
    case x :: xs => x match {
      case (s, t) if s == t => unify(xs)
      case (_@TypeVar(x), t) => {
        if(!inT(x, t))
          unify(xs.map( p => (subst(x, t, p._1), subst(x, t, p._2)) ))
        else
          throw new TypeError("Unification error, s in t")
      }
      case (s, _@TypeVar(x)) => {
        if(!inT(x, s))
          unify(xs.map( p => (subst(x, s, p._1), subst(x, s, p._2)) ))
        else
          throw new TypeError("Unification error, s in t")
      }
      case (s@FunType(s1, s2), t@FunType(t1, t2)) => {
        // TODO
      }
    }
    case Nil => ???
  }
}
