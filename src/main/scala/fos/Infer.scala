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

  def inT(s: TypeVar, t: Type): Boolean = t match {
    case tpe@TypeVar(_) => tpe == s
    case FunType(t1, t2) => inT(s, t1) || inT(s, t2)
    case _ => false
  }

  def subst(x: TypeVar, t: Type, f: Type): Type = f match {
    case tpe@TypeVar(_) if tpe == x => t
    case FunType(tp1, tp2) => {
      val tr1 = if(tp1 == x) subst(x, t, tp1) else tp1
      val tr2 = if(tp2 == x) subst(x, t, tp2) else tp2
      FunType(tr1, tr2)
    }
    case s => s
  }

  def unify(c: List[Constraint]): Type => Type = c match {
    case x :: xs => {
      // println(x._1 + " = " + x._2)
      x match {
        case (s, t) if s == t => {
          unify(xs)
        }
        case (s@TypeVar(_), t) => {
          if(!inT(s, t)) {
            val sub = unify(xs.map( p => (subst(s, t, p._1), subst(s, t, p._2)) ))


            def self(tpe: Type): Type = {
              // println("resolving: "+tpe+" in augmentation ("+s+" = "+t+")")
              tpe match {
                case tpe1 if tpe1 == s => sub(t)
                case FunType(tpe1, tpe2) => FunType(self(tpe1), self(tpe2))
                case _ => sub(tpe)
              }
            }
            self
          }
          else
            throw new TypeError("Unification error, s in t")
        }
        case (s, t@TypeVar(_)) => {
          if (!inT(t, s)) {
            val sub = unify(xs.map(p => (subst(t, s, p._1), subst(t, s, p._2))))

            def self(tpe: Type): Type = {
              // println("resolving: "+tpe+" in augmentation ("+s+" = "+t+")")
              tpe match {
                case tpe1 if tpe1 == t => sub(s)
                case FunType(tpe1, tpe2) => FunType(self(tpe1), self(tpe2))
                case _ => sub(tpe)
              }
            }
            self
          }
          else
            throw new TypeError("Unification error, t in s")
        }
        case (s@FunType(s1, s2), t@FunType(t1, t2)) => {
          val sub = unify( (s1, t1) :: (s2, t2) :: xs)

          (tpe: Type) => {
            // println("resolving: "+tpe+" in augmentation ("+s+" = "+t+")")
            tpe match {
              case FunType(tpe1, tpe2) => FunType(sub(tpe1), sub(tpe2))
              case _ => sub(tpe)
            }
          }

        }
        case _ => throw new TypeError("Cannot satisfy constraint"+x)
      }
    }
    case Nil => (t: Type) => {
      // println("resolving: "+t+" in base case")
      def self(tpe: Type): Type = tpe match {
        case NatType => tpe
        case BoolType => tpe
        case FunType(tp1, tp2) => FunType(self(tp1), self(tp2))
        case _ => throw new TypeError("Sorry bro, don't know about "+tpe)
      }
      self(t)
    }
  }
}
