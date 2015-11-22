package fos

import java.lang.reflect.Array

object Infer {
  case class TypeScheme(params: List[TypeVar], tp: Type)
  type Env = List[(String, TypeScheme)]
  type Constraint = (Type /* X */, Type /* tpe */) // Constraint: "X=tpe"

  case class TypeError(msg: String) extends Exception(msg)


  object getFreshTypeVar {
    val counter = Stream.from(1).iterator
    def apply (x: String) = x+"@T"+counter.next
    override def toString = throw new UnsupportedOperationException
  }

  object getFreshVar {
    val counter = Stream.from(1).iterator
    def apply (x: String) = x+"_"+counter.next
    override def toString = throw new UnsupportedOperationException
  }

  // Substitutes Var(x) by Var(y) in term t
  def substVar(x: String, y: String, t: Term): Term = t match {
    case Pred(t1) => Pred(substVar(x, y, t1))
    case Succ(t1) => Succ(substVar(x, y, t1))
    case IsZero(t1) => IsZero(substVar(x, y, t1))
    case If(t1, t2, t3) => If(substVar(x, y, t1), substVar(x, y, t2), substVar(x, y, t3))
    case Var(x1) if x1 == x => Var(y)
    case Abs(x1, tp, t1) if x1 != x => Abs(x1, tp, substVar(x, y, t1))
    case App(t1, t2) => App(substVar(x, y, t1), substVar(x, y, t2))
    case _ => t
  }

  def instanciate(scheme: TypeScheme): Type = scheme.params match {
    case x :: xs =>
      val fresh = getFreshTypeVar(x.name)
      instanciate(TypeScheme(xs, substType(x, TypeVar(fresh), scheme.tp)))
    case Nil => scheme.tp
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
      (myT.tp, Nil)
    }
    case Abs(x, _@EmptyTypeTree(), t1) => {
      // pessimistically rename all bound variables to avoid name collisions
      val freshVar = getFreshVar(x)
      val freshType = TypeVar(getFreshTypeVar(freshVar))
      val scheme = TypeScheme(freshType :: Nil, freshType)
      val (myT2, myC) = collect((freshVar, scheme) :: env, substVar(x, freshVar, t1))
      (FunType(freshType, myT2), myC)
    }
    case Abs(x, tp, t1) => {
      val freshVar = getFreshVar(x)
      val scheme = TypeScheme(Nil, tp.tpe)
      val (myT2, myC) = collect((freshVar, scheme) :: env, substVar(x, freshVar, t1))
      (FunType(tp.tpe, myT2), myC)
    }
    case App(t1, t2) => {
      val (myT1, myC1) = collect(env, t1)
      val (myT2, myC2) = collect(env, t2)
      val freshType = TypeVar(getFreshTypeVar("fn_app"))
      (freshType, (myT1, FunType(myT2, freshType)) :: myC1 ::: myC2)
    }
    case Let(x, tp, v, t) => {
      collect(env, App(Abs(x, tp, t), v))
    }
  }

  def inT(s: TypeVar, t: Type): Boolean = t match {
    case tpe@TypeVar(_) => tpe == s
    case FunType(t1, t2) => inT(s, t1) || inT(s, t2)
    case _ => false
  }

  /* Substitutes x by t in f */
  def substType(x: TypeVar, t: Type, f: Type): Type = f match {
    case tpe@TypeVar(_) if tpe == x => t
    case FunType(tp1, tp2) => {
      val tr1 = if(tp1 == x) substType(x, t, tp1) else tp1
      val tr2 = if(tp2 == x) substType(x, t, tp2) else tp2
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
            val sub = unify(xs.map( p => (substType(s, t, p._1), substType(s, t, p._2)) ))


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
            val sub = unify(xs.map(p => (substType(t, s, p._1), substType(t, s, p._2))))

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
        case _ => throw new TypeError("Cannot satisfy constraint "+x._1+" = "+x._2)
      }
    }
    case Nil => (t: Type) => {
      // println("resolving: "+t+" in base case")
      def self(tpe: Type): Type = tpe match {
        case NatType => tpe
        case BoolType => tpe
        case FunType(tp1, tp2) => FunType(self(tp1), self(tp2))
        case _ => throw new TypeError("No type found for type variable "+tpe)
      }
      self(t)
    }
  }
}
