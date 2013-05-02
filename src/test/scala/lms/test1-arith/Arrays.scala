package scala.lms
package test1

import ops._

import java.io.PrintWriter


trait Arrays extends Base {

  class ArrayOps[T:TypeRep](x: Rep[Array[T]]) {
    def apply(i: Int) = arrayApply(x, i)
  }
  implicit def array2arrayOps[T:TypeRep](x: Rep[Array[T]]) = new ArrayOps(x)

  def arrayApply[T:TypeRep](x: Rep[Array[T]], i:Int): Rep[T]
  //def arrayUpdate(x: Rep[Double]): Rep[Unit]
  def makeArray[T:TypeRep](x: List[Rep[T]]): Rep[Array[T]]
}

trait ArraysExp extends Arrays with BaseExp {
  implicit def arrayTypeRep[T](implicit t: TypeRep[T]): TypeRep[Array[T]] = {
    implicit val mf = t.mf
    typeRep[Array[T]]
  }

  case class ArrayApply[T:TypeRep](x:Rep[Array[T]], i:Int) extends Def[T]
  //case class ArrayUpdate[T](x:Rep[Array[T]], i:Int) extends Def[T]
  case class MakeArray[T:TypeRep](x:List[Rep[T]]) extends Def[Array[T]]

  def arrayApply[T:TypeRep](x: Rep[Array[T]], i:Int) = ArrayApply(x, i)
  //def arrayUpdate(x: Rep[Double]) = ArrayUpdate(x)
  def makeArray[T:TypeRep](x: List[Rep[T]]) = MakeArray(x)
}

trait ScalaGenArrays extends ScalaGenBase {
  val IR: ArraysExp
  import IR._

  override def emitNode(sym: Sym[Any], rhs: Def[Any]) = rhs match {
    case ArrayApply(x,i) =>  emitValDef(sym, "" + quote(x) + ".apply(" + i + ")")
    case MakeArray(x) =>  emitValDef(sym, "Array(" + x.map(quote).mkString(",") + ")")
    case _ => super.emitNode(sym, rhs)
  }
}