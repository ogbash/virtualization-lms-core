package scala.virtualization.lms
package epfl
package test7

import common._
import test1._

import util.OverloadHack
import scala.reflect.SourceContext

import java.io.{PrintWriter,StringWriter,FileOutputStream}

trait MyLoopFusionCore { // copied from LoopFusionOpt: LoopFusionCore trait

  val IR: LoopsFatExp with IfThenElseFatExp
  import IR._  
  
  def unapplySimpleIndex(e: Def[Any]): Option[(Exp[Any], Exp[Int])] = None
  def unapplySimpleDomain(e: Def[Int]): Option[Exp[Any]] = None
  def unapplySimpleCollect(e: Def[Any]): Option[Exp[Any]] = None
  def unapplySimpleCollectIf(e: Def[Any]): Option[(Exp[Any],List[Exp[Boolean]])] = None

  object SimpleIndex {
    def unapply(a: Def[Any]): Option[(Exp[Any], Exp[Int])] = unapplySimpleIndex(a)
  }

  object SimpleDomain {
    def unapply(a: Def[Int]): Option[Exp[Any]] = unapplySimpleDomain(a)
  }

  object SimpleCollect {
    def unapply(a: Def[Any]): Option[Exp[Any]] = unapplySimpleCollect(a)
  }

  object SimpleCollectIf {
    def unapply(a: Def[Any]): Option[(Exp[Any],List[Exp[Boolean]])] = unapplySimpleCollectIf(a)
  }
}

trait MyLoopFusionOpt extends MyLoopFusionCore {
  val IR: LoopsFatExp with IfThenElseFatExp
  import IR._  

}

trait ScalaGenFatArrayLoopsMyFusionOpt extends ScalaGenArrayLoopsFat with ScalaGenIfThenElseFat with MyLoopFusionOpt {
  val IR: ArrayLoopsFatExp with IfThenElseFatExp
  import IR._  
  
  override def unapplySimpleIndex(e: Def[Any]) = e match {
    case ArrayIndex(a, i) => Some((a,i))
    case _ => super.unapplySimpleIndex(e)
  }
  override def unapplySimpleDomain(e: Def[Int]): Option[Exp[Any]] = e match {
    case ArrayLength(a) => Some(a)
    case _ => super.unapplySimpleDomain(e)
  }

  override def unapplySimpleCollect(e: Def[Any]) = e match {
    case ArrayElem(Block(a)) => Some(a) //TODO: block??
    case _ => super.unapplySimpleCollect(e)
}

override def unapplySimpleCollectIf(e: Def[Any]) = e match {
    case ArrayIfElem(c,Block(a)) => Some((a,List(c))) //TODO: block?
    case _ => super.unapplySimpleCollectIf(e)
}

  override def applyAddCondition(e: Def[Any], c: List[Exp[Boolean]]) = e match { //TODO: should c be list or not?
    case ArrayElem(a) if c.length == 1 => ArrayIfElem(c(0),a)
    case ReduceElem(a) if c.length == 1 => ReduceIfElem(c(0),a)
    case _ => super.applyAddCondition(e,c)
  }

}


// trait MyLoops extends Loops with OverloadHack {
//   def loop(shape: Rep[Int])(f: Rep[Int] => Rep[Unit]): Rep[Unit]
// }

// trait MyLoopsExp extends LoopsExp {
//   case class LoopBody(y: Block[Unit]) extends Def[Unit]

//   def loop(shape: Rep[Int])(f: Rep[Int] => Rep[Unit]): Rep[Unit] = {
//     val x = fresh[Int]
//     val y = reifyEffects(f(x))
//     simpleLoop(shape, x, LoopBody(y))
//   }

//   // override def mirrorDef[A:Manifest](e: Def[A], f: Transformer)(implicit pos: SourceContext): Def[A] = e match {
//   //   case LoopBody(b) => e
//   //   case _ => super.mirrorDef(e,f)
//   // }

//   // override def mirror[A:Manifest](e: Def[A], f: Transformer)(implicit pos: SourceContext): Exp[A] = e match {
//   //   case Reflect(LoopBody(b), a, c) => e
//   //   case LoopBody(b) => e
//   //   case _ => super.mirror(e,f)
//   // }

//   override def mirrorFatDef[A:Manifest](e: Def[A], f: Transformer)(implicit pos: SourceContext): Def[A] = e match {
//    case LoopBody(b) => e
//    case _ => super.mirrorFatDef(e,f)
//   }

// }

// trait ScalaGenMyLoops extends ScalaGenLoops {
//   val IR: MyLoopsExp
//   import IR._

//   override def emitNode(sym: Sym[Any], rhs: Def[Any]) = rhs match {
//     case SimpleLoop(s,x,LoopBody(y)) =>  
//       stream.println("val " + quote(sym) + " = for ("+quote(x)+" <- 0 until " + quote(s) + ") {")
//       emitBlock(y)
//       stream.println(quote(getBlockResult(y)))
//       stream.println("}")
//     case _ => super.emitNode(sym, rhs)
//   }
// }

trait MyFusionProg extends Arith with ArrayLoops with Print {
  def test(x: Rep[Int]): Rep[Unit]
}

trait Impl extends MyFusionProg with ArithExp with ArrayLoopsFatExp with PrintExp
    with IfThenElseFatExp with OrderingOpsExp { self =>
  override val verbosity = 1
  val runner = new Runner { val p: self.type = self }
  runner.run()
}

trait Codegen extends ScalaGenFatArrayLoopsMyFusionOpt with ScalaGenArith with ScalaGenPrint with ScalaGenOrderingOps { val IR: Impl }

trait Runner {
  val p: Impl
  def run() = {
    val x = p.fresh[Int]
    val y = p.reifyEffects(p.test(x))

    val codegen = new Codegen { val IR: p.type = p }

    val graph = p.globalDefs
    println("-- full graph")
    graph foreach println

    println("-- before transformation")
    codegen.withStream(new PrintWriter(System.out)) {
      codegen.emitBlock(y)
    }

    val trans = new MyFusionTransformer {
      val IR: p.type = p
    }
    try {
      val z = trans.transformBlock(y)

      println("-- after transformation")
      codegen.withStream(new PrintWriter(System.out)) {
        codegen.emitBlock(z)
      }
      } catch {
        case ex =>
        println("error: " + ex)
      }
      println("-- done")      
    }
  }
  
  trait MyFusionTransformer extends ForwardTransformer /*with BaseLoopsTraversalFat*/ { 
    val IR: Impl
    import IR.{__newVar => _, _}
    
    override def transformStm(stm: Stm): Exp[Any] = stm match {
//      case TP(s,Print(num)) =>
//      println("replacing " + stm)
//      print(apply(num))
//      case TTP(_, _, _) => 
  //      println("MyTransformer caught fat: " + stm)
    //    self_mirror(sym, rhs) //???
        // ?? How to mirror TTP?
        
      case _ => 
        println("MyTransformer sees: " + stm)
        super.transformStm(stm)
    }
  }

  class TestFusion3 extends FileDiffSuite {
    
    val prefix = "test-out/epfl/test7-wip-"
    
  // def testFusion1 = {
  //   withOutFile(prefix+"fusion1") {
  //     new MyFusionProg with ArithExp with MyLoopsExp with PrintExp { self =>
  //       val codegen = new ScalaGenMyLoops with ScalaGenArith with ScalaGenPrint { val IR: self.type = self }
  //       codegen.emitSource(test, "Test", new PrintWriter(System.out))

  //     }
  //   }

  //   println("hello world")
  //   new TestOutput().apply()
  //   println("goodbye world")



  //   assertFileEqualsCheck(prefix+"fusion1")
  // }


  def testFusionTransform = withOutFileChecked(prefix+"transform2") {
    trait Prog extends MyFusionProg with OrderingOps with Impl {
      // def test(x: Rep[Int]) = {
      //   loop(unit(5)) {i => print(i) }
      //   loop(unit(6)) {i => print(i) }
      // }
      def test(x: Rep[Int]) = {
        
        val range = array(100) { i => i }
        
        val odds = arrayIf(range.length) { i => (range.at(i) > 50, range.at(i)) }
        // def filter[T:Manifest](x: Rep[Array[T]])(p: Rep[T] => Rep[Boolean]) = 
        //   arrayIf(x.length) { i => (p(x.at(i)), x.at(i)) }
        // val odds = filter(range) { z => z > 50 }
        
//        val res = sum(odds.length) { i => odds.at(i) }
//        print(res)
        print(odds.length)
      }
    }
    new Prog with Impl
  }


}