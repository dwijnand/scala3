sealed trait Foo[A, X <: A]

type FooX[F] = F match {
  case Foo[a, x] => x
}

val hello: FooX[Foo[String, "hello"]] = "hello"

//   ==> match case [a, x <: Foo[?, ?]#A] =>> scala.runtime.MatchCase[Foo[a, x], x] #9187 vs Foo[String, ("hello" : String)]?
//     ==> isSubType Foo[String, ("hello" : String)] <:< Foo[a, x]?
//
//       <== isSubType a <:< String = true
//       <== isSubType String <:< a = true
//
//       ==> isSubType x <:< ("hello" : String)?
//         <== isSubType Foo[?, ?]#A <:< ("hello" : String) = false
//         <== isSubType ("hello" : String) <:< Foo[?, ?]#A = false                         !!!
//       <== isSubType x <:< ("hello" : String) = true
//
//       ==> isSubType ("hello" : String) <:< x?
//         ==> isSubType ("hello" : String) <:< Foo[?, ?]#A & ("hello" : String)?
//           ==> isSubType ("hello" : String) <:< Foo[?, ?]#A?
//             <== isSubType String <:< Foo[?, ?]#A (left is approximated) = false          !!!
//           <== isSubType ("hello" : String) <:< Foo[?, ?]#A = false
//         <== isSubType ("hello" : String) <:< Foo[?, ?]#A & ("hello" : String) = false
//       <== isSubType ("hello" : String) <:< x = false
//
//     <== isSubType Foo[String, ("hello" : String)] <:< Foo[a, x] = false
//
//     <== isSubType String <:< a = true
//     <== isSubType a <:< String = true
//
//     ==> isSubType ("hello" : String) <:< x?
//       <== isSubType ("hello" : String) <:< Foo[?, ?]#A = false                           !!!
//     <== isSubType ("hello" : String) <:< x = false
//
//
//    ==> match case [a, x <: Foo[?, ?]#A] =>> scala.runtime.MatchCase[Foo[a, x], x] #9187 vs Foo[String, ("hello" : String)]?
//      ==> isSubType Foo[String, ("hello" : String)] <:< Foo[a, x] isSubType line-199?
//        ==> isSubType a <:< String isSubType line-199?
//          ==> isSubType a <:< String firstTry$1 line-317?
//            ==> isSubType Any <:< String isSubType line-199?
//            <== isSubType Any <:< String isSubType line-199 = false
//            ==> isSubType Nothing <:< String isSubType line-199?
//            <== isSubType Nothing <:< String isSubType line-199 = true
//          <== isSubType a <:< String firstTry$1 line-317 = true
//        <== isSubType a <:< String isSubType line-199 = true
//        ==> isSubType String <:< a isSubType line-199?
//          ==> isSubType String <:< a firstTry$1 line-321?
//            ==> isSubType String <:< Nothing thirdTry$1 line-573?
//            <== isSubType String <:< Nothing thirdTry$1 line-573 = false
//          <== isSubType String <:< a firstTry$1 line-321 = true
//        <== isSubType String <:< a isSubType line-199 = true
//        ==> isSubType x <:< ("hello" : String) isSubType line-199?
//          ==> isSubType Foo[?, ?]#A <:< ("hello" : String) isSubType line-199?
//            ==> isSubType Any <:< ("hello" : String) (left is approximated) fourthTry$1 line-777?
//            <== isSubType Any <:< ("hello" : String) (left is approximated) fourthTry$1 line-777 = false
//          <== isSubType Foo[?, ?]#A <:< ("hello" : String) isSubType line-199 = false
//          ==> isSubType ("hello" : String) <:< Foo[?, ?]#A isSubType line-199?
//            ==> isSubType String <:< Foo[?, ?]#A (left is approximated) fourthTry$1 line-803?
//            <== isSubType String <:< Foo[?, ?]#A (left is approximated) fourthTry$1 line-803 = false
//          <== isSubType ("hello" : String) <:< Foo[?, ?]#A isSubType line-199 = false
//          ==> isSubType Foo[?, ?]#A <:< ("hello" : String) isSubType line-199?
//            ==> isSubType Any <:< ("hello" : String) (left is approximated) fourthTry$1 line-777?
//            <== isSubType Any <:< ("hello" : String) (left is approximated) fourthTry$1 line-777 = false
//          <== isSubType Foo[?, ?]#A <:< ("hello" : String) isSubType line-199 = false
//          ==> isSubType Nothing <:< Foo[?, ?]#A & ("hello" : String) isSubType line-199?
//            ==> isSubType Nothing <:< Foo[?, ?]#A recur$$anonfun$2 line-1319?
//            <== isSubType Nothing <:< Foo[?, ?]#A recur$$anonfun$2 line-1319 = true
//            ==> isSubType Nothing <:< ("hello" : String) recur$$anonfun$2 line-1319?
//            <== isSubType Nothing <:< ("hello" : String) recur$$anonfun$2 line-1319 = true
//          <== isSubType Nothing <:< Foo[?, ?]#A & ("hello" : String) isSubType line-199 = true
//        <== isSubType x <:< ("hello" : String) isSubType line-199 = true
//        ==> isSubType ("hello" : String) <:< x isSubType line-199?
//          ==> isSubType ("hello" : String) <:< Nothing thirdTry$1 line-573?
//            ==> isSubType String <:< Nothing (left is approximated) fourthTry$1 line-803?
//            <== isSubType String <:< Nothing (left is approximated) fourthTry$1 line-803 = false
//          <== isSubType ("hello" : String) <:< Nothing thirdTry$1 line-573 = false
//          ==> isSubType ("hello" : String) <:< Foo[?, ?]#A & ("hello" : String) isSubType line-199?
//            ==> isSubType ("hello" : String) <:< Foo[?, ?]#A recur$$anonfun$2 line-1319?
//              ==> isSubType String <:< Foo[?, ?]#A (left is approximated) fourthTry$1 line-803?
//              <== isSubType String <:< Foo[?, ?]#A (left is approximated) fourthTry$1 line-803 = false
//            <== isSubType ("hello" : String) <:< Foo[?, ?]#A recur$$anonfun$2 line-1319 = false
//          <== isSubType ("hello" : String) <:< Foo[?, ?]#A & ("hello" : String) isSubType line-199 = false
//        <== isSubType ("hello" : String) <:< x isSubType line-199 = false
//      <== isSubType Foo[String, ("hello" : String)] <:< Foo[a, x] isSubType line-199 = false
//      ==> isSubType String <:< a isSubType line-199?
//        ==> isSubType String <:< a firstTry$1 line-321?
//          ==> isSubType String <:< Nothing thirdTry$1 line-573?
//          <== isSubType String <:< Nothing thirdTry$1 line-573 = false
//          ==> isSubType String <:< Any isSubType line-199?
//          <== isSubType String <:< Any isSubType line-199 = true
//        <== isSubType String <:< a firstTry$1 line-321 = true
//      <== isSubType String <:< a isSubType line-199 = true
//      ==> isSubType a <:< String isSubType line-199?
//        ==> isSubType a <:< String firstTry$1 line-317?
//          ==> isSubType Any <:< String isSubType line-199?
//          <== isSubType Any <:< String isSubType line-199 = false
//        <== isSubType a <:< String firstTry$1 line-317 = true
//      <== isSubType a <:< String isSubType line-199 = true
//      ==> isSubType ("hello" : String) <:< x isSubType line-199?
//        ==> isSubType ("hello" : String) <:< Nothing thirdTry$1 line-573?
//          ==> isSubType String <:< Nothing (left is approximated) fourthTry$1 line-803?
//          <== isSubType String <:< Nothing (left is approximated) fourthTry$1 line-803 = false
//        <== isSubType ("hello" : String) <:< Nothing thirdTry$1 line-573 = false
//        ==> isSubType ("hello" : String) <:< Foo[?, ?]#A isSubType line-199?
//          ==> isSubType String <:< Foo[?, ?]#A (left is approximated) fourthTry$1 line-803?
//          <== isSubType String <:< Foo[?, ?]#A (left is approximated) fourthTry$1 line-803 = false
//        <== isSubType ("hello" : String) <:< Foo[?, ?]#A isSubType line-199 = false
//      <== isSubType ("hello" : String) <:< x isSubType line-199 = false
//    <== match case [a, x <: Foo[?, ?]#A] =>> scala.runtime.MatchCase[Foo[a, x], x] #9187 vs Foo[String, ("hello" : String)] = Some(NoType)
