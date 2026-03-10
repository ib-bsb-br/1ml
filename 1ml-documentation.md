Title: Rossberg%20-%201ML%20--%20Core%20and%20modules%20united%20[JFP].pdf

URL Source: https://people.mpi-sws.org/~rossberg/papers/Rossberg%20-%201ML%20--%20Core%20and%20modules%20united%20[JFP].pdf

Published Time: Fri, 02 Nov 2018 16:58:41 GMT

Number of Pages: 62

Markdown Content:
ZU064-05-FPR main 30 October 2018 15:52  

> Under consideration for publication in J. Functional Programming

## 1

# 1ML – Core and Modules United 

ANDREAS ROSSBERG Dfinity Foundation 

rossberg@mpi-sws.org 

Abstract 

ML is two languages in one: there is the core , with types and expressions, and there are modules ,with signatures, structures and functors. Modules form a separate, higher-order functional language on top of the core. There are both practical and technical reasons for this stratification; yet, it creates substantial duplication in syntax and semantics, and it imposes seemingly unnecessary limits on expressiveness because it makes modules second-class citizens of the language. For example, selecting one among several possible modules implementing a given interface cannot be made a dynamic decision. Language extensions allowing modules to be packaged up as first-class values have been proposed and implemented in different variations. However, they remedy expressiveness only to some extent and tend to be even more syntactically heavyweight than using second-class modules alone. We propose a redesign of ML in which modules are truly first-class values, and core and module layer are unified into one language. In this “1ML”, functions, functors, and even type constructors are one and the same construct; likewise, no distinction is needed between structures, records, or tuples. Or viewed the other way round, everything is just (“a mode of use of”) modules. Yet, 1ML does not require dependent types: its type structure is expressible in terms of plain System F ω , in a minor variation of our F-ing modules approach. We introduce both an explicitly typed version of 1ML, and an extension with Damas/Milner-style implicit quantification. Type inference for this language is not complete, but, we argue, not substantially worse than for Standard ML. 

1 Introduction 

The ML family of languages is defined by two splendid innovations: parametric polymor-phism with Damas/Milner-style type inference (Milner, 1978; Damas & Milner, 1982), and an advanced module system based on concepts from dependent type theory (MacQueen, 1986). Although both have contributed to the success of ML, they exist in almost entirely distinct parts of the language. In particular, the convenience of type inference is available only in ML’s so-called core language , whereas the module language has more expressive types, but for the price of being painfully verbose. Modules form a separate language layered on top of the core. Effectively, ML is two languages in one. This stratification makes total sense from a historical perspective. Modules were intro-duced for programming-in-the-large, when the core language already existed. The depen-dently typed machinery that was the central innovation of the original module design was alien to the core language, and could not have been integrated easily. ZU064-05-FPR main 30 October 2018 15:52 

## 2 Andreas Rossberg 

However, we have since discovered that dependent types are not actually necessary to explain modules. In particular, Russo demonstrated that ML-style module types can be readily expressed using only System-F-style quantification (Russo, 1999; Russo, 2003). The F-ing modules approach later showed that the entire ML module system can in fact be understood as a form of syntactic sugar over System F ω (Rossberg et al. , 2014). Meanwhile, the second-class nature of modules is sometimes perceived as a practical limitation. The standard example is the desire to select modules at runtime:          

> module Table = if size >threshold then HashMap else TreeMap

A definition like this, where the choice of an implementation is dependent on dynamics, is entirely natural in object-oriented languages. Yet, it is not expressible with conventional ML modules. Isn’t that a shame! 

1.1 Packaged Modules 

It comes as no surprise, then, that various proposals have been made (and implemented) that enrich ML modules with the ability to package them up as first-class values (Russo, 2000; Dreyer et al. , 2003; Rossberg, 2006; Rossberg & Dreyer, 2013; Garrigue & Frisch, 2010; Rossberg et al. , 2014). Such packaged modules address the most imminent needs, but they are not to be confused with truly first-class modules. They require explicit injection into and projection from first-class core values, accompanied by heavy annotations. For example, in OCaml 4, which implements a simple form of packaged modules, the above example would have to be written as follows:          

> module Table = ( val (if size >threshold
> then (module HashMap)
> else (module TreeMap)) : MAP)

which, arguably, is neither natural nor pretty. Less straightforward examples require even more annotations, because package types cannot always be inferred from context. But it is not just notation: packaged modules have limited expressiveness as well. One problem is that the subtyping of the module language does not extend to package types, because they are part of the ML core language which does not have subtyping. For ex-ample, if HashMap and TreeMap had different signatures HASHMAP and TREEMAP ,respectively, both of which are extensions of MAP , then changing the above to              

> let hashmap = ( module HashMap : HASHMAP)
> let treemap = ( module TreeMap : TREEMAP)
> module Table = ( val (if size >threshold then hashmap else treemap) : MAP)

would not type-check. The consumer of the packages would need to unpack and repack them with their use-site types to allow subtyping to kick in, as in the following:            

> module Table = ( val (if size >threshold
> then (module (val hashmap))
> else (module (val treemap))) : MAP)

A more delicate limitation of packaged modules is that sharing types with them is only possible via a detour through core-level polymorphism. For example, with proper modules, we can express the type of a functor that abstracts over two modules of a given signature with the requirement that their types t are equivalent: ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 3         

> signature S = {type t ... }
> F : (X : S) →(Y : S with type t = X.t) →U

In the case of a core-level function abstracting over packaged modules the dependency on a parameter is not possible, so it gets a bit more complicated. We need to introduce an auxiliary polymorphic type variable (which is implicitly quantified):           

> f : ( module Swith type t = ’a) →(module Swith type t = ’a) →u

Worse, because core-level polymorphism is first-order, this approach cannot express type sharing between type constructors – a complaint that has come up several times on the OCaml mailing list. For example, if one were to abstract over a monad:             

> val map : ( module MONAD with type ’a t = ?) →(’a →’b) →?→?

There is nothing that can be put in place of the ?’s to complete this function signature – it would require a type variable of higher kind, which is not supported in ML. In some cases the programmer may be able to work around this limitation resorting to weaker types. But in the general case they are forced to drop the use of packaged modules and raise the function (and potentially a lot of downstream code) to the functor level – which not only is very inconvenient, it also severely restricts the possible computational behaviour of such code, because all module-level computations are effectively “static”, i.e., cannot involve dynamic constructs such as conditionals, let alone general recursion. One could imagine addressing this particular limitation by introducing higher-kinded polymorphism into the ML core. But with such an extension type inference would require higher-order unification and hence become undecidable – unless accompanied by signifi-cant restrictions that are likely to defeat this example (or others). 

1.2 First-Class Modules 

Why not true first-class modules, then? Can we overcome the segregation and make mod-ules more equal citizens of the language? This idea has been explored, of course. The answer from the literature so far has been: no, because first-class modules make type-checking undecidable and type inference infeasible. The most directly relevant work is the calculus of translucent sums of Harper & Lil-libridge (1994) (a precursor of later work on singleton types (Stone & Harper, 2006)). It can be viewed as an idealised functional language that allows types as components of (dependent) records, so that they can express modules. In the type of such a record, individual type members can occur as either transparent or opaque (hence, translucent ), which is the defining feature of ML module typing. Harper & Lillibridge prove that type-checking this language is undecidable. Their result applies to any language that (a) has contravariant functions, (b) has both transparent and opaque types, and (c) allows opaque types to be subtyped by arbitrary transparent types. The latter feature usually manifests in a subtyping rule like the following, 

{D1[τ/t]} ≤ { D2[τ/t]}{type t= τ; D1} ≤ { type t; D2} FORGET 

which is, in some variant, at the heart of every definition of signature matching. In the premise the concrete type τ is substituted for the abstract t in the remaining declarations ZU064-05-FPR main 30 October 2018 15:52 

## 4 Andreas Rossberg D1 and D2 of the signatures. Obviously, this rule is not inductive. And that is a real problem: the substitution can arbitrarily grow the types, and thus potentially require infinite derivations. A concrete example triggering non-termination is the following, adapted from Harper & Lillibridge (1994):                   

> type T = {type A; f : A →() }
> type U = {type A; f : (T where type A = A) →() }
> type V = T where type A = U g (X : V) = X : U (* V ≤U ? *)

Checking V ≤ U would match type A with type A=U , substituting U for A accordingly, and then requires checking that the types of f are in a subtyping relation – which contravari-antly requires checking that (T where type A = A)[U/A] ≤ A[U/A] , but that is the same as the V ≤ U we wanted to check in the first place. In fewer words, signature matching is no longer decidable when module types can be abstracted over, which is the case if module types are simply collapsed into ordinary types. It also arises if “abstract signatures” are added to the language, as in OCaml, where the same divergent example can be constructed on the module type level alone (Rossberg, 1999b). Some readers may consider decidability a rather theoretical concern. However, there also is the – quite practical – issue that the introduction of signature matching into the core language makes ML-style type inference impossible. Milner’s algorithm W (Milner, 1978) is far too weak to handle higher-order types, let alone dependent types. Moreover, modules introduce subtyping, which breaks unification as the basic algorithmic tool for solving type constraints. And while inference algorithms for subtyping exist, they have much less satisfactory properties than our beloved Hindley/Milner sweet spot. Worse, module types do not even form a lattice under subtyping:                 

> f1:{type t a; x : t int }→int f2:{type t a; x : int }→int g = if condition then f1else f2

There are at least two possible types for g:        

> g : {type t a = int; x : int }→int g : {type t a = a; x : int }→int

Neither is more specific than the other, so no least upper bound exists. Consequently, annotations are necessary to regain principal types for constructs like conditionals, in order to restore any hope for compositional type checking , let alone inference. 

1.3 F-ing Modules 

In the work on F-ing modules with Russo & Dreyer (Rossberg et al. , 2014) we have demonstrated that ML modules can be expressed and encoded entirely in vanilla System F (or F ω , depending on the concrete core language and the desired semantics for functors). Effectively, the F-ing semantics defines a type-directed desugaring of module syntax into System F types and terms, and inversely, interprets a stylised subset of System F types as module signatures. ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 5

Interestingly, in that paper we assume that the core language on which modules sit is simply System F (respectively, F ω ) itself. That leads to the seemingly paradoxical situation that the core language has more expressive types than the module language. But that makes sense when considering that the module translation rules manipulate the sublanguage of module types in ways that would not generalise to arbitrary System F types. In particular, the rules implicitly introduce and eliminate universal and existential quantifiers, which is key to making modules a usable means of abstraction. But the process is guided by, and only meaningful for, module syntax; likewise, the built-in subtyping relation is only “complete” (and decidable) for the specific occurrences of quantifiers in module types. Nevertheless, the observation that modules are just sugar for certain kinds of constructs that the core language can already express (even if less concisely), raises the question: what necessitates modules to be second-class in that system? 

1.4 1ML 

The answer to the previous question is: very little! And the present article is all about explaining, exploring and exploiting that answer. In essence, the F-ing modules semantics reveals that the syntactic stratification between ML core and module language is merely a rather blunt approach to enforce predicativity for module types: it prevents abstract types themselves from being instantiated with binders for abstract types. But this blunt syntactic restriction can be replaced by a much more surgical 

semantic restriction! It is in fact enough to introduce a simple universe distinction between small and large 

types – reminiscent of Harper & Mitchell’s XML (1993) – and limit the equivalent of the FORGET rule shown earlier to allow only small types for substitution, which serves to exclude problematic occurrences of quantifiers: 

{D1[τ/t]} ≤ { D2[τ/t]} τ small 

{type t= τ; D1} ≤ { type t; D2} FORGET 

A small type is one that does not itself contain any abstract type components or parameters. In particular, a type like {type t; D} is not small. The side condition thus prevents the substitution from introducing new occurrences of an opaque type specification, which would necessitate further (potentially never-ending) substitutions. That’s all, really. That would settle decidability, but what about type inference? Well, we can use the same distinction! A quick inspection of the subtyping rules in the F-ing modules semantics reveals that they, almost, degenerate to type equivalence when applied to small types. If we limit instantiation of implicit polymorphic type variables (and thus inference and unification) to small types then type inference works almost as usual. The only exception to subtyping coinciding with equivalence on small types is width subtyping on structures. We hence need to be willing to accept that inference is not going to be complete for records – which it already isn’t in Standard ML, whereas OCaml does not support inferring types of regular records in the first place. 1                

> 1Even though it is well-known how to achieve complete inference with record polymor-phism (R´ emy, 1989; Ohori, 1995). ZU064-05-FPR main 30 October 2018 15:52

## 6 Andreas Rossberg 

In this spirit, this paper presents 1ML , an ML-dialect in which modules are truly first-class values. The name is both short for “1st-class module language” and suggestive of the fact that it unifies core and modules of ML into one language. Our contributions are as follows: 

• We present a decidable type system for a language of first-class modules that sub-sumes conventional second-class ML modules. 

• We give an elaboration of this language into plain System F ω .

• Conversely, we demonstrate that F ω can be embedded into this language. 

• We show how Damas/Milner-style type inference can be integrated; it is incomplete, but only in ways that are already present in existing ML implementations. 

• Besides theoretic considerations, we develop the basis for a practical design of an ML-like language in which the distinction between core and modules is eliminated. This redesign has several benefits: it produces a language that is more expressive and 

concise , and at the same time, more minimal and uniform . “Modules” become a natural means of expressing all forms of polymorphism, both universal and existential. They can be freely intermixed with “computational” code and data, that is, polymorphism is fully first-class. Type inference integrates in a rather seamless manner, reducing the need for explicit annotations to large types, module or not. Every programming concept is derived from a small set of orthogonal constructs, over which general and uniform syntactic sugar can be defined. Relative to the conference version of this paper, this article adds more extensive expla-nations of the design and various technicalities of the language, it tweaks some pieces of the formalisation of type inference to make it easier to interpret as an algorithm, it includes all meta-theory that was previously omitted for space reasons — such as the proof of decidability of type checking —, and it devotes an entire new section to the expressiveness of the language (Section 5), including a simple extension with impredicative “packages” and a sound and complete embedding of System F ω .

2 1ML with Explicit Types 

Despite the simplicity of the basic ideas, the dear reader will probably have guessed that the complete story isn’t quite as trivial. To separate concerns a little, we will first introduce 1ML ex , a sublanguage of 1ML proper that is explicitly typed. We hold off fancier features like implicit typing and type inference until Sections 6 and 7. The kernel syntax of 1ML ex is given in Figure 1. This kernel language is intentionally small, but features everything that is semantically relevant. In addition, Figure 2 defines a rich set of syntactic sugar over this kernel that provides many of the syntactic forms familiar from the ML family of languages. 2 In both figures, as well as in other places throughout this article, we use an overbar, phrase , to stand for an arbitrary number of repetitions of 

phrase (including zero of them). We also conveniently write ⇒→ to range over both forms of arrows. Let us take a little tour of 1ML ex by way of examples.          

> 2We omit further sugar that is standard and not worth expanding on, such as tuples as records
> {1 : T1;. . . ;n:Tn}, pattern matching, or multi-argument functions as functions over tuples.

ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 7

(identifiers) X

(types) T :: = E | bool | {D} | (X:T ) ⇒→ T | type | = E | T where (. X:T )

(declarations) D :: = X : T | include T | D; D | ε

(expressions) E :: = X | true | false | if X then E else E:T |

{B} | E.X | fun (X:T ) ⇒E | X X | type T | X:>T

(bindings) B :: = X = E | include E | B; B | ε

Fig. 1. Kernel syntax of 1ML ex 

(types) let B in T := {B; X = type T }.XT1 ⇒→ T2 := (X : T1) ⇒→ T2

T where (. X P : T = E) := T where (. X : P ⇒ (= E : T )) 

T where (type .X P = T ′) := T where (. X : P ⇒ (= type T ′)) 

(declarations) local B in D := include (let B in {D})

X P : T := X : P ⇒ TX P : T = E := X : P ⇒ (= E : T )

type X P := X : P ⇒ type type X P = T := X : P ⇒ (= type T )

(expressions) let B in E := {B; X = E}.X

if E1 then E2 else E3 : T := let X = E1 in if X then E2 else E3 : TE1 E2 := let X1 = E1; X2 = E2 in X1 X2

E T := E (type T ) (if T unambiguous) 

E : T := (fun (X : T ) ⇒ X) EE :> T := let X = E in X :> T

fun P ⇒ E := fun P ⇒ E

(bindings) local B in B′ := include (let B in {B′})

X P : T ′ :> T ′′ = E := X = fun P ⇒ E : T ′ :> T ′′ 

type X P = T := X = fun P ⇒ type T

where (parameter) P :: = (X:T ) with abbreviation (parameter) X := (X: type )

(Identifiers only occurring on the right-hand side are considered fresh) Fig. 2. Syntactic abbreviations for 1ML ex 

Functional Core A major part of 1ML ex consists of fairly conventional functional lan-guage constructs. On the expression level, as a representative for a base type, we have Booleans ( true , false , if ) – in examples that follow, we will often assume the presence of an integer type and respective constructs as well. Then there are records {B}, which consist of a sequence of bindings, and can be accessed via dot notation E.X. And of course, it wouldn’t be a functional language without functions ( fun ) and their application ( X1 X2). In a first approximation, these constructs are mirrored on the type level as one would ex-pect, except that for functions we allow two forms of arrows, distinguishing pure function types ( ⇒) from impure ones ( →) (discussed later). Like with F-ing modules (Rossberg et al. , 2014), most elimination forms in the kernel syntax only allow variables as subexpressions. However, the general expression forms are all definable as straightforward syntactic sugar, as given in Figure 2: because we can encode ZU064-05-FPR main 30 October 2018 15:52 

## 8 Andreas Rossberg 

let -bindings with module projections, we can desugar all expressions into a kind of A-normal form. For example, the application    

> (fun (n : int) ⇒n + n) 3

desugars into        

> let f = fun (n : int) ⇒n + n; x = 3 in f x

and further into     

> {f = fun (n : int) ⇒n + n; x = 3; body = f x }.body

This works because records actually behave like ML structures, such that every bound identifier is in scope for later bindings – which enables encoding let -expressions. Also, notably, if -expressions require a type annotation in 1ML ex . As we will see, the type language subsumes module types, and as discussed in Section 1.2 there wouldn’t generally be a unique least upper bound without a type annotation. However, once we advance to full 1ML with type inference this annotation can usually be omitted (Section 6). Other abbreviations defined in Figure 2 are discussed further below. 

Reified Types The core feature that makes 1ML ex able to express modules is the ability to embed types in a first-class manner: the expression type T reifies the type T as a value .3

Such an expression has type type , and thereby can be abstracted over. For example,         

> id = fun (a : type )⇒fun (x : a) ⇒x

defines a polymorphic identity function, similar to how it would be written in dependent type theories. Note in particular that a is a term variable, but it is used as a type in the annotation for x. This is enabled by the “path” form E in the syntax of types, which expresses the (implicit) projection of a type from a term, provided this term has type type .Consequently, all variables are term variables in 1ML, and there is no separate notion of type variable. More interestingly, a function can return types, too. Consider           

> pair = fun (a : type )⇒fun (b : type )⇒type {fst : a; snd : b }

which takes two types and returns a type, and effectively defines a type constructor . Ap-plied to a reified type it yields a reified type, as a first class value. Again, the implicit projection from “path” expressions enables using this as a type:             

> second = fun (a : type )⇒fun (b : type )⇒fun (p : pair a b) ⇒p.snd

In this example, the whole of “ pair a b ” is a term of type type .Figure 2 also defines a bit of syntactic sugar for function and type definitions in “equa-tional” form with parameters on the left, which makes them look more like in traditional ML. 4 For example, the previous functions could equivalently be written as                           

> 3Ideally, “ type T” should be written just “ T”, like in various dependently typed languages. However, that creates syntactic ambiguities, e.g. for phrases like “ {} ”, which we prefer to avoid. The ambiguity could only be addressed by moving to a more artificial syntax for types themselves. Nevertheless, we at least allow writing “ E T ” for the application “ E(type T)” if Tunambiguously parses as a type.
> 4Some binding forms in Figure 2allow multiple consecutive type annotations, as in “X : T : U = E ”. I do not consider this useful, it is merely a shortcut to avoid introducing one-off notation for optional phrases. ZU064-05-FPR main 30 October 2018 15:52

1ML – Core and modules united 9  

> id a (x : a) = x
> type pair a b = {fst : a; snd : b }
> second a b (p : pair a b) = p.snd

For now, Figure 2 defaults an omitted type annotation on a parameter, as in the case of a

and b above, to type – a rule that we will refine somewhat when we introduce implicit types in Section 6. It may seem surprising that we can just reify types as first-class values. But reified types (or “atomic type modules”) have been common in module calculi for a long time (Lillib-ridge, 1997; Dreyer et al. , 2003; Rossberg & Dreyer, 2013; Rossberg et al. , 2014). We are merely making them available in the source language directly. For the most part, this is just a notational simplification over what first-class modules already offer: instead of having to define a spurious module T = {type t = int } : {type t} and then refer to T.t , we allow injecting types into modules (i.e., values in 1ML) anonymously , without wrapping them into a structure; thus t = ( type int) : type , which can be referred to as just t.

Declarations In the ML module system, bindings – i.e., definitions – in the module syntax are mirrored by declarations – i.e., specifications – in the signature syntax. That is no different in 1ML, where modules become records, such that bindings define record fields: analogously, signatures become record types, and declarations specify record fields. For example, the previous definitions could be collected in a record with a type as follows:                     

> type S =
> {
> id : (a : type )⇒a→apair : (a : type )⇒(b : type )⇒type
> second : (a : type )⇒(b : type )⇒pair a b →b
> }

This amounts to a module signature, since it contains the type (constructor) pair as a component. And that is referred to in the type of second , which shows that record types are seemingly “dependent”: like for terms, earlier components are in scope for later com-ponents – the key insight of the F-ing approach is that this dependency is benign, however, and can be translated away, as we will see in Section 4. As for bindings, Figure 2 defines analogous syntactic sugar for declarations, which enables writing the above declarations in a more familiar style:      

> id a : a →a;
> type pair a b; second a b : pair a b →b

In particular, we introduce the same kind of sugar that allows putting parameters on the left of declarations as we do for bindings. And like before, type annotations on parameters can be omitted, defaulting to type . This design not only reconstructs the way type speci-fications are written in ML (as for pair ). 5 The left-hand side parameter syntax uniformly also generalises to ordinary value specifications and allows us to rid ourselves of the brittle     

> 5Minus ML’s literally backwards type application syntax. ZU064-05-FPR main 30 October 2018 15:52

## 10 Andreas Rossberg 

implicit scoping rules that conventional ML defines for polymorphic type variables (as for 

id and second ). 

Translucency The type type allows us to classify types opaquely : given a value of type 

type , nothing is known about what type it is – it is abstract. But for modular program-ming it is essential that types can selectively be specified transparently , with a concrete definition. In particular, that enables expressing the vital concept of type sharing (Harper & Lillibridge, 1994; Leroy, 1994; Harper & Pierce, 2005). As a simple example, consider these type alias definitions:    

> type size = int
> type pair a b = {fst : a; snd : b }

According to the idea of translucency, the variables defined by these definitions can be classified in one of two ways in 1ML. Either opaquely :       

> size : type
> pair : (a : type )⇒(b : type )⇒type

Or transparently :          

> size : (= type int) pair : (a : type )⇒(b : type )⇒(= type {fst : a; snd : b })

The latter use a variant of singleton types (Stone & Harper, 2006; Dreyer et al. , 2003) to reveal the definitions: a type of the form “ = E” is inhabited only by values that are “structurally equivalent” to E, in particular, with respect to components of type type . It allows the type system to infer, for example, that the application pair size size is equivalent to the type {fst : int; snd : int }. A type (= E) is a subtype of the type of E itself, and consequently, transparent classifications define subtypes of opaque ones, which is the crux of ML signature matching. Translucent types usually occur as declarations in signatures, where according to Fig-ure 2 once more, they can be abbreviated to the more familiar    

> type size = int
> type pair a b = {fst : a; snd : b }

i.e., as in ML, transparent declarations look just like the definitions given earlier. But the former appear in types while the latter appear in values. Singletons can be formed over arbitrary values. This gives the ability to express module sharing and aliases . In the basic semantics described in this article, this is effectively a shorthand for sharing all types contained in the module (including those defined inside transparent functors, see below). For example, given a signature        

> type T = {type t a; A : {type u; x : u }; f : A.u →t bool }

and a module M : T , the signature   

> type S = {B = M : T }

with its transparent module component is equivalent to the more explicit formulation            

> type S = {B : {type t a = M.t a; A : {type u = M.A.u; x : u }; f : A.u →t bool }} ZU064-05-FPR main 30 October 2018 15:52

1ML – Core and modules united 11 

which only makes the individual type components transparent, while not implying anything about the identity of its values. This behaviour matches the meaning of structure sharing in Standard ML ’97 (Milner et al. , 1997). 6

We leave the extension of 1ML to tracking full value equivalence, like in our F-ing semantics for applicative functors (Rossberg et al. , 2014), to future work. 

Functors Returning to the 1ML grammar from Figure 1, the remaining constructs of the language are typical for ML modules, although they are perhaps a bit more general than what is usually seen. Let us explain them using an example that demonstrates that our language can readily express “real” modules. Here is the unavoidable example of a functor that defines a simple map ADT:                                         

> type EQ =
> {
> type t; eq : t →t→bool
> };
> type MAP =
> {
> type key;
> type map a; empty a : map a; add a : key →a→map a →map a; lookup a : key →map a →opt a
> };Map (Key : EQ) :>MAP where (type .key = Key.t) =
> {
> type key = Key.t;
> type map a = key →opt a; empty a = fun (k : key) ⇒none a; lookup a (k : key) (m : map a) = m k; add a (k : key) (v : a) (m : map a) =
> fun (x : key) ⇒if Key.eq x k then some a v else m x : opt a
> }

The record type EQ amounts to a module signature with an abstract type component t.Similarly, MAP defines a signature with abstract key and map types. The Map function is a functor: it takes a value of type EQ , i.e., a module. From that it constructs a naive imple-mentation of maps. “ X:>T ” is the usual sealing operator that opaquely ascribes a type (i.e., signature) to a value (here, a module). The type refinement syntax “ T where (type .X=T )”should be familiar from ML, but here it actually is derived from a more general construct: “T where (. X:U)” refines T ’s subcomponent at path .X to type U, which can be any subtype of what’s declared by T . That form subsumes module sharing as well as other forms of refinement, with some appropriate sugar defined in Figure 2.      

> 6But without disallowing transparent types in the signature of M, which is one of the more controversial limitations of SML ZU064-05-FPR main 30 October 2018 15:52

## 12 Andreas Rossberg 

Applicative vs. Generative In this article, we stick to a relatively simple semantics for functor-like functions, in which Map is generative (Russo, 2003; Dreyer, 2005; Rossberg 

et al. , 2014). That is, like in Standard ML, each application will yield a fresh map ADT, because sealing occurs inside the functor:       

> M1= Map IntEq; M2= Map IntEq; m = M 1.add int 7 M 2.empty (* ill-typed: M 1.map 6=M2.map *)

But as we saw earlier, type constructors like pair or map are essentially functors, too! Sealing the body of the Map functor hence implies higher-order sealing of the nested map 

“functor”, as if performing map :> type ⇒ type . It is vital that the so-sealed map functor – which returns an abstract type – has applicative semantics (Leroy, 1995; Rossberg et al. ,2014), so that    

> type map a = M 1.map a;
> type t = map int;
> type u = map int

yields t = u, as one would expect from a proper type constructor. We hence need applicative functors as well. 7 To keep things simple, we restrict ourselves to the simplest possible semantics in this paper, in which we distinguish between pure ( ⇒,i.e. applicative) and impure ( →, i.e. generative) function types, but sealing is always impure – or strong (Dreyer et al. , 2003). That is, the use of sealing inside a functor makes it gen-erative. The only way to produce an applicative functor is by sealing a (fully transparent) functor as a whole , with applicative functor type, as for the map type constructor above. Given:                                     

> F = ( fun (a : type )⇒type {x : a }):>type ⇒type
> G = ( fun (a : type )⇒type {x : a }):>type →type
> H = fun (a : type )⇒(type {x : a }:>type )J= F :>type →type
> K = G :>type ⇒type (* ill-typed! *)

F is an applicative functor, such that F int = F int . G and H on the other hand are generative functors; the former because it is sealed with impure function type, the latter because sealing occurs inside its body. Consequently, G int or H int are impure expressions and invalid as type paths (though it is fine to bind their result to a name, e.g., “ type w = G int ”, and use the constant w as a type). Applicative functor types are subtypes of generative ones, so that J turns F into a generative functor. Lastly, K is ill-typed, because applicative functor types are subtypes of generative ones, but not the other way round. This semantics for applicative functors – which is very similar to the applicative func-tors of Shao (1999) – is somewhat limited, but just enough to encode sealing over type constructors and hence recover the ability to express type definitions as in conventional ML. This choice is mainly to keep this article focussed on the novelties of 1ML. More fully-featured applicative functors as with F-ing modules (Rossberg et al. , 2014), where sealing is pure, could easily be incorporated into 1ML, but complicate elaboration in ways that are largely orthogonal to our present goals.     

> 7Not to be confused with the applicative functors later introduced in Haskell by McBride & Paterson (2008). ZU064-05-FPR main 30 October 2018 15:52

1ML – Core and modules united 13 

Effects The ability to distinguish pure from impure, for computations or functions, is mo-tivated by dealing with type abstraction correctly. But even in a traditional “core language” context this distinction is useful, for example, when we consider adding impure constructs to the language, such as an ML-style type ref T of mutable references with the obvious operators:                  

> new : (a : type )⇒(x : a) →ref a rd : (a : type )⇒(r : ref a) →awr : (a : type )⇒(r : ref a) ⇒a→{}

Their types make explicit where effects can occur, by mixing pure and impure arrows. A type parameter – expressing (explicit) polymorphism – is best considered a pure function: “instantiating” a polymorphic type should not have any effect. Similarly, an impure func-tion with curried value parameters (like wr ) releases its effect only when the last argument is provided. Expressing effects in function types is not just useful documentation, it can also aid type inference (see Section 6.1). The simplistic effect system could naturally be refined to track relevant effects in a manner more fine-grained than with just a black-and-white distinction. However, we do not explore that space further here. Clearly, there is plenty of room for future work. We discuss one interesting direction, effect polymorphism, in a spin-off paper (Rossberg, 2016), see Section 8. 

Transparent vs. Opaque Type Ascription Like Standard ML’s modules, our language provides two ways of ascribing a type to an expression or definition: 8

• opaquely (E :> T), which performs sealing as described above, that is, any type that is specified abstractly in T will be opaque in the type of the expression; 

• transparently (E : T ), which implicitly refines all abstract specifications in T with their actual definitions from E.The latter form is convenient when an ascription is used simply to narrow a signature, i.e., limit what is visible to the outside of a module. In Standard ML it is its own primitive with relatively complex semantics. But it turns out that it can simply be encoded as applying the identity functor at type T, as shown in Figure 2. 

Higher Polymorphism So far, we have focussed on how 1ML reconstructs features that are well-known from ML. As a first example of something that cannot directly be expressed in conventional ML, consider first-class polymorphic arguments:       

> f (id : (a : type )⇒a→a) = {x = id int 5; y = id bool true }

The function f takes a function id as argument that is (explicitly) polymorphic, and used with different instantiations inside the body. That is not possible with the prenex polymor-phism of core ML. Similarly, existential types are directly expressible:          

> 8The semantics of OCaml’s module type ascription, despite being written M : T , is opaque, i.e., corresponds to M:>Tin our notation. ZU064-05-FPR main 30 October 2018 15:52

## 14 Andreas Rossberg           

> type SHAPE = {type t; area : t →float }
> type shape = {S : SHAPE; v : S.t }
> totalArea = List.foldLeft shape float ( fun (a : float) (x : shape) ⇒a + x.S.area x.v)

This example uses a two stage construction: SHAPE abstracts an ADT of shapes, which can be implemented e.g. as a circle or rectangle:       

> Circ : SHAPE = {type t = {radius : float }; area c = pi * c.radius * c.radius }
> Rect : SHAPE = {type t = {width : float; height : float }; area r = r.width * r.height }

The type shape pairs such an ADT with an actual value:         

> aCirc = {S = Circ; v = {radius = 2.0 }} :>shape aRect = {S = Rect; v = {width = 1.8; height = 1.2 }} :>shape

The trick here is that the “: >” operator corresponds directly to an introduction form for existential types. Because their concrete type is “forgotten” this way, shapes like these can be collected in a heterogeneous list, for which the function totalArea is able to compute the cumulative area: 

> totalArea [aCirc, aRect, aCirc]

This works because the computation inside the function is agnostic to the actual type of each shape, and the 1ML typing rules implicitly “open” the existential package. The upshot is that ADTs and existential types are one and the same thing in 1ML – driving home Mitchell & Plotkin’s original point (Mitchell & Plotkin, 1988) not just as a theoretical semantic observation, but as very concrete language design choice. It turns out that the previous examples can still be expressed with packaged modules (Section 1.1), even though they would become fairly verbose. But now consider:                  

> type COLL c =
> {
> type key;
> type val; empty : c; add : c →key →val →c; lookup : c →key →opt val; keys : c →list key
> };entries c (C : COLL c) (xs : c) : list (C.key ×C.val) = ...

COLL amounts to a parameterised signature , and is akin to a Haskell-style type class (Wadler & Blott, 1989). It contains two abstract type specifications, which are known as associated types in the type class literature (or in the C++ universe). The function entries is parame-terised over a corresponding module C – an (explicit) instance of the type class if you want. Its result type depends directly on C’s definition of the associated types. Such a dependency can be expressed in ML on the module level, but not at the core level. 9                       

> 9In OCaml 4, this example can be approximated only with heavy fibration:
> module type COLL = sig type coll type key type val ... end let entries ( type c) ( type k) ( type v) (module C : COLL with type coll = c and type key = k and type value = v) (xs : c) : (k * v) list = ... ZU064-05-FPR main 30 October 2018 15:52

1ML – Core and modules united 15 

Moving to higher kinds, things become even more interesting:                      

> type MONAD (m : type ⇒type ) =
> {
> return a : a →m a; bind a b : m a →(a →m b) →m b
> };map a b (m : type ⇒type ) (M : MONAD m) (f : a →b) (mx : m a) = M.bind a b mx ( fun (x : a) ⇒M.return b (f x)) (* : m b *)

Here, MONAD is again akin to a constructor class, i.e., a type class over a type constructor. As explained in Section 1.1, this kind of polymorphism cannot be expressed in ML, even in dialects with packaged modules. 

Computed Modules Just for completeness, we should mention that the motivating exam-ple from Section 1 can of course be written (almost) as is in 1ML ex :        

> Table = if size >threshold then HashMap else TreeMap : MAP

The only minor nuisance is the need to annotate the type of the conditional. As explained earlier, the annotation is necessary in general to achieve unique types. But in most cases it can usually be inferred once we add inference to the mix (Section 6). 

Predicativity What is the restriction we employ to maintain decidability? It is simple: during subtyping (also known as signature matching) the type type can only be matched by small types, which are those that do not themselves contain the type type ; or in other words, monomorphic types. Small types thus exclude first-class abstract types, actual func-tors (functions taking type parameters), and type constructors (which are just functors). The primary place where the distinction between small and large types comes into play is when applying a function that abstracts over a type, more precisely, over a value of type 

type . The type of the actual argument value naturally has to be a subtype of the function’s formal parameter type. If that parameter type includes a component of type type , i.e., an abstract type, then the argument must contain a corresponding “type value”. And the crucial restriction is that this type value must denote a small type. For example, consider these applications of the Map functor from earlier:                       

> M1= Map {type t = {a : int; b : int }; . . . }
> M2= Map {type t = {type u; v : u; f : u →int }; . . . }
> M3= Map {type t = (u : type )→u→u; . . . }

The first application is fine: it passes the type {a : int; b : int }, which is a regular small type with only value components. The second application, however, defines t to be a type that itself has an abstract type component u. Such a definition is a large type, and as such, per the restriction mentioned in Section 1.4, not a subtype of the abstract declaration type t

in the functor’s parameter type EQ . Consequently, this application is rejected by the type system. Similarly, the third line defines t to be a large type, because it is a function that takes an abstract type as a parameter. This application is likewise rejected. ZU064-05-FPR main 30 October 2018 15:52 

## 16 Andreas Rossberg 

Intuitively, small types characterise what would be “values” while large type characterise what would be “modules” in conventional ML. In 1ML it is possible to abstract over modules as any other first-class value, but it is not possible to abstract over module types –at least not directly; in Section 5.1 we will lift this restriction with a minor addition to the language. All of the following define large types:                          

> type T1=type ;
> type T2={type u};
> type T3={type u = T 2};
> type T4= (x : {} )→type ;
> type T5= (a : type )⇒{} ;
> type T6={type u a = bool };

None of these are expressible as type expressions in conventional ML, and vice versa, all ML type expressions materialise as small types in 1ML, so nothing is lost in comparison. The restriction on subtyping affects annotations, parameterisation over types, and the formation of abstract types. For example, for all of the above Ti, none of the following definitions are well-typed:                     

> type U = pair T iTi;(* error *) A = ( type Ti) : type ;(* error *) B = {type u = T i}:>{type u};(* error *) C = if bthen Tielse int : type (* error *)

Notably, the case A with T1 literally implies type type 6 : type – although type type 

itself is a well-formed expression, it is the value of T1 above! But its only type is the transparent (= type type ); it cannot be abstracted. Preventing a type :type situation is the main challenge with first-class modules, and the separation into a small universe (denoted by type ) and a large one (for which no syntax exists) achieves that. A transparent type specification is small as long as it reveals a small type. Consequently, the following functor application is fine, because type u in t is transparent:         

> M4= Map {type t = {type u = int; v : u; f : u →int }; . . . }

Likewise, the following bindings,         

> type T′
> 1= (= type int);
> type T′
> 2={type u = int }

are to small types and would hence not cause an error when inserted into the definitions of 

U, A, B, and C above. 

Recursion The 1ML ex syntax we give in Figure 1 omits a couple of constructs that one can rightfully expect from any serious ML contender: in particular, there is no form of recursion, neither for terms nor for types. It turns out that those are largely orthogonal to the overall design of 1ML, so we only sketch them here. Recursive functions can be added simply by throwing in a primitive polymorphic fix-point operator 

fix a b : ((a → b) → (a → b)) → (a → b) 

On top of that, it is only a matter of defining suitable syntactic sugar: 

rec X Y (Z : T ) : U = E := X = fun Y ⇒ fix T U (fun (X : ( Z:T ) →U) ⇒ fun (Z:T ) ⇒ E)

Given an appropriate fixpoint operator, this generalises further to mutually recursive func-tions in the usual manner. Note how the need to specify the result type b (respectively, UZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 17                                                       

> (kinds) κ:: =Ω|κ→κ
> (types) τ:: =α|τ→τ| { l:τ} | ∀ α:κ.τ| ∃ α:κ.τ|λ α :κ.τ|τ τ
> (terms) e,f:: =x|λx:τ.e|e e | { l=e} | e.l|λ α :κ.e|eτ|pack 〈τ,e〉τ|unpack 〈α,x〉=ein e
> (environ’s) Γ:: =· | Γ,α:κ|Γ,x:τ
> Fig. 3. Syntax of F ω

for the sugared form) prevents using the operator to construct transparent recursive types, because U has no way of referring to the result of the fixpoint. (In this simple definition, U

is not even allowed to refer to the argument Z, although that could be relaxed with a more powerful fixpoint operator.) Moreover, fix yields an impure function, so even an attempt to define an abstract type recursively, as in       

> rec stream (a : type ) : type =type {head : a; tail : stream a }

won’t type-check, because stream wouldn’t be an applicative functor, and so the term 

stream a on the right-hand side is not a valid type — fortunately, because there would be no way to translate such a definition into System F ω with a conventional fixpoint operator. Recursive (data)types have to be added separately. One approach, that has been used by Harper & Stone’s type-theoretic account of Standard ML (Harper & Stone, 2000), is to interpret a recursive datatype like      

> datatype t = A |Bof T

as a module defining a primitive ADT with the signature               

> {type t; A : t; B : T⇒t; expose a : ( {} →a) ⇒(T→a) ⇒t→a}

where expose is a case-operator accessed by pattern matching compilation. We refer to Harper & Stone (2000) for more details on this approach. There is one caveat, though: datatypes expressed as ADTs require sealing. With the simple system presented in this article alone they hence could not be defined inside applicative functors. This limitation is removed by pure sealing, which, as mentioned before, is an obvious extension from the F-ing modules paper (Rossberg et al. , 2014) that is applicable to 1ML. 

3 System F ω

Before diving deep into the semantics of 1ML in Section 4, a brief detour is in order. Fol-lowing the F-ing modules approach (Rossberg et al. , 2014), 1ML’s semantics is defined by translation into System F ω , the higher-order polymorphic λ -calculus (Barendregt, 1992). Readers who know F ω inside out should feel free to skip over this section. 

Syntax Figure 3 gives the syntax of (impredicative) System F ω as we will use it here. It includes simple record types {l : τ} (where we assume that labels are always disjoint), but is otherwise completely standard. In the grammar, and elsewhere, we liberally use the meta-notation A to stand for zero or more repetitions of an object or formula A, sometimes writing ε explicitly for the empty sequence. We also sometimes abuse the notation A to actually denote the unordered set {A}.ZU064-05-FPR main 30 October 2018 15:52 

## 18 Andreas Rossberg 

To differentiate the external language (1ML) from the internal one (F ω ) later in the paper, we consistently use uppercase letters to range over phrases of the former ( X, T , E,etc.), and lowercase for the latter ( α, x, τ, e). 

Static Semantics The full typing rules of F ω are given in Figure 4. The judgements are as usual, with Γ ` 2 denoting well-formedness of typing environments. Type equivalence is defined as full β η -equivalence. The only point of note is that, unlike in many presentations, environments Γ permit term variables x (but not type variables α) to be shadowed without α-renaming, which is convenient for translating 1ML ex -bindings later. Thus, we take the notation Γ(x) to index the rightmost binding of x in Γ. Finally, dom (Γ) denotes the set of bound variables in Γ,while fv (τ) and fv (e) are the free type and term variables of τ and e, respectively. 

Dynamic Semantics We assume a standard left-to-right call-by-value operational seman-tics, which is defined in Figure 5 via small-step reduction rules and evaluation contexts. There is nothing unusual about the semantics, so we can move on immediately to the meta-theory. 

Properties The calculus as defined enjoys the standard soundness properties: 

Theorem 3.1 (Preservation )If · ` e : τ and e ↪→ e′, then · ` e′ : τ.

Theorem 3.2 (Progress )If · ` e : τ and e 6 = v for any v, then e ↪→ e′ for some e′.The proofs are entirely standard. The calculus also has the usual technical properties. The most relevant ones for our purposes are the following: 

Lemma 3.3 (Validity )1. If Γ ` τ : Ω, then Γ ` 2.2. If Γ ` e : τ, then Γ ` τ : Ω.

Lemma 3.4 (Weakening )Let Γ′ ⊇ Γ with Γ′ ` 2.1. If Γ ` τ : κ, then Γ′ ` τ : κ.2. If Γ ` e : τ, then Γ′ ` e : τ.

Lemma 3.5 (Strengthening )Let Γ′ ⊆ Γ with Γ′ ` 2 and D = dom (Γ) \ dom (Γ′).1. If Γ ` τ : κ and fv (τ) ∩ D = /0, then Γ′ ` τ : κ.2. If Γ ` e : τ and fv (e) ∩ D = /0, then Γ′ ` e : τ.

Theorem 3.6 (Uniqueness of types and kinds )1. If Γ ` τ : κ1 and Γ ` τ : κ2, then κ1 = κ2.2. If Γ ` e : τ1 and Γ ` e : τ2, then τ1 ≡ τ2.ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 19 

Environments Γ ` 2

· ` 2

Γ ` 2 α /∈ dom (Γ)

Γ, α:κ ` 2

Γ ` τ : ΩΓ, x:τ ` 2

Types Γ ` τ : κ

Γ ` τ1 : Ω Γ ` τ2 : ΩΓ ` τ1 → τ2 : ΩΓ ` τ : Ω Γ ` 2

Γ ` { l:τ} : ΩΓ ` 2

Γ ` α : Γ(α)

Γ, α:κ ` τ : ΩΓ ` ∀ α:κ.τ : ΩΓ, α:κ ` τ : ΩΓ ` ∃ α:κ.τ : ΩΓ, α:κ ` τ : κ′

Γ ` λ α :κ.τ : κ → κ′

Γ ` τ1 : κ′ → κ Γ ` τ2 : κ′

Γ ` τ1 τ2 : κ

Terms Γ ` e : τ

Γ ` 2

Γ ` x : Γ(x)

Γ ` e : τ′ τ′ ≡ τ Γ ` τ : ΩΓ ` e : τ

Γ, x:τ ` e : τ′

Γ ` λ x:τ.e : τ → τ′

Γ ` e1 : τ′ → τ Γ ` e2 : τ′

Γ ` e1 e2 : τ

Γ ` e : τ Γ ` 2

Γ ` { l=e} : {l:τ}

Γ ` e : {l:τ, l′:τ′}

Γ ` e.l : τ

Γ, α:κ ` e : τ

Γ ` λ α :κ.e : ∀α:κ.τ

Γ ` e : ∀α:κ.τ′ Γ ` τ : κ

Γ ` e τ : τ′[τ/α]

Γ ` τ : κ Γ ` e : τ′[τ/α] Γ ` ∃ α:κ.τ′ : ΩΓ ` pack 〈τ, e〉∃α:κ.τ′ : ∃α:κ.τ′

Γ ` e1 : ∃α:κ.τ′ Γ, α:κ, x:τ′ ` e2 : τ Γ ` τ : ΩΓ ` unpack 〈α, x〉=e1 in e2 : τ

Type Equivalence τ ≡ τ′

τ ≡ ττ′ ≡ ττ ≡ τ′

τ ≡ τ′ τ′ ≡ τ′′ 

τ ≡ τ′′ 

τ1 ≡ τ′ 

> 1

τ2 ≡ τ′

> 2

τ1 → τ2 ≡ τ′ 

> 1

→ τ′

> 2

τ ≡ τ′

{l:τ} ≡ { l:τ′}

τ ≡ τ′

∀α:κ.τ ≡ ∀ α:κ.τ′

τ ≡ τ′

∃α:κ.τ ≡ ∃ α:κ.τ′

τ ≡ τ′

λ α :κ.τ ≡ λ α :κ.τ′

τ1 ≡ τ′ 

> 1

τ2 ≡ τ′

> 2

τ1 τ2 ≡ τ′ 

> 1

τ′

> 2

(λ α :κ.τ1) τ2 ≡ τ1[τ2/α]

α /∈ fv (τ)(λ α :κ.τ α ) ≡ τ

Fig. 4. Typing rules for F ωZU064-05-FPR main 30 October 2018 15:52 

## 20 Andreas Rossberg 

Reduction e ↪→ e′

(λ x:τ.e) v ↪→ e[v/x]

{l1=v1, l=v, l2=v2}.l ↪→ v

(λ α :κ.e) τ ↪→ e[τ/α]

unpack 〈α, x〉 = pack 〈τ, v〉τ′ in e ↪→ e[τ/α][ v/x]

e ↪→ e′

C[e] ↪→ C[e′]

where: (values) v :: = λ x:τ.e | { l=v} | λ α :κ.e | pack 〈τ, v〉τ

(contexts) C :: = [] | C e | v C | { l1=v, l=C, l2=e} | C.l | C τ | pack 〈τ,C〉τ | unpack 〈α, x〉=C in e

Fig. 5. Reduction rules for F ω

Finally, all judgments of the F ω type system are decidable: 

Theorem 3.7 (Decidability )1. It is decidable whether Γ ` 2.2. It is decidable whether Γ ` τ : κ.3. It is decidable whether Γ ` e : τ.4. If Γ ` τ1 : κ and Γ ` τ2 : κ, it is decidable whether τ1 ≡ τ2.

Notational Shorthands The rest of this article often deals with quantification over whole sequences α of type variables, and some other forms of lists of binders. The following (fairly standard) definitions for shortened n-ary notation will come in handy: 

∀ε.τ := τ ∃ε.τ := τ λ ε .τ := τ τ0 ε := τ0

∀α.τ := ∀α1.∀α′.τ ∃α.τ := ∃α1.∃α′.τ λ α .τ := λ α 1.λ α ′.τ τ0 τ := τ0 τ1 τ′

λ ε .e := e

λ α .e := λ α 1.λ α ′.ee ε := ee τ := e τ1 τ′

pack 〈ε, e〉∃ε.τ0 := e

pack 〈τ, e〉∃α.τ0 := pack 〈τ1,pack 〈τ′, e〉∃α′.τ0[τ1/α1]〉∃α.τ0

unpack 〈ε, x:τ〉 = e1 in e2 := let x:τ = e1 in e2

unpack 〈α, x:τ〉 = e1 in e2 := unpack 〈α1, x1〉 = e1 in unpack 〈α′, x:τ〉 = x1 in e2

let x:τ = e1 in e2 := ( λ x:τ.e2) e1

(where α = α1α′ and τ = τ1τ′)To ease notation, we often drop type annotations from let , pack , and unpack where clear from context. 

Substitution Our semantics will also make considerable use of parallel type substitutions. We write them as [τ/α], assuming that both vectors have the same arity. Sometimes we use δ to range over such substitutions. The following definitions and lemmas are relevant: 

Definition 3.8 (Typing of Type Substitutions )ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 21                                                                                                         

> (abstracted) Ξ:: =∃α.Σ
> (large) Σ:: =π|bool |[= Ξ]| { l:Σ} | ∀ α.Σ→ηΞ
> (small) σ:: =π|bool |[= σ]| { l:σ} | σ→Iσ
> (paths) π:: =α|π σ
> (purity) η:: =P|I
> Desugarings into F ω:(types)
> [= τ]:={type :τ→ {}}
> τ1→lτ2:=τ1→ { l:τ2}
> (terms)
> [τ]:={type =λx:τ.{}}
> λlx:τ.e:=λx:τ.{l:e}
> Notation: head (α):=α
> head (π σ ):=head (π)
> η≤ηη∨η:=ηη(Σ):=PP≤IP∨I:=I∨P:=Iη(∃αα .Σ):=I
> τ.l:=τ
> {l:τ, ... }.l:=τ.l′
> τ[.l=τ2]:=τ2
> {l:τ, ... }[.l=τ2]:={l:τ[.l′=τ2], ... }
> (l=ε)(l=l.l′)
> Fig. 6. Semantic Types

Let δ = [ τ/α]. We write Γ′ ` δ : Γ if and only if 1. Γ′ ` 2,2. α ⊆ dom (Γ),3. for all α ∈ dom (Γ), Γ′ ` δ α : Γ(α),4. for all x ∈ dom (Γ), Γ′ ` x : δ (Γ(x)) .

Lemma 3.9 (Type Substitutions )Let Γ′ ` δ : Γ. Then: 1. If Γ ` τ : κ, then Γ′ ` δ τ : κ.2. If Γ ` e : τ, then Γ′ ` δ e : δ τ .

4 Type System and Elaboration 

The general recipe for 1ML ex is simple: take the semantics from F-ing modules (Rossberg 

et al. , 2014), collapse the levels of modules and core, and impose the predicativity restric-tion needed to maintain decidability. This requires surprisingly few changes to the whole system. 

4.1 Semantic Types 

The entire semantics is defined by elaborating 1ML ex types and terms directly into “equiv-alent” types and terms of System F ω as given in the previous section. However, 1ML types do not translate to arbitrary F ω types – instead, they map to types of very specific shape. The grammar of these semantic types is given in Figure 6 (“semantic” as opposed to the “syntactic” types of the surface language which they model). To avoid clutter, we omit all ZU064-05-FPR main 30 October 2018 15:52 

## 22 Andreas Rossberg 

kind annotations on type variable binders. Where needed, we use the notation κα to refer to the kind implicitly associated with α.Semantic types are the essence of the F-ing elaboration. To understand them, it is prob-ably best to walk through a few explanatory examples that elaborate a concrete 1ML type 

T into a System F ω type τ, a relation we write T τ.

• { x : bool, y : int } {x : bool , y : int }

Elaboration will translate this syntactic type into the semantic type of the same shape. So records map to records, which should be no surprise. We assume an implicit injection from 1ML identifiers X into F ω labels l (and variables x), so we can conveniently treat any 

X as a label (or variable). 

• { t : (= type bool); u : (= type t); x : t, y : u }

{t : [= bool ], u : [= bool ], x : bool , y : bool }

Structurally, the elaborated type still looks almost like the original, except that all refer-ences to the transparent type specifications are replaced with their definitions. Of course, one may (and should!) wonder what this “ [= τ]” is that represents transparent types. Because we keep saying that semantic types are just System F types, but this does not look like one. The answer can be found in Figure 6: it is simply a notational abbreviation that is encoded into bare System F. Its expansion does not actually matter much, it is merely a coding trick. All that matters is that it is a form of type that (1) uniquely determines τ,and (2) is inhabited by a term that also uniquely determines τ. A function fits the bill. 10 

To make the encoding unambiguous, it is wrapped into a record type with a unique label “type ” that we assume to be a reserved name disjoint from all valid 1ML identifiers. 

• { t : type ; u : (= type t); x : t; y : u }

∃α.{t : [= α], u : [= α], x : α, y : α}

This type is almost the same as before except that t now is an abstract type. The example demonstrates the main trick of elaboration: it inserts appropriate quantifiers to bind abstract types. Following Mitchell & Plotkin (1988), abstract types are represented by existentials. The type variable α provides a “semantic” name for t, and all references to t are replaced by α. This includes the specification of t itself, which can now be viewed as being trans-parently equal to α. The upshot is that all reified types, whether transparent or opaque, are represented in a uniform manner. It also removes any dependency between fields of the record type – key to elaborating into bare System F without dependent types. 

• { A : {t : type }; B : {u : type ; x : A.t }; y : B.u }

∃αβ .{A : {t : [= α]}, B : {u : [= β ], x : α}, y : β }

This one shows the handling of nested abstract types: inner quantifiers are collectively hoisted out of records. In particular, this makes them scope over the remainder of any enclosing record, which allows us to reference the type variable across subcomponents –       

> 10 Because all type constructors are separately represented as “functors” in 1ML, we have no need for types of higher kind in this notation, as opposed to Rossberg et al. (2014). ZU064-05-FPR main 30 October 2018 15:52

1ML – Core and modules united 23 

such as A.t and B.u in the example. A type may have arbitrarily many abstract components, which all accumulate in an outermost quantifier. Accordingly, the grammar of semantic types defines an abstracted type Ξ = ∃α.Σ that quantifies over all the abstract types (i.e., components of type type ) from the underlying 

concretised type Σ, by naming them α. Σ itself contains no existential quantifiers – except as part of function types. So let us move to functions then. 

• (t : type ) → { u : type ; x : t, y : u }

∀α.[= α] →I ∃β .{u : [= β ], x : α, y : β }

Conceptually, all function types map to polymorphic functions in F ω . Being in negative position, the quantifier for the abstract types from the parameter (here α) turns into a universal quantifier. It scopes over the whole arrow type and thereby allows the codomain to refer to it. Like for nested records, this hoisting avoids the need for dependent types. For an impure function type like the above, the abstract types in the result are encapsu-lated by a local existential quantifier. It binds all those types that will be “generated” when applying the function. This representation of generative functor types as System F types of the form ∀α.Σ1 → ∃ β .Σ2 is due to Russo (1999; 2003), and another central ingredient of the F-ing modules semantics. Arrow types are further annotated by a simple effect η, which distinguishes impure ( →I)from pure ( →P) function types. Again, this syntax is encoded into bare F ω types with a little record trick, see Figure 6 (we assume that record labels used with this form do not overlap with other labels). 

• (t : type ) ⇒ { u : type ; x : t; y : u }

∃β .∀α.[= α] →P {u : [= β α ], x : α, y : β α }

This example shows the pure variant of the previous function type. Because it does not generate types at applications time, the existential quantifier changes position in the F ω

translation: pure function types encode applicative semantics for the abstract types they return by having their existential quantifiers (here for β ) “lifted” over their parameters. Their general form is ∃β .∀α.Σ1 → Σ2. Conceptually, the abstract types are generated when the function is defined , not when it is applied. We impose the syntactic invariant that a pure function type ( →P) never has an existential quantifier immediately right of the arrow, i.e., always has shape Σ1 →P Σ2.However, the representation of an abstract type returned by a function may depend on the function’s parameters. To capture any potential dependencies, the β in a pure function type are skolemised over α (Biswas, 1995; Russo, 2003; Rossberg et al. , 2014). That is, the kinds of β are of the form κα → κ, which is where higher kinds come into play. In return, all their occurrences are applied to α. In the concrete example, the kind of the type variable β for u hence is Ω → Ω, and all its references are of the form β α , thereby saturating any use of a type constructor and making sure that they all yield kind Ω. Once the function is applied to a concrete type, say τ, the parameter variable α is substituted, and all occurrences will have the form β τ .

• { t : type ⇒ type ; x : t int; y : t bool }

∃β .{t : ∀α.[= α] →P [= β α ], x : β int , y : β bool }ZU064-05-FPR main 30 October 2018 15:52 

## 24 Andreas Rossberg 

Pure functions over type type readily subsume abstract type constructors. As we will see in a short while, elaborating the application (t int) in the above example substitutes int 

for α in β α and results in a value of semantic type [= β int ] – which is the representation of the syntactic type (= type t int) . Hence, the types of x and y in the example have the desired meaning. We call the general form of abstract type variables applied to parameters semantic paths ,11 ranged over by π. Parameters are (only) introduced through pure function ab-straction and the aforementioned kind raising that goes with it. In general, an abstract type that is the result of an application of a pure function F to a value M is represented by the application of the higher-kinded type variable representing the constructor to the concrete types σ M from the argument, like the type β int in the example. Because we enforce predicativity, these argument types have to be small. Figure 6 defines small types as a subgrammar σ of the general semantic types Σ. The central difference is that small types cannot contain quantifiers. Moreover, small function types are required to be impure, which will simplify type inference (Section 7). A summary of the mapping between syntactic types T and semantic types Ξ is as follows: 

T ∃α.Σ

(= type T1) [= ∃α1.Σ1]

type ∃α.[= α]

{X1:T1;X2:T2} ∃α1α2.{X1:Σ1, X2:Σ2}

(X:T1) → T2 ∀α1.Σ1 →I ∃α2.Σ2

(X:T1) ⇒ T2 ∃α2.∀α1.Σ1 →P Σ2

A.t αA.t F( M) αF( ) σ M

Here, we assume that each constituent type Ti on the left-hand side is recursively mapped to a corresponding ∃αi.Σi appearing on the right-hand side. Note that all semantic types are F ω types of kind Ω, even those that are the equivalent of higher kinds, such as type ⇒ type . This type will elaborate into the polymorphic function 

∃α2.∀α1.[= α1] → [= α2 α1], where the higher-kindedness is manifest only in the kind of the “output” type variable α2.

4.2 Elaboration 

The elaboration rules for 1ML ex are collected in Figures 7 and 8. There is one judgement for each syntactic class with the following regular structure: 

Γ ` T Ξ Γ ` E :η Ξ e

Γ ` D Ξ Γ ` B :η Ξ e   

> 11 Because they are the semantic analog to syntactic paths like F(M).t that appear in some previous type systems for higher-order modules (Leroy, 1995)

ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 25 

Types Γ ` T Ξ

Γ ` E :P [= Ξ] e

Γ ` E Ξ TPATH κα = ΩΓ ` type ∃α.[= α] TTYPE 

Γ ` bool bool TBOOL Γ ` D ΞΓ ` {D} Ξ TSTR 

Γ ` T1 ∃α1.Σ1

Γ, α1, X:Σ1 ` T2 ∃α2.Σ2

Γ ` (X:T1) → T2 ∀α1. Σ1 →I ∃α2.Σ2

TFUN 

Γ ` T1 ∃α1.Σ1

Γ, α1, X:Σ1 ` T2 ∃α2.Σ2 κα′ 

> 2

= κα1 → κα2

Γ ` (X:T1) ⇒ T2 ∃α′

> 2

.∀α1. Σ1 →P Σ2[α′ 

> 2

α1/α2] TPFUN 

Γ ` E :P Σ e E = E′:>T ∨ E = E′:T ∨ E = type T

Γ ` (= E) Σ TSING 

Γ ` T1 ∃α1.Σ1 α1 = α11 ] α12 

Γ ` T2 ∃α2.Σ2 Γ, α11 , α2 ` Σ2 ≤α12 Σ1.X δ ; f

Γ ` T1 where (. X:T2) ∃α11 α2.δ Σ1[.X=Σ2] TWHERE 

Declarations Γ ` D Ξ

Γ ` T ∃α.ΣΓ ` X:T ∃α.{X:Σ} DVAR Γ ` T ∃α.{X:Σ}

Γ ` include T ∃α.{X:Σ} DINCL 

Γ ` D1 ∃α1.{X1:Σ1}

Γ, α1, X1:Σ1 ` D2 ∃α2.{X2:Σ2} X1 ∩ X2 = /0

Γ ` D1;D2 ∃α1α2.{X1:Σ1, X2:Σ2} DSEQ Γ ` ε {} DEMPTY 

Subtyping Γ ` Ξ′ ≤π Ξ δ ; fΓ ` Ξ ≤ Ξ′ f := Γ ` Ξ ≤ε Ξ′ id; f

Γ ` π ≤ π λ x.x SPATH Γ ` bool ≤ bool λ x.x SBOOL 

Γ ` Ξ′ ≤ Ξ f Γ ` Ξ ≤ Ξ′ f ′

Γ ` [= Ξ′] ≤ [= Ξ] λ x.[Ξ] STYPE π = α α ′

Γ ` [= σ ] ≤π [= π] [λ α ′.σ /α]; λ x.x SFORGET 

Γ ` { l:Σ′} ≤ {} λ x.{} SEMPTY 

Γ ` Σ′ 

> 1

≤π1 Σ1 δ1; f1

Γ ` { l′:Σ′} ≤ π2 {l: δ1Σ} δ2; f2 δ2Σ1 = Σ1

Γ ` { l1:Σ′

> 1

, l′:Σ′} ≤ π1π2 {l1:Σ1, l:Σ} δ1δ2; λ x.{l1= f1(x.l1), l=( f2 x).l} SSTR 

Γ, α ` Σ ≤α′ Σ′ δ1; f1 η′ ≤ η

Γ, α ` δ1Ξ′ ≤πα Ξ δ2; f2 δ2Σ = ΣΓ ` (∀α′.Σ′ →η′ Ξ′) ≤π (∀α.Σ →η Ξ) δ2; λ x. λ α . λη y:Σ. f2 (( x (δ1α′) ( f1 y)) .η′) SFUN 

Γ, α′ ` Σ′ ≤α Σ δ ; f α′α 6 = ε

Γ ` ∃ α′.Σ′ ≤ ∃ α.Σ λ x.unpack 〈α′, y〉 = x in pack 〈δ α , f y 〉 SABS 

Fig. 7. Elaboration of 1ML ex types ZU064-05-FPR main 30 October 2018 15:52 

## 26 Andreas Rossberg 

Expressions Γ ` E :η Ξ e

Γ(X) = ΣΓ ` X :P Σ X EVAR Γ ` T ΞΓ ` type T :P [= Ξ] [Ξ] ETYPE 

Γ ` true :P bool true ETRUE Γ ` false :P bool false EFALSE 

Γ ` X :P bool e Γ ` E1 :η1 Ξ1 e1 Γ ` Ξ1 ≤ Ξ f1

Γ ` T Ξ Γ ` E2 :η2 Ξ2 e2 Γ ` Ξ2 ≤ Ξ f2

Γ ` if X then E1 else E2 : T :η1∨η2∨η(Ξ) Ξ if e then f1 e1 else f2 e2

EIF 

Γ ` B :η Ξ e

Γ ` {B} :η Ξ e ESTR Γ ` E :η ∃α.{X′:Σ′} e X:Σ ∈ X′:Σ′

Γ ` E.X :η ∃α.Σ unpack 〈α, y〉 = e in pack 〈α, y.X〉 EDOT 

Γ ` T ∃α.Σ Γ, α, X:Σ ` E :η Ξ e

Γ ` fun (X:T ) ⇒E :P ∀α. Σ →η Ξ λ α .λη X:Σ.e EFUN 

Γ ` X1 :P ∀α. Σ1 →η Ξ e1

Γ ` X2 :P Σ2 e2 Γ ` Σ2 ≤α Σ1 δ ; f

Γ ` X1 X2 :η δ Ξ (e1 (δ α ) ( f e 2)) .η EAPP 

Γ ` X :P Σ1 e Γ ` T ∃α.Σ2 Γ ` Σ1 ≤α Σ2 δ ; f

Γ ` X:>T :η(∃α.Σ2) ∃α.Σ2 pack 〈δ α , f e 〉 ESEAL 

Bindings Γ ` B :η Ξ e

Γ ` E :η ∃α.Σ e

Γ ` X=E :η ∃α.{X:Σ} unpack 〈α, x〉 = e in pack 〈α, {X=x}〉 BVAR 

Γ ` E :η ∃α.{X:Σ} e

Γ ` include E :η ∃α.{X:Σ} e BINCL Γ ` ε :P {} {} BEMPTY 

Γ ` B1 :η1 ∃α1.{X1:Σ1} e1 X′ 

> 1

= X1 − X2

Γ, α1, X1:Σ1 ` B2 :η2 ∃α2.{X2:Σ2} e2 X′

> 1

:Σ′ 

> 1

⊆ X1:Σ1

Γ ` B1;B2 :η1∨η2 ∃α1α2.{X′

> 1

:Σ′

> 1

, X2:Σ2} unpack 〈α1, y1〉 = e1 in let X1 = y1.X1 in unpack 〈α2, y2〉 = e2 in pack 〈α1α2, {X′ 

> 1

= y1.X′

> 1

, X2 = y2.X2}〉 

BSEQ 

Fig. 8. Elaboration of 1ML ex expressions 

In addition, there is an additional judgement defining subtyping over semantic types: 

Γ ` Ξ1 ≤π Ξ2 δ ; f

The rules may seem a bit intimidating at first, especially those for expressions and sub-typing. But do not despair: that is only because elaboration defines both static semantics (typing) and dynamic semantics (operational meaning) at the same time. The latter is encapsulated in the greyed parts like “ e”, and defines what System F term a construct translates to. A reader who is merely interested in typing 1ML can completely ignore those grey parts in all rules – just squint and make them disappear. 

Types and Declarations The elaboration rules for types implement the translation scheme we laid out in the previous section. Their main job is to name all abstract type components with type variables, collect them, and bind them hoisted to an outermost existential (or ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 27 

universal, in the case of functions) quantifier. The rules are mostly identical to F-ing modules, except that type is a free-standing construct instead of being tied to the syntax of bindings, and 1ML’s “ where ” construct is slightly more general. Most notable are the following rules. Using an expression E as a type path requires that E is pure and has a type of the form 

[= Ξ]. It denotes the very type Ξ – which may be anything from an abstract type variable to a large type (rule T PATH ). Function types have separate rules for impure (generative) functions (T FUN ) and pure (applicative) ones (T PFUN ). As explained above, pure function types have the existential quantifier for the α2 from the codomain lifted over the parameters, skolemising them accordingly. Rule T SING handles “singleton” types. It corresponds to rule S-LIKE in Rossberg et al. (2014), except that we restrict it to expressions with explicit types, in order to mesh well with type inference later (where it would not otherwise denote a unique type). In return, we can drop the former side condition requiring Σ to be explicit . The rule simply infers the (unique) type 

Σ of the pure expression E. Note that this type is not allowed to have existential quantifiers, i.e., E may not introduce local abstract types. All types occurring in Σ thus are transparent. The most complex rule is T WHERE . Unlike in conventional ML, where the where 

construct simply concretises one (or several) types via substitution, we allow it to specialise an arbitrary subcomponent of T1 to an arbitrary subtype. The original semantic type of that subcomponent, denoted by Σ1.X in the rule, is replaced by the semantic interpretation of 

T2, written Σ1[.X = Σ2] (both these notations are defined in Figure 6). If T2 defines its own abstract types α2 then they are added to the list. At the same time, it may remove some of the abstract types α1 from the original type. To this end, α1 is partitioned into types α11 that remain abstract and α12 that are made concrete by the refinement (or just replaced by some of the α2). The last premise checks that Σ2 indeed matches Σ1.X, using the subtyping judgement explained below. This yields a substitution δ for eliminating the previously abstract types α12 . The remaining α11 are left abstract, so their quantifiers are kept. As a rule of thumb, any 1ML ex type with an occurrence of type type will elaborate to a large type, unless this abstact type is refined to something concrete using the where form. Any type without the use of type type and no reference to another large type will denote a small type. 

Expressions and Bindings The elaboration of expressions closely follows the rules from the first part of Rossberg et al. (2014), but adds the tracking of purity as in Section 7 of that paper. However, to keep the current article simple, we left out the ability to perform pure sealing, or to create pure functions around it – that avoids some of the notational contortions necessary for a relaxed applicative functor semantics. The only other non-editorial change over F-ing modules – apart from the addition of Boolean expression forms – is that as for types, “ type T ” is now handled as a first-class value, no longer tied to bindings. The rules assign effects η and semantic types Ξ to 1ML expressions or bindings, and at the same time translate them to corresponding terms e of System F ω that define the operational semantics of 1ML. It is an invariant of the judgement that e has type Ξ in System F ω .ZU064-05-FPR main 30 October 2018 15:52 

## 28 Andreas Rossberg 

As we saw before, the main trick in interpreting 1ML’s module-like types is introducing quantifiers for abstract types. That is reflected in the typing of expressions: an expression that defines new abstract types will have an “abstracted” semantic type Ξ with existential quantifiers, one quantifier for each new type. When such an expression is nested into a larger expression then the rules have to propagate these quantifiers accordingly. For example, for a projection E.x to be well-typed, E obviously needs to have a type of the form {x : Σ, . . . }; the resulting type would be Σ then. However, if E creates abstract types locally, then its type will be of the form ∃α.{x : Σ, . . . } instead. The central idea taken from F-ing modules is to handle such types implicitly by extruding the existential quantifier automatically: that is, the projection E.x is well-typed and assigned type ∃α.Σ,with the same sequence of quantifiers. And so on for other constructs. On the term level, that corresponds to repeated unpacking and repacking of the respective existentials. Moreover, the sequencing rule B SEQ combines two ( n-ary) existentials into one – and is the only rule that does so, because the kernel syntax allows only variables in most places; the derived forms from Figure 1 all desugar into uses of sequencing. For the categorically inclined, the existential quantifiers in an expression’s type Ξ act like an implicit monad of “abstraction effects”. There is no way to “escape” this monad: the sequencing rule B SEQ acts like its bind operator, and the only construct to suspend it is functional abstraction (rule E FUN ). The only rules that effectively “run” such a monad are the type formation rules T PATH and T SING , and they require the abstraction effects to be encapsulated in the expression (i.e., no abstract types escape). 12 

It is another invariant of the expression elaboration judgement that η = I in all cases where Ξ does not degenerate into a concrete type Σ with empty (i.e., no) quantifier – in other words, abstract type “generation” is indeed impure. Without this invariant, rule E FUN 

might form an invalid function type that is marked pure but yet has an inner existential quantifier (i.e., is “generative”). To maintain the invariant, both sealing (rule E SEAL ) and conditionals (rule E IF ) have to be deemed impure if they generate abstract types – enforced by the notation η(Ξ) defined in Figure 6. In that sense, our notion of purity actually corresponds to the stronger property of valuability in the parlance of Dreyer (2005), which also implies phase separation , i.e., the ability to separate static type information from dynamic computation, key to avoiding the need for dependent types. 

Subtyping In two places expression typing uses subtyping: for function application (rule EAPP ) and for sealing (rule E SEAL ). Subtyping is like signature matching for ML modules: it allows not only for width subtyping on records, it can also substitute concrete definitions for abstract types. It is through that property, that the two occurrences of subtyping sub-sume universal elimination and existential introduction. The subtyping judgement is defined on semantic types. It computes a substitution δ for the matched abstract types from the right-hand side, and it generates a coercion function f

as computational evidence of the subtyping relation. The domain of that function always     

> 12 More precisely, we actually have an infinite family of monads – one for each possible sequence of variable kinds – and the bind operator is heterogeneous, yielding the composition of two monads with composition being just nesting. See Rossberg (2016) for a more extensive discussion. ZU064-05-FPR main 30 October 2018 15:52

1ML – Core and modules united 29 

is the left-hand type Ξ′; to avoid clutter, we omit its explicit annotation from the λ -terms produced by the rules. The rules mostly follow the structure from F-ing modules, merely adding a straightforward rule for abstract type paths π (rule S PATH ), because those can now occur as “module types”. However, we make one structural change: instead of guessing the substitution δ non-deterministically in a separate rule (rule U-MATCH in Rossberg et al. (2014)), the current formulation looks them up algorithmically as it goes, using the new rule S FORGET to match an individual abstract type. The reason for this change is merely a technical one: it elim-inates the need for any significant meta-theory about decidability, which was somewhat non-trivial with the non-determinism before, at least with applicative functors. To this end, the judgement is indexed by a vector π of abstract paths that correspond to the abstract types from the right-hand Ξ. The counterparts of those types have to be looked up in the left-hand Ξ′, which happens one at a time in the rule S FORGET . Those lookups incrementally produce the substitution δ whose domain corresponds to the (root variables of) the abstract paths π. Substitutions are combined in rule S STR , where the vector of type paths is partitioned over the record components as needed. Let us look at a couple of examples. When matching {type t = bool; v : t } against 

{type t; v : t } then first, these types elaborate into {t : [= bool ], v : bool } and ∃α.{t :

[= α], v : α}, respectively. The subtyping judgement then is invoked with an empty path at first, i.e., checking {t : [= bool ], v : bool } ≤ ε ∃α.{t : [= α], v : α}. Rule S ABS would first eliminate the quantifier and move the variable to the list of paths, thereby invoking 

{t : [= bool ], v : bool } ≤ α {t : [= α], v : α}. After applying rule S STR this would arrive at matching the structure component t via [= bool ] ≤α [= α]. That is where rule S FORGET 

fires, because the path matches the right-hand side. It produces the substitution [bool /α],under which the remainder of the structure can be matched successfully. 13 

When matching a type with multiple abstract type components, e.g., ∃α1α2.{t : [= 

α1], u : [= α2], v : α2 → α1}, then it proceeds similarly, but with a list of paths α1, α2 that is then split up by rule S STR . Individual applications of S FORGET yield separate substitutions for each type component which S STR composes on the way back. Hence, normally, each path in π is just a plain abstract type variable that occurs free in 

Ξ. But as we saw in the formation rule T PFUN for pure function types, lifting produces more complex paths. So when subtyping goes inside a pure functor in rule S FUN , the same abstract paths with skolem parameters have to be formed for lookup, so that rule S FORGET 

can match them accordingly. For example, matching (a : type ) ⇒ (= type a) against 

(a : type ) ⇒ type translates to ∀α′.[= α′] →P [= α′] ≤ ∃ β .∀α.[= α] →P [= β α ] with 

κβ = Ω → Ω. Via rule S ABS , this would try to match ∀α′.[= α′] →P [= α′] ≤β ∀α.[= 

α] →P [= β α ], which involves looking up the higher-kinded β . After contra-variantly matching the function parameters, the second premise of rule S FUN then traverses into the functions’ codomains with path β α , trying to match [= α] ≤(β α ) [= β α ]. And indeed, that is the only way for S FORGET to “find” the path and yield δ = [ λ α .α/β ].      

> 13 Unlike the more declarative formulation in F-ing modules (2014), but similar to the subtyping algorithm of Leroy (1996), these rules rely on the invariant that semantic signatures {l:Σ}are ordered, such that the label that is “binding” an abstract type always appears before any of the type’s uses. This is sufficient for 1ML, but would not scale to recursive modules, for example. ZU064-05-FPR main 30 October 2018 15:52

## 30 Andreas Rossberg 

We assume that applying substitutions implicitly performs β η -normalisation. Because all type applications in semantic paths are saturated, no type lambdas remain in a semantic type after applying a substitution. No types can actually be looked up from under an(other) abstracted type Ξ with non-empty quantifier – because π is required to be empty when entering rule S ABS . Hence, for any subtyping derivation Ξ′ ≤π Ξ, it is either the vector π that is empty, or the quantifiers of both Ξ and Ξ′. Either case can actually occur when invoking the second premise of rule SFUN , depending on whether the function types are pure or not. The side conditions of the form δ Σ = Σ in rules S STR and S FUN enforce that no variables in the domain of δ occur in Σ (under the usual freshness assumptions for bound variables). That in turn ensures that all abstract variables are properly scoped, i.e., do not occur before a “definitional” occurrence in a type of the form [= π] that allows us to look them up. Finally, we note that rule S FORGET is the single place in the whole set of 1ML typing rules where the predicativity restriction materialises: the rule allows only a small type σ

on the left, so that only small types can end up in the image of the substitution δ .

4.3 Meta-Theory 

It is relatively straightforward to verify by induction that elaboration is correct, i.e., pro-duces only well-formed F ω -objects: 

Proposition 4.1 (Correctness of 1ML ex Elaboration )Let Γ ` 2.1. If Γ ` T /D Ξ, then Γ ` Ξ : Ω.2. If Γ ` E/B :η Ξ e, then Γ ` e : Ξ, and if η=P then Ξ=Σ.3. If Γ ` Ξ′ ≤αα ′ Ξ δ ; f and Γ ` Ξ′ : Ω and Γ, α ` Ξ : Ω, then dom (δ ) = α and 

Γ ` δ : Γ, α and Γ ` f : Ξ′ → δ Ξ.Together with the standard soundness result for System F ω we can tell that 1ML ex is sound, i.e., a well-typed 1ML ex program will either diverge or terminate with a value of the right type. With the bare definition of 1ML ex we have given divergence cannot even arise, but a more complete ML-like language will surely have it. 

Theorem 4.2 (Soundness of 1ML ex )If · ` E : Ξ e, then either e ↑ or e ↪→∗ v such that · ` v : Ξ.More interestingly, the 1ML ex type system is also decidable: 

Theorem 4.3 (Decidablity of 1ML ex Elaboration )All 1ML ex elaboration judgements are decidable. This is immediate for all but the subtyping judgement, since they are syntax-directed and inductive, with no complicated side conditions. The rules can be read directly as an inductive algorithm. The one odd case is rule T WHERE , where it seems necessary to find a partitioning α1 = α11 ] α12 , but it is not hard to see that the subtyping premise can only possibly succeed when picking α12 = fv (Σ1.X) ∩ α1.ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 31 

The only tricky judgement is subtyping. Although it is syntax-directed as well, the rules are not actually inductive: some of their premises apply a substitution δ to the inspected types. Alas, that is exactly what can cause undecidability (see Section 1.2). The restriction to substituting small types saves the day. With that, we can define a weight metric over semantic types such that a quantified type variable has more weight than any possible substitution of that variable with a small type . Because the subtyping rules always remove quantifiers before applying a substituion, the overall weight of types involved decreases in all subtyping rules. One suitable choice of weight functions is mapping to ordered pairs as follows: 

W [[ Ξ]] = 〈Q[[ Ξ]] , S[[ Ξ]] 〉

Q[[ bool ]] = 0

Q[[ α]] = 0

Q[[ π σ ]] = 0

Q[[ λ α .σ ]] = 0

Q[[[= Ξ]]] = 2 · Q[[ Ξ]] 

Q[[ {} ]] = 0

Q[[ {l0:Σ0, l:Σ}]] = Q[[ Σ0]] + Q[[ {l:Σ}]] 

Q[[ ∀α.Σ →η Ξ]] = |α| + Q[[ Σ]] + Q[[ Ξ]] 

Q[[ ∃α.Σ]] = |α| + Q[[ Σ]] 

S[[ bool ]] = 1

S[[ α]] = 1

S[[ π σ ]] = S[[ π]] + S[[ σ ]] + 1

S[[ λ α .σ ]] = S[[ σ ]] + 1

S[[[= Ξ]]] = S[[ Ξ]] + 1

S[[ {} ]] = 1

S[[ {l0:Σ0, l:Σ}]] = S[[ Σ0]] + S[[ {l:Σ}]] + 1

S[[ ∀α.Σ →η Ξ]] = S[[ Σ]] + S[[ Ξ]] + 1

S[[ ∃α.Σ]] = S[[ Σ]] 

The definitions assume β η -normal form; in the case of paths and structures, they are inductive over the vector of arguments and components, respectively. Intuitively, the first component of a weight pair, Q[[]] , measures the number of quantifiers – or more precisely, the number of quantifiers that need to be eliminated in the subtyping rules, thus the seemingly odd definition for the case Q[[[= Ξ]]] . The second component, S[[]] ,is the actual syntactic size of the type expression. We apply addition point-wise to weights 

W [[]] , and impose a lexicographic ordering on them: 

〈q, s〉 + 〈q′, s′〉 := 〈q + q′, s + s′〉〈q, s〉 < 〈q′, s′〉 :⇔ q < q′ ∨ (q = q′ ∧ s < s′)

The most important property of this definition of weights is that Q[[ σ ]] = 0 for all small types σ , because small types do not contain quantifiers. Consequently, any large type will have more weight then even the biggest small type. We extend the notion of small type to (higher-order) type constructors and substitutions: a type constructor is small if it is of the form λ α .σ ; a substitution δ is small if δ (α) is small for all α. Then: 

Lemma 4.4 (Weight Reduction under Small Substitution )Let δ be a small substitution. 1. Q[[ δ Ξ]] = Q[[ Ξ]] .2. W [[ δ Ξ]] < W [[ Ξ]] + 〈1, 0〉.3. W [[ δ Ξ]] ≤ W [[ Ξ]] + 〈| dom (δ )|, 0〉.In more prose, the first property shows that substitution does not change the number of quantifiers; consequently, the second says that eliminating a quantifier is a strictly larger weight reduction then performing a substitution; and the third says that eliminating a ZU064-05-FPR main 30 October 2018 15:52 

## 32 Andreas Rossberg 

Syntax (types) T :: = . . . | wrap T                              

> (expressions) E:: =. . . |wrap X:T|unwrap X:T
> Abbreviations: wrap E:T:=let X=Ein wrap X:T
> unwrap E:T:=let X=Ein unwrap X:T

Semantic Types (large) Σ :: = . . . | [Ξ]              

> (small) σ:: =. . . |[Ξ]
> Desugarings: (types)
> [Ξ]:={val :Ξ}
> (terms)
> [e]:={val =e}

Types Γ ` T ΞΓ ` T ΞΓ ` wrap T [Ξ] TWRAP 

Expressions Γ ` E :η Ξ e                                              

> Γ`X:PΣeΓ`T[Ξ]Γ`Σ≤Ξf
> Γ`wrap X:T:P[Ξ][f e ]EWRAP
> Γ`X:P[Ξ′]eΓ`T[Ξ]Γ`Ξ′≤Ξf
> Γ`unwrap X:T:η(Ξ)Ξf(e.val )EUNWRAP

Subtyping Γ ` Ξ′ ≤ Ξ δ ; f        

> Γ`[Ξ]≤[Ξ]λx:[Ξ].xSWRAP
> Fig. 9. Extending 1ML ex with Impredicativity

sequence of quantifiers via substitution is a weight reduction or at least keeps the weight unchanged. Note how this lemma crucially relies on δ being small. The properties are essential in proving the case of rule S FUN for the termination lemma: 

Lemma 4.5 (Termination of Algorithmic Subtyping )Let Γ ` Ξ′ : Ω and Γ, α ` Ξ : Ω and π = α α ′. Then Γ ` Ξ′ ≤π Ξ δ ; f terminates. The proof is by case analysis on the algorithm. In each rule, the weight W [[ Ξ′]] + W [[ Ξ]] + 

〈| π|, 0〉 gets strictly smaller for each premise: either its Q component shrinks, because a quantifier is peeled, or its S, because the structure is otherwise simplified. In particular, Q

shrinks in all cases where a substitution δ is applied in a premise and S increases. 

5 Expressiveness 

5.1 Impredicativity Reloaded 

Some readers will think that predicativity is a rather severe restriction. And they are right. So it is worth asking: Can we (re)enable impredicative type abstraction without breaking decidability? ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 33 

Yes we can. One possibility is the common trick of piggy-backing datatypes: we could allow their data constructors to have large parameters. Because datatypes are nominal 

in ML, impredicativity is “hidden away” and does not interfere with subtyping, thereby avoiding the issue described in Section 1.2. Here, we suggest a more orthogonal solution, namely introducing structural impredica-tive types. Figure 9 reveals how they can be defined as an easy extension to 1ML ex and the rules we have previously given. The trick is that a large type has to be injected into the universe of small types explicitly ,by way of a special type “ wrap T ” (not entirely dissimilar from the bracketted polytypes that occur in the semi-explicit first-class polymorphism of Garrigue & R´ emy (1999)). Semantically, this type is represented by a new form “ [Ξ]” (with the now familiar coding trick of marking it through a special record) that may appear as a small type even when the inner type is large. The new type comes with respective expression forms for introducing and eliminating it. The elaboration rules for wrapped types and expressions are straightforward. The crux of this approach is that subtyping does not extend to wrapped types (rule S WRAP ): a wrapped type can only be matched by an equivalent type, not a subtype. This way, any infinite recursion is avoided; the weight function for the termination proof (Section 4.3) can trivially be extended to the new form of wrapped type as follows: 

Q[[[ Ξ]]] = 0 S[[[ Ξ]]] = 1That goes through because S WRAP is simply an axiom, i.e., always a leaf node in any subtyping derivation. The syntax we chose for wrapped types is reminiscent of packaged modules (Sec-tion 1.1) and indeed the construct is practically identical to the packaged modules defined for F-ing modules (Rossberg et al. , 2014). However, it has far more specialised use cases in 1ML. In particular, wrapping is never needed if one merely wants to abstract over a value 

that has a large type (as is the case with packaged modules). It is only needed in the rarer case 14 where one wants to abstract over something that is a large type – and thus has a type that lies outside the universe of large types. Wrapping embeds the universe of large types back into the universe of small types, for the price of losing subtyping. As an example, consider a Church encoding of the option type:                  

> type OPT =
> {
> type opt a none a : opt a some a : a →opt a caseopt a b : opt a →b→(a →b) →b
> }
> Opt :>OPT =
> 14 From the module perspective, this case corresponds to what would be the use of an abstract module type in OCaml, something that is virtually nonexistent in the wild. However, OCaml also allows introducing impredicativity on the core level, e.g. by instantiating a polymorphic function to an object type that has a polymorphic method.

ZU064-05-FPR main 30 October 2018 15:52 

## 34 Andreas Rossberg 

(kinds) 

[[ Ω]] = type 

[[ κ1 → κ2]] = [[ κ1]] ⇒ [[ κ2]] 

(types) 

[[ α]] = Xα

[[ τ1 → τ2]] = type ([[ τ1]] → [[ τ2]] )

[[ τ1 × τ2]] = type ([[ τ1]] × [[ τ2]] )

[[ ∀α:κ.τ]] = type (wrap (( Xα : [[ κ]] ) ⇒ [[ τ]] )) 

[[ ∃α:κ.τ]] = type (wrap (( Xα = [[ κ]] ) × [[ τ]] )) 

[[ λ α :κ.τ]] = fun (Xα : [[ κ]] ) ⇒ [[ τ]] [[ τ1 τ2]] = [[ τ1]] [[ τ2]] 

(expressions) 

[[ x]] = Xx

[[ λ x:τ.e]] = fun (Xx : [[ τ]] ) ⇒ [[ e]] [[ e1 e2]] = [[ e1]] [[ e2]] [[ 〈e1, e2〉]] = ([[ e1]] , [[ e2]] )

[[ e.i]] = [[ e]] .i

[[ λ α :κ.e]] = wrap (fun (Xα : [[ κ]] ) ⇒ [[ e]] ) : ( Xα : [[ κ]] ) ⇒ [[ τe]] [[ e1 τ2]] = (unwrap [[ e1]] : [[ τe1 ]] ) [[ τ2]] [[ 〈τ1, e2〉τ ]] = wrap ([[ τ1]] , [[ e2]] ) : [[ τ]] [[ unpack 〈α, x〉=e1 in e2]] = let (Xα , Xx) = unwrap [[ e1]] : [[ τe1 ]] in [[ e2]] 

where: 

(X = T1) × T2 := { 1 : T1; 2 : let X = 1 in T2}

(E1, E2) := { 1 = E1; 2 = E2}

E.i := E. i

let (X1, X2) = E1 in E2 := let X = E1; X1 = X. 1; X2 = X. 2 in E2

Fig. 10. Embedding of F ω in 1ML 

{

type opt a = wrap ((b : type ) ⇒ b → (a → b) → b) none a = wrap (fun b (n : b) (s : a → b) ⇒ n) : opt a some a (x : a) = wrap (fun b (n : b) (s : a → b) ⇒ s x) : opt a caseopt a b (o : opt a) = ( unwrap o : opt a) b 

}

The representation of opt is a large type, so it has to be wrapped in order to “make it small” and allow matching its abstract declaration in the signature. 

5.2 Embedding F ω

The elaboration of 1ML ex embeds the language into System F ω , showing that it is no more expressive than that calculus. We can also show that it is no less expressive, by doing the inverse: embedding F ω into 1ML ex .Doing so is fairly straightforward: Figure 10 gives the canonical translation function 

[[ ]] for F ω kinds, types, and terms. It assumes a syntactic injection of F ω type and term variables α and x into 1ML identifiers Xα and Xx, respectively. F ω kinds are translated to suitable 1ML types. F ω types are translated to 1ML expressions; in the case that the type has ground kind Ω, the resulting expression will have a type of the form [= σ ], so that it ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 35 

can be used as a 1ML type; otherwise, it will be a function returning such a value. Finally, Fω terms are translated into 1ML expressions, as is to be expected. Notably, all translated F ω terms become 1ML expressions with a small type. And con-sequently, ground types translate to small types as well. That is necessary to encompass the impredicativity of F ω . To achieve that for quantified types, the translation wraps the translation of every quantified type, using the extension from the previous Section 5.1. Wrapped expressions require a type annotation; we simply assume that the types τe and τe1

used in the figure are determined by context – as usual, this could be made more precise via a type-directed translation, but we gloss over this detail for the sake of simple exposition. To state correctness of the embedding, we also need to define an embedding of F ω

environments. It modifies variable bindings in such a way that they match the requirements of the 1ML typing rules: 

[[ · ]] = ·

[[ Γ, x:τ]] = [[ Γ]] , Xx:σ if [[ Γ]] ` [[ τ]] : [= σ ][[ Γ, α:κ]] = [[ Γ]] , α:κ, Xα :Σ if [[ Γ]] ` [[ κ]] ∃α:κ.Σ

For each F ω term binding x:τ this embedding produces a respective 1ML binding Xx:σ ,where the 1ML embedding [[ τ]] of the type τ is an expression denoting a first-class type (or function over it). This expression has a transparent type by construction. For each F ω type binding α:κ the embedding produces an additional 1ML term binding Xα :Σ of the type as a first-class value, where Σ is determined by the inverse elaboration of the embedding of the kind κ. For example, the F ω kind Ω → Ω translates to the 1ML type type ⇒ type , which by the elaboration rules from Figure 7 is represented by the F ω type ∃α:(Ω → Ω). ∀β :Ω. [= 

α β ]. Consequently, a binding α:(Ω → Ω) is twinned as α:(Ω → Ω), Xα :(∀β :Ω. [= α β ]) ,thereby representing both the abstract type as well as a term carrying it. It is an invariant of elaboration and embedding that the existential quantifiers produced by the elaboration of [[ κ]] always coincides with α:κ – the embedding of kinds is an inverse of the quantifier elaboration of 1ML types. With this, we can show that the embedding is sound, i.e., produces well-formed 1ML programs from well-formed F ω terms: 

Theorem 5.1 (Soundness of Embedding )1. For all κ, · ` [[ κ]] ∃α.Σ with κα = κ and · ` ∃ α.Σ : Ω.2. For all Γ, if Γ ` 2, then [[ Γ]] ` 2.3. For all τ, if Γ ` τ : κ, then [[ Γ]] ` [[ τ]] : Σ and [[ Γ]] ` [[ κ]] Ξ and [[ Γ]] ` Σ ≤ Ξ

(the latter implies that if κ = Ω then Σ = [= σ ]). 4. For all e, if Γ ` e : τ, then [[ Γ]] ` [[ e]] : σ and [[ Γ]] ` [[ τ]] : [= σ ].The proof of (1) is by induction on the structure of κ, and the rest by (simultaneous) induction on the first derivations, respectively. For a complete proof of correctness we would also need to show that the embedding is adequate, i.e., the produced 1ML ex programs are computationally equivalent to the original Fω terms. One way to achieve that would be through a suitable logical relation. But it would be rather involved, requiring simultaneous reasoning about the embedding just defined and 

the 1ML elaboration back into F ω . Given the informal “obviousness” of this result we take the liberty of skipping over it. ZU064-05-FPR main 30 October 2018 15:52 

## 36 Andreas Rossberg 

Although we will not show it here either, it is also worth noting that a predicative version of System F ω can be embedded into plain 1ML ex . All uses of wrap and unwrap in the embedding of types and terms could simply be dropped – except in the case of existential formation, where it is replaced by sealing, i.e., [[ 〈τ1, e2〉τ ]] = ([[ τ1]] , [[ e2]] ) :> [[ τ]] .

5.3 Compositionality 

The takeaway from the last two sections is that 1ML ex is no more and no less powerful than System F ω . But if it is all just a matter of a fairly direct translation, why is it so much less compelling to program in F ω directly? What is the fundamental advantage that a language like 1ML provides, apart from just nifty type inference and a lot of syntactic sugar? The answer is modular compositionality . The heart of modularity is the ability to group types and values together into reusable units, typically called modules and signatures. But also, that from these, larger units can be formed in a compositional manner. Consider the following toy signatures for demonstration:       

> type A = {type t; v : t }
> type B = {type u; w : u }

They can be freely composed into new types:       

> type S = {a : A; b : B; c : {v : a.t; w : b.u }}
> type F = S →S

Similarly, values of these types can be constructed and composed, for example:            

> m1:>A = {type t = int; v = 1 }
> m2:>B = {type u = bool; w = true }
> m3: S = {a = m 1; b = m 2; c = {v = a.v; w = b.w }}

More interestingly, compound types can be abstracted over as they are:          

> g = fun (x : A) (y : B) (f : F) ⇒f{a = x; b = y }
> h = fun (p : S) (f : F) ⇒(f p).a

With raw F ω such composition is not directly possible. It is not possible to group types and values together into composable and reusable units like the signatures and structures above. Type components must instead be represented by quantified types, whose form, placement and scope is dependent on the circumstances. For example, a naive attempt of translating A and B to F ω would be to define them as the corresponding existential types, in direct adherence to Mitchell & Plotkin (1988): 

A = ∃t.{v : t}

B = ∃u.{w : u}

But that’s no good! How can we define S in terms of these types? How about functions corresponding to g and h? It is not possible. The closest one can come to defining reusable named signatures in F ω is by λ -abstracting the contained abstract types (Russo, 2003): 

A = λt.{v : t}

B = λ u.{w : u}

S = λ t u .{a : A t , b : B u , c : {v : t, w : u}} ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 37 

Syntax (types) T :: = . . . | | ’( X : type ) ⇒ T                                             

> Abbreviations: (expressions) if E1then E2else E3:=if E1then E2else E3:
> fun X⇒E:=fun (X:)⇒E
> (types) ’X⇒T:=’( X:type )⇒T
> (declarations) X’Y:T:=X: ’( Y:type )⇒T
> Fig. 11. Extension to Full 1ML

That way, they can be associated with the appropriate binders as needed, for example: 

F = ∀t u . S t u → ∃ t′ u′. S t ′ u′

g = λ t u . λ x : A t . λ y : B u . λ f : F. f t u {a = x, b = y}

h = λ t u . λ p : S t u . λ f : F.unpack 〈t′ u′, q〉 = f t u p in pack 〈t′, q.a〉∃t′. At ′

In general, composition in F ω requires systematically separating all “static” components of a type (i.e., the types it contains) from its “dynamic” components (i.e., proper values), a transformation known as phase-splitting in the module literature (Dreyer et al. , 2003). And if the latter definitions look awfully like the result of 1ML elaboration then that is no coincidence! Behind the syntax distraction, 1ML elaboration is primarily a means of automatically and systematically phase-splitting the input program. Of course, the programmer could try to do that manually, following the sketch above. However, from those simple examples it is already easy to extrapolate that this approach gets very laborious very quickly. Let alone the managing of corresponding existentials on the term level. Harper & Pierce (2005) in fact argue that modular programming based on parameterised signatures (which is what the above is, essentially) leads to a combinatorial explosion of parameters accumulating with each layer of abstraction. That problem carries over to other proposals that suggest adding or emulating modular structure via manual management of polymorphism or separating type components (such as Shields & Peyton Jones (2002)). The fact that under such approaches it is simply not possible to really build fully composable program units means that such approaches are not really modular. 1ML avoids this problem because it does not treat modular composition as an afterthought, but instead takes it as a starting point at the centre of its design. 

6 Full 1ML 

A language without type inference is unworthy of being named ML. This section therefore extends 1ML ex to full 1ML, which includes implicit typing and recovers ML-style implicit polymorphism. Figure 11 shows the minimal syntactic extension necessary. 

6.1 Extensions 

Syntactically, full 1ML merely adds two new forms of type expression to the kernel: 

wildcards “ ” for types inferred from context, and implicit function types, distinguished by a leading tick ’ (a choice that will become clear in a moment). Let us walk through a number of examples, and also explain some of the new syntax sugar on the way. ZU064-05-FPR main 30 October 2018 15:52 

## 38 Andreas Rossberg 

Inferred Types The wildcard “ ” stands for a type that is to be inferred from context – similar to OCaml or dependently typed languages like Coq. The crucial restriction here is that this can only be a small type. This fits nicely with the notion of a monotype in core ML, and prevents the need to infer polymorphic types in an analogous manner. For example, with this syntax, the precise argument type of a function or conditional can be left out:       

> or (x : ) (y : ) = if xthen true else y :

The type system will infer that all wildcards in this function are placeholders for bool .As sugar on top of this new piece of kernel syntax we allow a type annotation “ : ” on a function parameter or conditional to be omitted entirely, thereby recovering the implicitly typed expression syntax familiar from ML. So the above can be condensed to just     

> or x y = if xthen true else y

At this point we drop the 1ML ex interpretation of an unannotated parameter as a type ; we only keep that interpretation in those declaration or binding shorthands that are headed by the type keyword, that is:    

> type t a b = a →b

still defaults a and b to have type type . But in all other places parameter types default to “ ” in full 1ML, that is, they can be any small type. Wildcards can also be used to give partial annotations:         

> projPlus1 b (p : {x : ; y : }) = ( if bthen p.x else p.y) + 1

In this example, the annotation specifies the outer shape of the parameter p (so that it avoids running into inference problems with records, see below). But the component types are inferred to be int .Large types cannot be inferred. Consequently, type annotations still have to be given when a parameter type is large (as, e.g., for polymorphic parameters) or when a condi-tional’s type is large (as in the “computed modules” example given in Section 2) – that is, in all cases that the core type system of conventional ML cannot express. 

Polymorphic Inference The previous examples all were monomorphic. But of course, the claim to fame of ML’s type inference (Damas & Milner, 1982) is that it can assign 

polymorphic types to let -bindings. And of course, that ought to work in 1ML as well:       

> pick b x y = if bthen xelse y

Here, the instantiation of the (omitted) wildcards on the parameters x and y is arbitrary and the type of pick thus polymorphic. This polymorphic type can be expressed syntactically with the other new form of type expression, implicit function types :         

> pick : ’(a : type )⇒bool ⇒a⇒a⇒a

This corresponds to an ML-style polymorphic type, but makes the binder explicit. For obvious reasons, an implicit function has to be pure. The parameter has to be of type type ,whose being small fits nicely with the fact that ML can only abstract monotypes, and not polymorphic types or type constructors. Because the type annotation must be type anyway, we allow to omit it (per Figure 11) and just write the above type as: ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 39         

> pick : ’a ⇒bool ⇒a⇒a⇒a

Or even moving the implicit parameter to the left-hand side, just like we already allow for explicit parameters (cf. Figure 2):       

> pick ’a : bool ⇒a⇒a⇒a

Now it is more apparent: the tick becomes a pun on ML’s type variable syntax, but without relying on brittle implicit scoping rules. As the name would suggest, there are no explicit introduction or elimination forms for implicit functions. Instead, implicit parameters are introduced and eliminated implicitly. So, as one would rightly expect from an ML, the previous function can be invoked without worrying about its type argument: 

> x = pick false 2 3 y = pick true (pick false) (pick true)

Because implicit parameters always have type type , again only small types can be inferred as arguments. So (pick (size > threshold) HashMap TreeMap) would not be well-typed, but demands an explicitly polymorphic version of the pick function. Implicit type generalisation applies to expressions, not just bindings. That is true in some formulations of ML-style polymorphism as well, but usually the difference is not observable. In 1ML it is, because we can have contexts that require a polymorphic value:         

> makeAB (g : ’(a : type )⇒a⇒a⇒a) = {a = g 1 2; b = g true false }

Given this, the argument function in the invocation    

> makeAB ( fun x y ⇒x)

is inferred to have polymorphic type. In fact, we could even apply makeAB (pick true) , as we show next. 

Purity restriction Regular ML imposes the value restriction (Wright, 1995) as an ap-proximation for ensuring the absence of side effects when applying type generalisation, which is needed for soundness. Sine 1ML already tracks purity, it can (once more) replace a syntactic restriction with a more precise semantic one and reuse a concept that we already have introduced. Simply, any pure expression can have its type generalised. For example: 

> pickFst = pick true

has polymorphic type        

> pickFst : ’(a : type )⇒a⇒a⇒a

because the fat arrow in (the first explicit argument of) the type of pick indicates that its application has no side effects. Compare that to                   

> pickImp 1b x y = if !b then xelse ypickImp 2b = if !b then fun x y ⇒xelse fun x y ⇒y

Assuming (!) : ’(a : type ) ⇒ ref a → a, as the implicitly polymorphic version of the rd 

operator from Section 2, the previous functions have types as follows:                     

> pickImp 1: ’(a : type )⇒ref bool ⇒a⇒a→apickImp 2: ’(a : type )⇒ref bool →a⇒a⇒a

Respectively, given a reference r, (pickImp 1 r) could still be generalised, but (pickImp 2 r) 

could not. ZU064-05-FPR main 30 October 2018 15:52 

## 40 Andreas Rossberg 

Subtyping The definition and use of expressions is just one way to introduce or eliminate implicit functions. The other is through subtyping: an implicit function type is a subtype of any possible application of this function. If you consider the two types             

> type T1= int →bool
> type T2= ’a ⇒’b ⇒a→b

then T2 is a subtype of T1. This is another generalisation of a notion that already exists in traditional ML: when matching signatures, a value component can be matched by a more polymorphic value component. Here, it becomes an independent notion. 

Example With these few extensions, the Map functor from Section 2 can now be written in 1ML very much like it would be in traditional ML:                                    

> type MAP =
> {
> type key;
> type map a; empty ’a : map a; lookup ’a : key →map a →opt a; add ’a : key →a→map a →map a
> };Map (Key : EQ) :>MAP where (type .key = Key.t) =
> {
> type key = Key.t;
> type map a = key →opt a; empty = fun x⇒none; lookup x m = m x; add x y m = fun z⇒if Key.eq z x then some y else m z
> }

6.2 Semantics 

The semantics for the extension of 1ML ex to Full 1ML can be seen in Figure 12. As is typical for type systems with inference, the formulation of the semantics is purely 

declarative : the typing rules are non-deterministic, they simply “guess” the right types and quantifiers in various places. We defer the discussion of an actual algorithm that implements type inference for this system to Section 7. 

Semantic Types Wildcards do not induce any extension to semantic types, since they just stand for a suitable small type σ . But obviously, we have to extend our semantic types with a representation for implicit function types. The semantic representation of the syntactic type ’(a : type ) ⇒ { ... } is ∀α.{} → A {. . . }.We write these types with an arrow →A (“ A” for automatic), in order to reuse the notational encoding we already introduced for effects. However, it is a distinct form from →η , i.e., A

is not an effect, and not included in η. All implicit functions are pure. The semantic denotation of an explicitly written, syntactic implicit function type always has exactly one quantified type variable. However, inferred implicit functions can quantify multiple type variables at once. For example, the polymorphic function ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 41 

Semantic Types (large signatures) Σ :: = . . . | ∀ α.{} → A Σ

Types Γ ` T Ξ

Γ ` σ : ΩΓ ` σ TINFER Γ, α, X:[= α] ` T Σ κα = ΩΓ ` ’( X:type ) ⇒ T ∀α.{} → A Σ TIMPL 

Expressions Γ ` E :η Ξ e

Γ, α ` E :P Σ e κα = ΩΓ ` E :P ∀α.{} → A Σ λ α .λAx:{} .e EGEN 

Γ ` E :η ∃α.∀α′.{} → A Σ e Γ, α ` σ : κα′

Γ ` E :η ∃α.Σ[σ /α′] unpack 〈α, x〉 = e in pack 〈α, (x σ {} ).A〉 EINST 

Subtyping Γ ` Ξ′ ≤π Ξ δ ; f

Γ ` σ : κα′ Γ ` Σ′[σ /α′] ≤π Σ δ ; f

Γ ` ∀ α′.{} → A Σ′ ≤π Σ δ ; λ x. f (( x σ {} ).A) SIMPLL 

Γ, α ` Σ′ ≤π Σ δ ; f fv (δ π ) 6 ∩ α

Γ ` Σ′ ≤π ∀α.{} → A Σ δ ; λ x. λ α .λAy:{} . f x SIMPLR 

Fig. 12. New elaboration rules for full 1ML 

f x y = {a = x; b = y }

can conveniently be typed ∀αβ .{} → A α →P β →P {a : α, b : β }. As we will see, this type is interchangeable (via subtyping in both directions) with ∀α.{} → A ∀β .{} → A α →P

β →P {a : α, b : β }, because all arguments are implicit either way. So this is simply a technical convenience. The term argument to an implicit function is always {} , a.k.a. unit. That is so because the function’s parameters are simply a sequence of types α, and there is little value in reifying them as terms [= α], since they are implicit anyway. 15 

Typing Rules With regard to elaboration, we first need the formation rules for the new pieces of type syntax. The rule for wildcards simply guesses a (well-formed) small type non-deterministically. The one for implicit functions mirrors the one for regular function types, but with a fixed parameter type. Moreover, implicit functions may not produce abstract types – a restriction that wouldn’t strictly be necessary, but precludes questionable examples like the following, where each use of weird could denote a completely different type: 16 

f (weird : ’a ⇒ type ) (x : weird) (y : weird) = ...  

> 15

We could have dropped the term argument entirely, representing implicit function types simply as ∀Aα.Σ, but we opted for keeping the shape of all function types uniform and reusing the →x

notation. In part, because we foresee nice generalisations of implicit functions.  

> 16

Our type system still allows definitions like “ type weird = ” to be polymorphic with type 

∀α.{} → A [= α]. Those could be ruled out by removing [= σ ] from the syntax of small types. ZU064-05-FPR main 30 October 2018 15:52 

## 42 Andreas Rossberg 

Next, the new typing rules for introducing and eliminating implicit functions, E GEN and EINST , match common formulations of ML-style polymorphism (Damas & Milner, 1982). The former rule simply introduces (non-deterministically) a sequence of fresh type vari-ables into the context that can be used to type an expression – which must behave nicely by being pure, however. In the conclusion, the rule turns these variables into implicit function parameters. Conversely, the latter rule can take any expression with implicit function type and replaces its type parameters with arbitrary (small) types. The only difference from plain Damas/Milner is that the rule must allow for abstract types α being generated by the (possibly impure) expression; as usual, their quantifiers are just hoisted. Finally, subtyping allows the implicit introduction and elimination of implicit functions as well, via instantiation of the parameter types on the left, or skolemisation on the right (rules S IMPLL and S IMPLR ). As mentioned earlier, this closely corresponds to ML’s signa-ture matching rules. In combination, the two rules also implement reflexivity for implicit function types. For example, ∀α.{} → A [= α] can be derived to be a subtype of itself by first applying S IMPLR in reverse, moving the right-hand side α from the quantifier to the context, and then applying S IMPLL to derive ∀α′.{} → A [= α′] ≤ [= α] via instantiation 

[α/α′].

6.3 Meta-Theory Revisited 

The additional semantics of 1ML does not introduce any difficulty for the soundness proof from Section 4.3. The following properties extend easily to the new rules: 

Proposition 6.1 (Correctness of Full 1ML Elaboration )Let Γ ` 2.1. If Γ ` T /D Ξ, then Γ ` Ξ : Ω.2. If Γ ` E/B :η Ξ e, then Γ ` e : Ξ, and if η=P then Ξ=Σ.3. If Γ ` Ξ′ ≤αα ′ Ξ δ ; f and Γ ` Ξ′ : Ω and Γ, α ` Ξ : Ω, then dom (δ ) = α and 

Γ ` δ : Γ, α and Γ ` f : Ξ′ → δ Ξ.Like before, soundness is still a direct corollary: 

Theorem 6.2 (Soundness of Full 1ML )If · ` E : Ξ e, then either e ↑ or e ↪→∗ v such that · ` v : Ξ.What breaks, though, is our previous proof for decidability, because several of the new rules are “guessing”. The next section is dedicated to coping with that problem. 

7 Type Inference 

With the additions from Figure 12 we have turned the deterministic typing and elaboration judgements of 1ML ex non-deterministic. In a derivation, one has to guess types (in rules TINFER , E INST , S IMPLL ) and quantifiers (in rule E GEN ). Moreover, one has to decide when to apply rules E GEN and E INST . Clearly, an algorithm is needed. 

> However, that is a more substantial restriction. More practical experience with the language is probably needed to figure out the most pragmatic trade-off.

ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 43 

Types Γ `θ T Ξ

Γ `[= ·] 

> θ

E :P [= Ξ]

Γ `θ E Ξ IT PATH υ fresh ∆υ = dom (Γ)

Γ `[] υ IT INFER 

κα = ΩΓ `[] type ∃α.[= α] IT TYPE Γ `[] bool bool IT BOOL 

Γ `θ D ΞΓ `θ {D} Ξ IT STR 

Γ `θ1 T1 ∃α1.Σ1

Γ; α1, X:Σ1 θ1`θ2 T2 ∃α2.Σ2

Γ `θ2 (X:T1) → T2 ∀α1. Σ1 →I ∃α2.Σ2

IT FUN 

Γ `θ1 T1 ∃α1.Σ1

Γ; α1, X:Σ1 θ1`θ2 T2 ∃α2.Σ2 κα′ 

> 2

= κα1 → κα2

Γ `θ2 (X:T1) ⇒ T2 ∃α′

> 2

.∀α1. Σ1 →P Σ2[α′ 

> 2

α1/α2] IT PFUN 

Γ; α, X:[= α] `θ T Σ κα = ΩΓ `θ ’( X:type ) ⇒ T ∀α.{} → A Σ IT IMPL 

Γ `θ T ΞΓ `θ wrap T [Ξ] IT WRAP Γ `θ E :P Σ E = E′:>T ∨ E = E′:T ∨ E = type T

Γ `θ (= E) Σ IT SING 

Γ `θ1 T1 ∃α1.Σ1 α1 = α11 ] α12 

Γ θ1`θ2 T2 ∃α2.Σ2 Γ, α11 , α2 θ2`θ Σ2 ≤α12 Σ1.X δ

Γ `θ T1 where (. X:T2) ∃α11 α2.δ Σ′

> 1

[.X=Σ2] IT WHERE 

Declarations Γ `θ D Ξ

Γ `θ T ∃α.ΣΓ `θ X:T ∃α.{X:Σ} ID VAR Γ `θ T ∃α.{X:Σ}

Γ `θ include T ∃α.{X:Σ} ID INCL 

Γ `θ1 D1 ∃α1.{X1:Σ1}

Γ; α1, X1:Σ1 θ1`θ2 D2 ∃α2.{X2:Σ2} X1 ∩ X2 = /0

Γ `θ2 D1;D2 ∃α1α2.{X1:Σ1, X2:Σ2} ID SEQ Γ `[] ε {} ID EMPTY 

Fig. 13. Inference for Types 

Fortunately, what’s going on is not fundamentally different from conventional (core) ML. Where core ML would require type equivalence (and type inference would use unifi-cation), the 1ML rules require subtyping. Subtyping sneaking into inference may seem scary at first. But closer inspection of the subtyping rules reveals that, when applied to small types, they almost degenerate to type equivalence! The only exception is width subtyping on records, which we will get back to in Section 7.2. The 1ML type system only promises to infer small types, so we are not far away from conventional ML. That is, we can still formulate an algorithm based on 

inference variables – place holders for small types – and a variation on unification. ZU064-05-FPR main 30 October 2018 15:52 

## 44 Andreas Rossberg 

Expressions Γ `θ E :η Ξ

Γ(X) = ΣΓ `[] X :P Σ IE VAR Γ `θ T ΞΓ `θ type T :P [= Ξ] IE TYPE 

Γ `[] true :P bool IE TRUE Γ `[] false :P bool IE FALSE 

Γ `bool  

> θ0

X :P bool Γ θ0`∀

θ1 E1 :η1 Ξ1 Γ θ3`θ4 Ξ1 ≤ ΞΓ θ2`θ3 T Ξ Γ θ1`∀

θ2 E2 :η2 Ξ2 Γ θ4`θ5 Ξ2 ≤ ΞΓ `θ5 if X then E1 else E2 : T :η1∨η2∨η(Ξ) Ξ IE IF 

Γ `θ B :η ΞΓ `θ {B} :η Ξ IE STR Γ `{·}  

> θ

E :η ∃α.{X:Σ, X′:Σ′}

Γ `θ E.X :η ∃α.Σ IE DOT 

Γ `θ1 T ∃α.Σ Γ; α, X:Σ θ1`θ2 E :η ΞΓ `θ2 fun (X:T ) ⇒E :P ∀α. Σ →η Ξ IE FUN 

Γ `·→·  

> θ1

X1 :P ∀α. Σ1 →η ΞΓ θ1`θ2 X2 :P Σ2 Γ θ2`θ3 Σ2 ≤α Σ1 δ

Γ `θ3 X1 X2 :η δ Ξ IE APP 

Γ `θ1 X :P Σ1 Γ θ1`θ2 T ∃α.Σ2 Γ θ2`θ3 Σ1 ≤α Σ2 δ

Γ `θ3 X:>T :η(∃α.Σ2) ∃α.Σ2

IE SEAL 

Γ `θ1 X :P ΣΓ θ1`θ2 T [Ξ] Γ θ2`θ3 Σ ≤ ΞΓ `θ3 wrap X:T :P [Ξ] IE WRAP 

Γ `[·] 

> θ1

X :P [Ξ′]

Γ θ1`θ2 T [Ξ] Γ θ2`θ3 Ξ′ ≤ ΞΓ `θ3 unwrap X:T :η(Ξ) Ξ IE UNWRAP 

Bindings Γ `θ B :η Ξ

Γ `∀ 

> θ

E :η ∃α.ΣΓ `θ X=E :η ∃α.{X : Σ} IB VAR Γ `{·}  

> θ

E :η ∃α.{X:Σ}

Γ `θ include E :η ∃α.{X:Σ} IB INCL 

Γ `θ1 B1 :η1 ∃α1.{X1:Σ1} X′ 

> 1

= X1 − X2

Γ; α1, X1:Σ1 θ1`θ2 B2 :η2 ∃α2.{X2:Σ2} X′

> 1

:Σ′ 

> 1

⊆ X1:Σ1

Γ `θ2 B1;B2 :η1∨η2 ∃α1α2.{X′

> 1

:Σ′

> 1

, X2:Σ2} IB SEQ Γ `[] ε :P {} IB EMPTY 

Fig. 14. Inference for Expressions 

7.1 Algorithm 

Figures 13-15 show how the elaboration rules from the previous sections (including the rules for impredicative types) can be turned into an inference algorithm. Because we are just interested in typing, witness terms (i.e., the bits that were previously greyed out) are omitted from the rules this time. ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 45 

Subtyping Γ `θ Ξ′ ≤π Ξ δΓ `θ Ξ ≤ Ξ′ := Γ `θ Ξ ≤ε Ξ′ id 

Γ `[] υ ≤ υ IS REFL 

Γ `! 

> θ

υ ≈ Σ Γ θ `θ ′ υ ≤ ΣΓ `θ ′ υ ≤ Σ IS RESL Γ `! 

> θ

υ ≈ Σ′ Γ θ `θ ′ Σ′ ≤ υ

Γ `θ ′ Σ′ ≤ υ IS RESR 

Γ `θ π′ = π

Γ `θ π′ ≤ π IS PATH Γ `[] bool ≤ bool IS BOOL 

Γ `θ Ξ′ ≤ Ξ Γ θ `θ ′ Ξ ≤ Ξ′

Γ `θ ′ [= Ξ′] ≤ [= Ξ] [] IS TYPE Γ `[] [= σ ] ≤α0 α [= α0 α] [λ α .σ /α0] IS FORGET 

Γ `θ Ξ′ = ΞΓ `θ [Ξ′] ≤ [Ξ] IS WRAP 

Γ `[] {l:Σ′} ≤ {} IS EMPTY 

Γ `θ1 Σ′ 

> 1

≤π1 Σ1 δ1 head (π1) ⊆ fv (Σ1)

Γ θ1`θ2 {l′:Σ′} ≤ π2 {l:δ1Σ} δ2 head (π2) 6 ∩ fv (Σ1) θ2δ2Σ1 = θ2Σ1

Γ `θ2 {l1:Σ′

> 1

, l′:Σ′} ≤ π1π2 {l1:Σ1, l:Σ} δ1δ2

IS STR 

Γ, α `θ1 Σ ≤α′ Σ′ δ1 η′ ≤ η

Γ; α θ1`θ2 δ1Ξ′ ≤πα Ξ δ2 θ2δ2Σ = θ2ΣΓ `θ2 (∀α′.Σ′ →η′ Ξ′) ≤π (∀α.Σ →η Ξ) δ2

IS FUN 

Γ; α `θ Σ′ ≤α Σ δ α′α 6 = ε

Γ `θ ∃α′.Σ′ ≤ ∃ α.Σ IS ABS 

Σ◦ = S υ fresh ∆υ = dom (Γ) Γ `θ Σ′[υ/α′] ≤π Σ δ

Γ `θ ∀α′.{} → A Σ′ ≤π Σ δ IS IMPLL 

Γ; α `θ Σ′ ≤π Σ δ fv (θ δ π ) 6 ∩ α

Γ `θ Σ′ ≤π ∀α.{} → A Σ δ IS IMPLR 

Fig. 15. Inference for Subtyping 

In order to treat these rules as a definition of a recursive algorithm, we need to interpret the relational judgements as functions. Therefore, we have to be explicit about what are “inputs” and what are “outputs” to these relations. We mark all outputs with a shaded background in the rule schemata given in the figures, i.e., everything right of a colon “:” or squiggly arrow “ ”. The θ index on the turnstile (explained in a minute) is an additional output in every judgement. All other meta variables occurring in the schemata are inputs. The basic idea of these algorithmic rules is to introduce a (free) inference variable υ

wherever the original declarative rules have to guess a (small) type – for example, in rule IT INFER . Furthermore, the rules are augmented by outputting a substitution θ for resolved 

inference variables: all judgements have the form Γ `θ J, which, roughly, implies the ZU064-05-FPR main 30 October 2018 15:52 

## 46 Andreas Rossberg 

Generalisation Γ `∀

θ E :η Ξ

Γ `θ E :I ΞΓ `∀ 

> θ

E :I Ξ IG IMPURE Γ `θ E :P Σ υ = undet (θ Σ) − undet (θ Γ) κα = ΩΓ `∀ 

> θ

E :P ∀α.{} → A Σ[α/υ] IG PURE 

Instantiation Γ `S

θ E :η ΞS :: = υ | α · | bool | [= ·] | [·] | {·} | · → · 

Γ `θ E :η ΞΓ `S 

> θ

E :η Ξ IN REFL Γ `S 

> θ

E :η ∃α′.∀α.{} → A Σ υ fresh ∆υ = dom (Γ)

Γ `S 

> θ

E :η ∃α′.Σ[υ/α] IN IMPL 

Γ `θ E :η ∃α.υ Γ θ `θ ′ υ ≈ S

Γ `S  

> θ′

E :η ∃α.υ IN RES 

Resolution Γ `θ υ ≈ SΓ `! 

> θ

υ ≈ Σ := υ /∈ undet (Σ) ∧ Γ `θ υ ≈ Σ◦

υ′′ fresh ∆υ′′ = ∆υ ∩ ∆υ′

Γ `[υ′′ /υ,υ′′ /υ′] υ ≈ υ′ IR INFER κα = Ω → Ω α ∈ ∆υ υ′ fresh ∆υ′ = ∆υ

Γ `[α υ ′/υ] υ ≈ α · IR PATH 

Γ `[ bool /υ] υ ≈ bool IR BOOL υ′ fresh ∆υ′ = ∆υ

Γ `[[= υ′]/υ] υ ≈ [= ·] IR TYPE 

υ′ fresh ∆υ′ = ∆υ

Γ `[[ υ′]/υ] υ ≈ [·] IR WRAP υ1, υ2 fresh ∆υ1 = ∆υ2 = ∆υ

Γ `[( υ1→Iυ2)/υ] υ ≈ · → · IR FUN 

Unification Γ `θ Ξ = Ξ′

Γ `[] υ = υ IU REFL Γ `θ Ξ′ = ΞΓ `θ Ξ = Ξ′ IU SYMM 

υ′ = undet (σ ) υ /∈ υ′ ∆υ ⊇ fv (σ ) υ′′ fresh ∆υ′′ = ∆υ′ ∩ ∆υ

Γ `[υ′′ /υ′]◦[σ /υ] υ = σ IU BIND 

Γ `θ Ξ = Ξ′

Γ `θ ′ [= Ξ] = [= Ξ′] IU TYPE Γ `θ Ξ = Ξ′

Γ `θ [Ξ] = [ Ξ′] IU WRAP Γ `θ σ = σ ′

Γ `θ α σ = α σ ′ IU PATH 

Γ `θ Σ = Σ′

Γ `θ {l:Σ} = {l:Σ′} IU STR Γ; α `θ1 Σ = Σ′ Γ; α θ1`θ2 Ξ = Ξ′

Γ `θ2 ∀α.Σ →η Ξ = ∀α.Σ′ →η Ξ′ IU FUN 

Γ; α `θ Σ = Σ′

Γ `θ ∃α.Σ = ∃α.Σ′ IU ABS Γ; α `θ Σ = Σ′

Γ `θ ∀α.{} → A Σ = ∀α.{} → A Σ′ IU IMPL 

Fig. 16. Generalisation, Instantiation, Resolution, and Unification ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 47 

respective υ, θ Γ ` θ J declaratively, where υ in the context binds the unresolved inference variables that still appear free in θ Γ or θ J (as if they were regular type variables). In rules with multiple premises, the output substitution of one premise needs to be applied to the inputs of the next, and all output substitutions must be composed. We avoid too much notational awkwardness with abbreviations of the form 

Γ θ `θ ′ J := θ Γ `θ ′′ θJ ∧ θ ′ = θ ′′ ◦ θ

for all inference judgement forms J, where the θ left of the turnstile is effectively an extra input and θJ is meant to apply θ to J’s inputs, as defined above. This notation is used to consistently thread and compose substitutions through all rules that have multiple premises. The desugared form Γ `θ J with just an output substitution is equivalent to the degenerate case Γ id `θ J, i.e., where the input substitution is the identity. Other than the systematic threading of θ there are fairly few changes relative to the declarative rules. In Figures 13-15, all those other differences are highlighted in red for easier reference. The basics of the inference algorithm are not that unusual, focussing around generalisa-tion, instantiation, and resolution of inference variables. 

Generalisation The declarative typing rules allow generalising the type of an expression at any point. However, there are only two situations under which generalisation actually needs to happen: (1) when a value is bound to a variable, because then it could potentially be used at multiple different types, and (2) when an expression’s type needs to match an explicit annotation (directly or indirectly), because that annotation may demand polymor-phism. The first case corresponds to the classical let -rule of Damas/Milner, and occurs in the rule IB VAR : this invokes the auxiliary Generalisation judgement (Figure 16). For pure expressions, it finds all inference variables υ in the expression’s type that do not also occur in the context (we write undet (A) to denote the free inference variables of a semantic object 

A) and quantifies over them – in our case, by introducing an implicit function abstraction. In fact, this rule already covers almost all cases of the second kind as well, because our kernel grammar is a sort of normal form which requires named variables in most places (Figure 1). In particular, this is the case for function arguments. Consider this example:           

> (fun (id : ’a ⇒a→a) ⇒{x = id 3; y = id true }) ( fun x⇒x)

Desugaring rewrites this application into an expression that has an explicit binding for the argument (fun x ⇒ x) , such that rule IB VAR kicks in. The same observation applies to other places where an expression’s type must match an annotation: rules IE SEAL , IE WRAP 

and IE UNWRAP . Similarly, it extends to sugar such as transparent type ascriptions E:T as defined in Figure 2. The only exception is conditionals, because their arms are not variables, yet the type annotation may require them to be polymorphic. Rule IE IF hence also has to invoke the Generalisation judgement. 

Instantiation Instantiation is the inverse of generalisation. It takes place in a slightly different location than with Damas/Milner. Since implicit functions are first-class in 1ML, ZU064-05-FPR main 30 October 2018 15:52 

## 48 Andreas Rossberg 

it is not just variables that can have “polymorphic” type. For example, the result of a projection m.f or of an application g v might have a polymorphic type, too, that potentially requires instantiation. For that reason, the rules delay instantiation as much as possible, and only perform it in the typing rules of elimination forms (e.g. rules IE IF , IE DOT , IE APP , but also IT PATH ). They do so with the help of the auxiliary Instantiation judgement, shown in Figure 16. Instantiation can also happen implicitly as part of subtyping (rule IS IMPLL ), which covers the case where a polymorphic value is matched against a monomorphic (or other polymorphic) parameter. For example, ∀α1α2.{} → A α1 →I α2 ≤ ∀ β .{} → A β →I β will be checked by first applying IS IMPLR , turning the right type monomorphic, and then instantiating the left with IS IMPLL , so that the check is down to υ1 →I υ2 ≤ β →I β ,resolving easily. The instantiation judgement may seem non-deterministic because rule IN IMPL may or may not be applied after IN REFL returns an implicit function type. However, all invoking rules require an output type of a certain shape, so that it is always enforced by context that all implicit functions are actually eliminated, i.e., rule IN IMPL is always applied exhaustively. Therefore, the judgement should be read as iterating over the inferred type until all implicit abstractions are eliminated. What is left, modulo possible existential quantifiers, is either an already determined, non-implicit type or an undetermined type signified by an inference variable. Because implicit types are large and inference variables only stand for small types, there is no ambiguity between the three cases. In the case where the result is an inference variable, rule IN RES has to resolve it. What to resolve it to depends on the context. Instantiation is always invoked for elimination forms, and each elimination expects a corresponding type of a specific shape. This information is passed to the Instantiation judgement in the form of an additional index S that specifies the “shape” in the form of its head constructor. The rule IN RES uses this shape to invoke the resolution judgement, which fabricates a fresh type of the expected shape. 

Resolution The judgement Γ `θ υ ≈ S (Figure 16) is responsible for resolving an in-ference variable to a more specific small type. There is one main complication to this which necessitates turning this step into its own judgement as opposed to simply using substitution. The reason is that, unlike good old ML, our 1ML allows small types to be intermixed with large ones. For one, it is necessary to be able to infer small types from large ones via subtyping. For example, we might encounter the inequality 

∀α.[= α] →P [= α] ≤ υ

which can be solved just fine with υ = [= σ ] →I [= σ ] for any σ . Through contravariance, similar situations can arise with an inference variable on the left, e.g.: 

υ ≤ (∀α.[= α] →P [= α]) →I bool 

which can be solved with υ = ([= σ ] →I [= σ ]) →I bool .Because of this, it is not enough to just consider the cases υ ≤ σ or σ ≤ υ for resolving 

υ. Instead, when the subtyping algorithm hits υ ≤ Σ or Σ ≤ υ (rules IS RESL and IS RESR ,where Σ may or may not be small) it invokes the Resolution judgement, which only resolves ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 49 

υ so far as to match the outermost constructor of Σ and inserts fresh inference variables for its subcomponents. For this purpose we define the auxiliary notation Σ◦ that extracts the shape from a type. Its obvious definition is: 

υ◦ = υ

(α σ )◦ = α ·

bool ◦ = bool 

[= Ξ]◦ = [= ·][Ξ]◦ = [·]

{l:Σ}◦ = {·} 

(∀α1.Σ1 →η ∃α2.Σ2)◦ = · → · 

(∃α.Σ)◦ = Σ◦

With that knowledge, resolution can create a fresh type of the necessary shape. After refining υ that way in the first premise of IS RESL or IS RESR , the rules “try again” in their second premise, and are guaranteed to proceed at least one step further. The occurs check encoded in the shorthand Γ `! 

> θ

υ ≈ S prevents this process from looping. There intentionally is no definition of shape for implicit functions, because they must always be eliminated first. We piggyback on this in the first side condition of the subtyping rule IS IMPLL , which enforces that a shape exists for the right-hand side, and thus, all im-plicit function abstractions on the right are eliminated (by rule IS IMPLR ) before applying this rule. 

Variable Scoping The second complication to 1ML inference is that an inference variable 

υ can be introduced within the scope of arbitrary abstract types (i.e., regular type variables 

α). It would be incorrect to resolve υ to a type containing type variables that are not in scope for all occurrences of υ in a derivation. To prevent that, each υ is associated with a set ∆υ of type variables that are known to be in scope for all uses of υ. The set is verified when resolving υ (see resolution rule IR PATH 

in particular). The set also is propagated to any other υ′ that the original υ is unified with, by intersecting ∆υ′ with ∆υ – or more precisely, by introducing a new variable υ′′ with the intersected ∆υ′′ , and replacing both υ and υ′ with it (see e.g. rule IR INFER ); that way, we can treat ∆υ as a globally fixed set for each υ, and do not need to maintain those sets separately. For example, consider type-checking the following program:              

> f = fun x⇒fun (type t) ⇒fun (g : t →int) ⇒g x

The body of this function is type-checked under some context Γ, x:υ, α, t:[= α], g:(α → α)

where α /∈ ∆υ , because υ was created before α was in scope. Because of that, resolving 

υ with α to make the application type-check will be rejected – which is correct, because otherwise f would be given a malformed type like α → ∀ α.[= α] → (α → int ) → int ,where α escapes its scope. Inference variables also have to be updated when regular type variables go out of scope. Consider this example:         

> (fun (t : type )⇒fun x⇒x) ( type bool)

As a representation for t, type checking will introduce a type variable, say α, into the context. For the inner fun , the parameter x will be assigned a fresh inference variable υ,ZU064-05-FPR main 30 October 2018 15:52 

## 50 Andreas Rossberg 

with α ∈ ∆υ . But υ is not resolved within the scope of α. Once the typing algorithm returns from the outer function, α goes out of scope, and hence can no longer be allowed to occur in any solution for υ – otherwise the type of the overall expression could, e.g., be resolved to α → α with no α in scope. Consequently, α has to be removed from ∆υ at this point. That is achieved by employing the following notation (note the semicolon!) in all rules that locally extend Γ with type variables: 

Γ; Γ′ θ `θ ′ J := Γ, Γ′ θ `θ ′′ J ∧ θ ′ = [ υ′/υ] ◦ θ ′′ 

where υ = undet (θ ′′ J) and υ′ fresh with ∆υ′ = ∆υ ∩ dom (Γ)

The net effect is that all local α’s in the domain of Γ′ are stripped from all ∆-sets of inference variable υ (renamed to υ′ in the process) that remain after executing Γ, Γ′ ` J,thereby disallowing any later resolution with types that would contain those α’s. We omit 

θ in this notation when it is the identity. 

Unification Finally, our algorithm also includes a separate, old-fashioned unification al-gorithm (Figure 16). However, unification is only needed by two rules: the rule IS PATH 

for paths and the rule IS WRAP for the wrapped types of the impredicative extension – because those are the only rule where subtyping does not recurse into subcomponents. In their declarative formulation (Figure 12), the respective rules simply require the types on both sides of the relation to be syntactically equivalent (modulo αβ -conversion, as noted). The presence of inference variables in the algorithmic rules makes that formulation insufficient, of course, and necessitates traversing the structure of the two types to unify possible inference variables embedded in them. This algorithm is much stricter than (mutual) subtyping: there is no quantifier elimi-nation or substitution, all quantifiers, as well as implicit function types, must match up one-to-one. That makes this algorithm trivially decidable even for arbitrary large types. 

7.2 Incompleteness 

Unfortunately, there are a couple of sources of incompleteness in this algorithm: 

Width Subtyping Subtyping constraints like υ ≤ { l:σ } do not determine the shape of the record type υ: the set of its labels can still vary over all possible subsets of l. Consequently, the Resolution judgement in Figure 16 has no rule for structures – instead a structure type must be determined by the previous context. For example.    

> fun x⇒x.a

cannot be handled by the algorithm, because there are infinitely many solutions, and none is principal. The type of x must be annotated explicitly. This is, in fact, similar to Standard ML (Milner et al. , 1997), where record types cannot be inferred either, and require type annotations. However, SML implementations typically ensure that type inference is still order-independent, i.e., the information may be supplied 

after the point of use, so that the equivalent of        

> (fun x⇒x.a) {a = 1; b = 2 }ZU064-05-FPR main 30 October 2018 15:52

1ML – Core and modules united 51 

still type-checks, even if that is not guaranteed by the language specification. They do so by employing a simple form of row inference internally. A similar approach would be possible for 1ML, but subtyping would still make more programs fail to type-check. For the sake of presentation, we decided to err on the side of simplicity in this article and leave out this possible improvement. The real solution of course would be to incorporate not just row inference but row polymorphism (R´ emy, 1989; Ohori, 1995), so that width subtyping on structures can be recast as universal and existential quantification over row variables. We leave investigating such an extension for future work. We only note here that it would not solve the problem completely, because of include : that extends the current scope with bindings that are deter-mined by a structure type; to handle the case where the structure type is row-polymorphic we somehow would have to allow environments Γ to be row-polymorphic, too, or restrict 

include in a suitable manner. 

Type Scoping Tracking of the sets ∆υ is conservative: after leaving the scope of a type variable α, we exclude any solution for υ that would still involve α, even if υ only appears inside a type binder for α. Consider the following example, adapted from Example (c) in Dreyer & Blume (2007):       

> G (x : int) = {M = {type t = int; v = x }:>{type t; v : t }; f = id id };C = G 3; y = C.f (C.M.v);

Assume id : ’a ⇒ a → a. Because id is impure, the definition of f is impure, and its type cannot be generalised; consequently, G is impure, too, and hence generative. The algorithm will infer G’s type as 

int →I ∃β .{M : {t : [= β ], v : β }, f : υ →I υ}

with β /∈ ∆υ – because β goes out of scope the moment we bind it with a local quantifier, while all υ are treated as “global”. It then generalises to 

G : ∀α.{} → A int → ∃ β .{M : {t : [= β ], v : β }, f : α →I α}

But it’s too late: the solution υ = β , which would make y well-typed, is already precluded. When typing C, instantiating α with β is not possible either, because β can only come into scope again (by opening the existential) after having applied an argument for α already. Although not well-known, this very problem is already present in conventional ML, as Dreyer & Blume (2007) pointed out: all existing type inference implementations for ML are incomplete, because combinations of functors and the value restriction (like above) do not have principal types. Interestingly, a variation of the solution suggested by Dreyer & Blume – implicitly generalising the types of functors – is implied by the 1ML typing rules: since functors are just functions, their types can already be generalised (as for G above). However, generalisation happens outside the abstraction, which is more rigid than what they propose (but which is not expressible in System F ω ). Consequently, 1ML can type some examples from their paper – such as Example (b):      

> F (t : type ) = {f = id id };A = F int; B = F bool; x = A.f 10; y = B.f ”dude”; ZU064-05-FPR main 30 October 2018 15:52

## 52 Andreas Rossberg 

This works because F is polymorphic in 1ML (with type ∀α.{} → A ∀β .[= β ] →P {f : α →I

α}). But it is not enough to handle other examples, like G above. In other words, our algorithm can infer the types of some programs that regular ML inference unexpectedly can’t handle. At the same time, the liberal mixture of modules and core programming in 1ML introduces more of these cases, and some remain incomplete. 

Purity Annotations Due to effect subtyping, a function type as an upper bound does not determine the purity of a smaller type. Technically, that does not affect completeness, because we defined small types to include only impure functions: the resolution rule IR FUN 

can always pick I. But arguably, that is cheating a little by side-stepping the issue. In particular, it makes an extension of the notion of (im)purity to other effects, as suggested in Section 2, somewhat inconvenient, because pure function types could not be inferred in parameter positions. Again, the solution would be more polymorphism, in this case a simple form of effect polymorphism (Talpin & Jouvelot, 1992): if effects could be quantified over, they could also be inferred in a complete manner. We explored this solution in a separate paper that extends 1ML with effect polymorphism (Rossberg, 2016), which – interestingly – induces a novel notion of generativity polymorphism for functors. Despite these limitiations, we found 1ML inference quite usable. In practice, MLs have long given up on complete type inference: various limitations exist in both SML and OCaml (and the extended language family including Haskell), necessitating type annota-tions or declarations. In our limited experience with a prototype, 1ML is not substantially worse, at least not when used in the same manner as traditional ML. In fact, we conjecture that any portable 17 SML program in the fragment of the language covered by 1ML – i.e., ignoring features such as references, exceptions, or the likes, but including both modules and Damas/Milner polymorphism – can be directly transliterated into valid 1ML without adding a single type annotation. 

7.3 Correctness 

Algorithmic Soundness The inference algorithm may not be complete, but at least it is sound. That is, we can show the following result: 

Theorem 7.1 (Soundness of 1ML Inference )Let υ, Γ be a well-formed F ω environment. 1. If Γ `θ T /D Ξ, then υ′, θ Γ ` T /D θ Ξ for some υ′.2. If Γ `θ E/B :η Ξ e, then υ′, θ Γ ` E/B :η θ Ξ θ e for some υ′.3. If Γ `θ Ξ′ ≤π Ξ δ ; f and υ, Γ ` Ξ′ : Ω and υ, Γ, α ` Ξ : Ω, then υ′, θ Γ ` θ Ξ′ ≤π

θ Ξ θ δ ; θ f for some υ′.     

> 17 That is, not depending on more liberal type inference than strictly required by the language definition (Milner et al. , 1997). Unfortunately, that is a somewhat fuzzy notion, because the incompleteness of SML type inference is not handled in any precise manner in the standard, see Rossberg (1999a). ZU064-05-FPR main 30 October 2018 15:52

1ML – Core and modules united 53 

In order to prove this result, we need to refine the statement a little bit. In particular, instead of just bundling together υ, Γ as an environment, we want to construct an environ-ment that respects the scoping constraints on the free inference variables υ relative to the regular type variables in their ∆-sets. To that end, we define a little auxiliary judgement υ ` Γ Γ′ that intersperses Γ with υ

such that for each υ the type variables ∆υ are in scope: 

ε ` · ·

υ ∈ υ υ − υ ` Γ Γ′ ∆υ ⊆ dom (Γ)

υ ` Γ Γ′, υυ ` Γ Γ′ α /∈ dom (Γ′)

υ ` Γ, α Γ′, αυ ` Γ Γ′ Γ′ ` Σ : Ω

υ ` Γ, X:Σ Γ′, X:Σ

This assumes that dom (Γ) 6 ∩ υ initially. Γ′ is an extension of Γ that includes bindings for υ, treated as ordinary type variables, and placed such that they adhere to the scoping constraints encoded in ∆. Note that this is a relation: there may be many possible Γ′ for a given pair of Γ and υ (although they are all equivalent in the sense that they all admit the same set of F ω typing judgments). With that, for any F ω or 1ML typing judgement J, we define 

υ; Γ ` J :⇔ υ ` Γ Γ′ ∧ Γ′ ` J (for some Γ′)Furthermore, define well-formedness of resolution substitutions: 

υ′; Γ′ ` θ : υ; Γ :⇔ υ ` Γ Γ′′ ∧ υ′; Γ′ ` θ : Γ′′ ∧

θ small ∧ dom (θ ) 6 ∩ υ′ ∧∀υ ∈ υ, ∀υ′′ ∈ undet (θ υ ), ∆υ′′ ⊆ ∆υ

Well-typed substitutions can be composed: 

Lemma 7.2 (Composition of Substitutions )If υ′; Γ′ ` θ : υ; Γ and υ′′ ; Γ′′ ` θ ′ : υ′; Γ′ and dom (θ ) 6 ∩ υ′′ , then υ′′ ; Γ′′ ` θ ′ ◦ θ : υ; Γ.The refined soundness theorem in its full glory is then stated as follows: 

Theorem 7.3 (Soundness of 1ML Inference Refined )Let dom (Γ) 6 ∩ υ and υ ` Γ Γ′. Let J range over the 1ML inference judgements. 1. Γ′ ` 2 and υ ⊆ dom (Γ′).2. If θ Γ `θ ′ θJ, then θ Γ `θ ′ θ J.3. If Γ `θ J, then υ′; θ Γ ` θ : υ; Γ with υ′ − υ fresh. 4. If Γ θ `θ ′ J and υ′; θ Γ ` θ : υ; Γ, then υ′′ ; θ ′Γ ` θ ′ : υ; Γ with υ′′ − υ′ − υ fresh. 5. If Γ1; Γ2 θ `θ ′ J and υ′; θ Γ ` θ : υ; Γ with Γ = Γ1, Γ2,then υ′′ ; θ ′Γ ` θ ′ : υ; Γ with υ′′ − υ′ − υ fresh and ∆υ′′ ⊆ dom (Γ1).6. If Γ `θ T /D Ξ, then υ′; θ Γ ` T /D θ Ξ.7. If Γ `θ E/B :η Ξ, then υ′; θ Γ ` E/B :η θ Ξ θ e.8. If Γ `θ Ξ ≤π Ξ′ δ , and υ; Γ ` Ξ : Ω and υ; Γ ` Ξ′ : Ω,then υ′; θ Γ ` θ Ξ ≤π θ Ξ′ θ δ ; θ f .9. If Γ `∀ 

> θ

E :η Ξ, then υ′; θ Γ ` E :η θ Ξ θ e.10. If Γ `S 

> θ

E :η Ξ, then υ′; θ Γ ` E :η θ Ξ θ e and Ξ◦ = S.11. If Γ `θ υ ≈ S, then (θ υ )◦ = S.ZU064-05-FPR main 30 October 2018 15:52 

## 54 Andreas Rossberg 

12. If Γ `θ Ξ = Ξ′, and υ; Γ ` Ξ : Ω and υ; Γ ` Ξ′ : Ω, then θ Ξ = θ Ξ′.The proof of the first part is by induction on the derivation of υ ` Γ Γ′, for the others by simultaneous induction on the (first) derivation. 

Termination We can also show that – despite its incompleteness – the inference algorithm at least does not go astray by diverging: 

Theorem 7.4 (Termination of 1ML Inference )All 1ML type inference judgements terminate. As for the 1ML ex typing rules, termination is obvious for most the 1ML inference judgements: the main ones are inductive on the syntactic structure of the language; for the auxiliary Unification judgement, termination can be proved in the usual manner, In-stantiation is inductive on the right-hand side type, and Resolution is not even recursive. Again, only subtyping remains as the problem child. We can prove its termination by extending the proof from Section 4.3. First, we trivially extend the weight function to handle inference variables: 

Q[[ υ]] = 0 S[[ υ]] = 1The Weight Reduction lemma still holds for δ -substitutions on type variables, but we can formulate it analogously for θ -substitutions on inference variables, which are always small as well: 

Lemma 7.5 (Weight Reduction under Small Resolution )1. Q[[ θ Ξ]] = Q[[ Ξ]] .2. W [[ θ Ξ]] < W [[ Ξ]] + 〈1, 0〉.3. W [[ θ Ξ]] ≤ W [[ Ξ]] + 〈| dom (θ )|, 0〉.The following key lemma postulates that a subtyping derivation either resolves more inference variables than it introduces, or the number of excess variables (which will come from rule IS IMPLL ) is bounded by the number of quantifiers in the types involved. 

Lemma 7.6 (Resolution Progress in Subtyping Inference )Let Γ `θ J an inference derivation and Y the set of fresh inference variables it generates. 1. If J is Ξ′ = Ξ, then either |Y | = |θ | = 0 or |Y | < |θ |.2. If J is Ξ′ ≤π Ξ δ ; f , then either |Y | = |θ | = 0 or |Y | < |θ | or |Y | − | θ | ≤ Q[[ Ξ′]] + 

Q[[ Ξ]] . Furthermore, if Ξ 6 = Ξ′ and either Ξ = υ or Ξ′ = υ, then υ ∈ dom (θ ). Else if 

Ξ = υ 6 = Ξ′ = υ′, then |{ υ, υ′} ∩ dom (θ )| = 1. With this, the termination proof can proceed similarly to before, except that we have to take θ into account. 

Lemma 7.7 (Termination of Subtyping Inference )Let υ ` Γ Γ′ and Γ′ ` Ξ′ : Ω and Γ′, α ` Ξ : Ω and π = α α ′. Then Γ `θ Ξ′ ≤π Ξ δ ; f

terminates. The proof is again by case analysis on the algorithm, mostly as before, but this time using the weight W [[ Ξ′]] + W [[ Ξ]] + 〈| π| + |υ′|, 0〉, with υ′ = undet (Ξ′) ∪ undet (Ξ). In each rule, ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 55 

this weight gets smaller for all premises. The only exceptions are the rules IS RESL and IS RESR , which invoke the Resolution judgment that may introduce additional temporary inference variables. That locally increases the weight of the judgement, but we can show by a simple case analysis of the Σ in these rules that the temporary variables are resolved immediately and weight will decrease again in the recursive invocation of the subtyping judgement. 

8 Related Work Packaged Modules The first concrete proposal for extending ML with packaged modules was by Russo (2000), and is implemented in Moscow ML. Later work on type systems for modules routinely included them (Dreyer et al. , 2003; Dreyer, 2005; Rossberg & Dreyer, 2013; Rossberg et al. , 2014), and variations have been implemented in other ML dialects, such as Alice ML (Rossberg, 2006) and OCaml (Garrigue & Frisch, 2010). To avoid soundness issues in the combination with applicative functors, Russo’s original proposal conservatively allowed unpacking a module only local to core-level expressions, but this restriction has been lifted in later systems, which forbid only the occurrence of unpacking inside applicative functors. 

First-Class Modules The first to unify ML’s stratified type system into one language was Harper & Mitchell’s XML calculus (Harper & Mitchell, 1993). It is a dependent type theory modeling modules as terms of Martin-L¨ of-style Σ and Π types, closely following MacQueen’s original ideas (MacQueen, 1986). The system enforces predicativity through the introduction of two universes U1 and U2, which correspond directly to our notion of small and large type. XML allows both U1 : U2 and U1 ⊆ U2, which is similar in 1ML. However, XML lacks any account of either sealing or translucency, which makes it fall short as a foundation for contemporary ML modules. That gap was closed by Harper & Lillibridge’s calculus of translucent sums (Harper & Lillibridge, 1994; Lillibridge, 1997), which also was a dependently typed language of first-class modules. Its main novelty were records with both opaque and transparent type components, directly modeling ML structures. However, unlike XML, the calculus is impredicative, which renders it undecidable. Translucent sums were later deconstructed into the notion of singleton types (Stone & Harper, 2006); they formed the foundation of Dreyer et al.’s type theory for higher-order modules (Dreyer et al. , 2003). However, to avoid undecidability, this system went back to second-class modules (though it provides packaged modules). One central concern in dependently typed theories is phase separation : to enable compile-time checking without requiring core-level computation, such theories must be sufficiently restricted. For example, Harper et al. (1990) investigate phase separation for the XML calculus. The beauty of the F-ing approach underlying 1ML is that it enforces phase separation by construction, since it avoids dependent types altogether. There are previous accounts of ML with modules that involve a limited kind of unifi-cation between core and module language by modelling core-level polymorphic functions as functors (Harper & Stone, 2000; Dreyer et al. , 2007). Furthermore, the latter work on modular type classes also introduces a notion of functors with implicit arguments. ZU064-05-FPR main 30 October 2018 15:52 

## 56 Andreas Rossberg 

Shields & Peyton Jones (Shields & Peyton Jones, 2002) proposed first-class modules for Haskell. However, these do not provide modular compositionality in the sense discussed in Section 5.3, because they cannot contain type components (only module types can), there is no sealing, and type abstraction is manual through raw existential types. 

Applicative Functors Leroy proposed applicative semantics for functors (Leroy, 1995), as implemented in OCaml. Russo later combined both generative and applicative functors in one language (Russo, 2003) and implemented them in Moscow ML; others followed (Shao, 1999; Dreyer et al. , 2003; Dreyer, 2005; Rossberg et al. , 2014). A system like Leroy’s, where all functors are applicative, would be incompatible with first-class modules even in a pure language, because the application in type paths like 

F(A).t needs to be phase-separable to enable type checking, but not all functions are. Russo’s system has similar problems, because it allows converting all generative func-tors into applicative ones. Like Dreyer (Dreyer, 2005) or F-ing modules (Rossberg et al. ,2014), 1ML hence combines applicative (pure) and generative (impure) functors such that applicative semantics is only allowed for functors whose body is both pure and separable. In F-ing modules, applicativity is even inferred from purity, and sealing itself not consid-ered impure. The Technical Appendix of the conference version of this article (Rossberg, 2015) sketches a similar extension to 1ML. In the basic language introduced in the present article, an applicative functor can only be created by sealing a fully transparent functor with pure function type, very much like in Shao’s system (Shao, 1999). 

Type Inference There has been little work that has considered type inference for modules. Russo examined the interplay between core-level inference and modules (Russo, 2003), elegantly dealing with variable scoping via unification under a mixed prefix (which might also form a more elegant basis for 1ML inference than our ∆-sets do). Dreyer & Blume (2007) investigated how functors interfere with the value restriction. They show that – contrary to popular belief – Damas/Milner type inference (Damas & Milner, 1982) with a value restriction (Wright, 1995), as employed in core ML, is no longer complete when combined with ML-style functors. They propose a way to fix this problem by allowing functors to become (implicitly) polymorphic as well. However, their solution requires a destination-passing style semantics for type abstraction – inspired by work on recursive modules (Dreyer, 2007) – that is well beyond the realms of what System F ω can express. Consequently, although 1ML can implicitly generalise functors as well and thus is able to handle some of the examples from Dreyer & Blume’s paper, it cannot deal with the more interesting ones. At the same time, there have been ambitious extensions of ML-style type inference with higher-rank or impredicative types (Garrigue & R´ emy, 1999; Le Botlan & R´ emy, 2003; Vytiniotis et al. , 2008; Russo & Vytiniotis, 2009). Unlike those systems, 1ML never tries to infer a polymorphic type annotation: all guessed types are monomorphic; polymorphic parameters always require annotations. The impredicative extension from Section 5.1 is similar to Garrigue & R´ emy’s semi-explicit polymorphism (Garrigue & R´ emy, 1999), but also allows unboxed polytypes. ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 57 

On the other hand, 1ML allows bundling types and terms together into structures. While it is necessary to explicitly annotate terms that contain types, associated type quantifiers 

(both universal and existential) and their actual introduction and elimination always remain implicit and are effectively inferred as part of the elaboration process. 

9 Conclusion and Future Work 

1ML is a coherent, unified redesign of ML in a single language that subsumes both the ML core and the ML module language. It is no more and no less powerful than System F ω (the higher-order polymorphic lambda calculus), but unlike the latter, supports type inference and modular composition. At the same time, modelling 1ML’s type structure in terms of mere System F ω types trivially establishes phase separation between type checking and execution, a property that requires extra effort in approaches based on dependently typed calculi (Harper et al. , 1990). But 1ML, as shown here, is but a first step. There are many possible improvements and extensions that are worth investigating. 

Mechanisation Elaboration of 1ML ex is fairly straightforward and merely a small mod-ification to F-ing modules, which has been mechanised in Coq (Rossberg et al. , 2014). It should be relatively easy to extend this work to 1ML. The full language and its type inference is far more intricate, however. While we have done the essential parts of the proofs on paper, their details are tedious enough to be almost guaranteed to be wrong. It would be very valuable to mechanise this part of the formalisation and machine-verify the stated properties. 

Implementation We have implemented a simple prototype interpreter for 1ML ( mpi-sws.org/˜rossberg/1ml/ ) that allows running smallish examples. But it would be great to gather more experience with a “real” implementation, especially regarding the viability and user-friendliness of 1ML type inference. 

Usability Pragmatics While 1ML achieves a nice unification of core and module lan-guage, it isn’t necessarily clear whether this is the most desirable design in practice. A clearer syntactic separation of module-level features might be a valuable aid to program-mers. It might also help to tame more obscure cases of subtyping and type inference semantics and avoid confusing the programmer with the full generality of the system in all places. 

Applicative Functors To keep the present paper simple, it adopts a rather basic notion of applicative functor. It is not hard to extend it to pure sealing in the style of F-ing modules – as mentioned earlier, a sketch can be found in the Technical Appendix of the conference version of this article (Rossberg, 2015). A greater challenge would be to go a step further and make it properly abstraction-safe , by tracking value identities as described in Section 8 of Rossberg et al. (2014). This is because the omni-present quantification over value paths 

in that extension likely interferes badly with the small type restriction in 1ML. ZU064-05-FPR main 30 October 2018 15:52 

## 58 Andreas Rossberg 

Implicits The domain of implicit functions in 1ML is limited to type type . Allowing richer types would be a natural extension, and might provide functionality like Haskell-style type classes (Wadler & Blott, 1989; Dreyer et al. , 2007) or Coq-style canonical structures (Mahboubi & Tassi, 2013). In particular, generalised implicit functions could be a semantic foundation for modular implicits (White et al. , 2014). 

Type Inference Despite the ability to express first-class and higher-order polymorphism, inference in 1ML is rather simple. Perhaps it is possible to combine 1ML with some of the more advanced approaches to inference described in literature, some of which we mentioned in Section 8. However, it is non-obvious how well these methods will interact with the implicit quantifier pushing in 1ML’s elaboration. 

Row Polymorphism Replacing subtyping with a more potent form of polymorphism might increase expressiveness and lead to better inference: in particular, row polymor-phism (R´ emy, 1989; Ohori, 1995) could express width subtyping without compromising completeness of inference. The main issue with such an extension probably is its effect on the small/large type universe distinction, since many current uses of subtyping on small types will require large types once they involve quantification over row variables. 

Effect Polymorphism Similarly, the utility of 1MLs effect system and its pure func-tion types could be greatly increased if higher-order functions could vary their effect by employing effect polymorphism (Talpin & Jouvelot, 1992). We have recently explored this direction in a separate paper (Rossberg, 2016). Its most interesting implication is that it enables “functors” to be polymorphic over their generativity, i.e., whether they behave applicatively or generatively. Incidentally, this ability finally allows expressing the motivating examples of MacQueen’s “truly higher-order modules” (MacQueen & Tofte, 1994; Kuan & MacQueen, 2009), which previously have eluded a nice type-theoretic explanation, and were not supported by any other module type system. 

Recursive Modules Recursive modules would add a whole new dimension of expressive-ness – and complexity! – to 1ML. With MixML (Rossberg & Dreyer, 2013) we gave a fully general design for recursive modules, elaborating into an extension of System F. It would be interesting (but complicated) to redo it 1ML-style, in order to achieve a more uniform treatment of recursion than 1ML has. The result of such a cross-breed would presumably share some similarities with Scala (Odersky & Zenger, 2005), but with a more expressive semantics for type equivalences. 

Dependent Types Finally, 1ML goes to great lengths to push the boundaries of non-dependent typing. It’s a legitimate question to ask, what for? Why not go fully depen-dent? Well, even then sealing necessitates some equivalent of weak sums (a.k.a. existential types). Incorporating them, along with the quantifier pushing of our elaboration, into a dependent type system poses a thrilling challenge. ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 59 

References 

Barendregt, Henk. (1992). Lambda calculi with types. Chap. 2, pages 117–309 of: Abramsky, Samson, Gabbay, Dov, & Maibaum, T.S.E. (eds), Handbook of logic in computer science , vol. 2. Oxford University Press. Biswas, Sandip K. (1995). Higher-order functors with transparent signatures. ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL) .Damas, Luis, & Milner, Robin. (1982). Principal type-schemes for functional programs. ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL) .Dreyer, Derek. (2005). Understanding and Evolving the ML Module System . Ph.D. thesis, Carnegie Mellon University. Dreyer, Derek. (2007). Recursive type generativity. Journal of Functional Programming (JFP) ,

17 (4&5), 433–471. Dreyer, Derek, & Blume, Matthias. (2007). Principal type schemes for modular programs. European Symposium on Programming (ESOP) .Dreyer, Derek, Crary, Karl, & Harper, Robert. (2003). A type system for higher-order modules. ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL) .Dreyer, Derek, Harper, Robert, & Chakravarty, Manuel. (2007). Modular type classes. ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL) .Garrigue, Jacques, & Frisch, Alain. (2010). First-class modules and composable signatures in Objective Caml 3.12. ACM SIGPLAN Workshop on ML .Garrigue, Jacques, & R´ emy, Didier. (1999). Semi-explicit first-class polymorphism for ML. 

Information and computation , 155 (1-2). Harper, Robert, & Lillibridge, Mark. (1994). A type-theoretic approach to higher-order modules with sharing. ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL) .Harper, Robert, & Mitchell, John C. (1993). On the type structure of Standard ML. ACM Transactions on Programming Languages and Systems (TOPLAS) , 15 (2), 211–252. Harper, Robert, & Pierce, Benjamin C. (2005). Design considerations for ML-style module systems. 

Chap. 8 of: Pierce, Benjamin C. (ed), Advanced Topics in Types and Programming Languages .MIT Press. Harper, Robert, & Stone, Chris. (2000). A type-theoretic interpretation of Standard ML. Proof, Language, and Interaction: Essays in Honor of Robin Milner . MIT Press. Harper, Robert, Mitchell, John C., & Moggi, Eugenio. (1990). Higher-order modules and the phase distinction. ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL) .Kuan, George, & MacQueen, David. (2009). Engineering higher-order modules in SML/NJ. 

International Symposium on the Implementation and Application of Functional Languages (IFL) .LNCS, vol. 6041. Le Botlan, Didier, & R´ emy, Didier. (2003). MLF: Raising ML to the power of System F. ACM SIGPLAN International Conference on Functional Programming (ICFP) .Leroy, Xavier. (1994). Manifest types, modules, and separate compilation. ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL) .Leroy, Xavier. (1995). Applicative functors and fully transparent higher-order modules. ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL) .Leroy, Xavier. (1996). A syntactic theory of type generativity and sharing. Journal of Functional Programming (JFP) , 6(5), 1–32. Lillibridge, Mark. (1997). Translucent sums: A foundation for higher-order module systems . Ph.D. thesis, Carnegie Mellon University. ZU064-05-FPR main 30 October 2018 15:52 

## 60 Andreas Rossberg 

MacQueen, David B. (1986). Using dependent types to express modular structure. ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL) .MacQueen, David B., & Tofte, Mads. (1994). A semantics for higher-order functors. European Symposium on Programming (ESOP) .Mahboubi, Assia, & Tassi, Enrico. (2013). Canonical structures for the working Coq user. Pages 19– 34 of: Blazy, Sandrine, Paulin-Mohring, Christine, & Pichardie, David (eds), Interactive theorem proving . LNCS, no. 7998. Springer-Verlag. McBride, Conor, & Paterson, Ross. (2008). Applicative programming with effects. Journal of Functional Programming (JFP) , 18 (1), 1–13. Milner, Robin. (1978). A theory of type polymorphism in programming languages. Journal of Computer and System Sciences , 17 , 348–375. Milner, Robin, Tofte, Mads, Harper, Robert, & MacQueen, David. (1997). The Definition of Standard ML (Revised) . MIT Press. Mitchell, John C., & Plotkin, Gordon D. (1988). Abstract types have existential type. ACM Transactions on Programming Languages and Systems (TOPLAS) , 10 (3), 470–502. Odersky, Martin, & Zenger, Matthias. (2005). Scalable component abstractions. Object-Oriented Programming, Systems, Languages and Applications (OOPSLA) . ACM Press. Ohori, Atsushi. (1995). A polymorphic record calculus and its compilation. ACM Transactions on Programming Languages and Systems (TOPLAS) , 17 (6), 844–895. R´ emy, Didier. (1989). Records and variants as a natural extension of ML. ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL) .Rossberg, Andreas. (1999a). Defects in the Revised Definition of Standard ML . Technical report, Max Planck Institute for Software Systems. mpi-sws.org/~rossberg/sml-defects.html .Rossberg, Andreas. (1999b). Undecidability of OCaml type checking . Posting to Caml mailing list, 13 July. sympa.inria.fr/sympa/arc/caml-list/1999-07/msg00027.html .Rossberg, Andreas. (2006). The Missing Link – Dynamic components for ML. ACM SIGPLAN International Conference on Functional Programming (ICFP) .Rossberg, Andreas. (2015). 1ML – Core and modules united (Technical Appendix) . mpi-sws.org/ ~rossberg/1ml/ .Rossberg, Andreas. (2016). 1ML with special effects. Pages 336–355 of: A List of Successes That Can Change the World – WadlerFest 2016 . LNCS, no. 9600. Springer-Verlag. Rossberg, Andreas, & Dreyer, Derek. (2013). Mixin’ up the ML module system. ACM Transactions on Programming Languages and Systems (TOPLAS) , 35 (1), 1–84. Rossberg, Andreas, Russo, Claudio, & Dreyer, Derek. (2014). F-ing modules. Journal of Functional Programming (JFP) , 24 (5), 529–607. Russo, Claudio, & Vytiniotis, Dimitris. (2009). QML: Explicit first-class polymorphism for ML. 

ACM SIGPLAN Workshop on ML .Russo, Claudio V. (1999). Non-dependent types for Standard ML modules. International Conference on Principles and Practice of Declarative Programming (PPDP) .Russo, Claudio V. (2000). First-class structures for Standard ML. Nordic Journal of Computing ,

7(4), 348–374. Russo, Claudio V. (2003). Types for Modules. Electronic Notes in Theoretical Computer Science (ENTCS) , 60 .Shao, Zhong. (1999). Transparent modules with fully syntactic signatures. ACM SIGPLAN International Conference on Functional Programming (ICFP) .Shields, Mark, & Peyton Jones, Simon. (2002). First-class modules for Haskell. International Workshop on Foundations of Object-Oriented Languages (FOOL) .ZU064-05-FPR main 30 October 2018 15:52 

1ML – Core and modules united 61 

Stone, Christopher A., & Harper, Robert. (2006). Extensional equivalence and singleton types. ACM Transactions on Computational Logic (TOCL) , 7(4), 676–722. Talpin, Jean-Pierre, & Jouvelot, Pierre. (1992). Polymorphic type, region and effect inference. 

Journal of Functional Programming (JFP) , 2(3), 245–271. Vytiniotis, Dimitrios, Weirich, Stephanie, & Peyton Jones, Simon. (2008). FPH: First-class polymorphism for Haskell. ACM SIGPLAN International Conference on Functional Programming (ICFP) .Wadler, Philip, & Blott, Stephen. (1989). How to make ad-hoc polymorphism less ad hoc. ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL) .White, Leo, Bour, Fr´ ed´ eric, & Yallop, Jeremy. (2014). Modular implicits. Pages 22–63 of: Kiselyov, Oleg, & Garrigue, Jacques (eds), ACM SIGPLAN ML Family / OCaml Workshops . EPTCS, no. 198. Wright, Andrew. (1995). Simple imperative polymorphism. LISP and Symbolic Computation (LASC) , 8(4), 343–356. ZU064-05-FPR main 30 October 2018 15:52
