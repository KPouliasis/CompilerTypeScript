// Compiler Construction (CSCI-GA.2130.001) Spring 2014
// Project Milestone 2 ("pr2") base file.
//
module "edu.nyu.cims.cc.spring2014.ProjectMilestone2" {


// LEXICAL CONVENTIONS (pr2/Def.A.1)

space [ \t\n\r] | '//' [^\n]* | '/*' ( [^*] | '*' [^/] )* '*/'  ;

token Identifier | ⟨LetterEtc⟩ (⟨LetterEtc⟩ | ⟨Digit⟩)* ;

token Decimal    | ⟨Digit⟩+ ('.' ⟨Digit⟩+)? ('e' [-+]? ⟨Digit⟩+)? ;

token String     | [''] ( [^''\\\n] | \\ ⟨Escape⟩ )* ['']  |  [""] ( [^""\\\n] | \\ ⟨Escape⟩ )* [""] ;
                 //Note: double the quotes to not confuse pretty-printer...

token fragment Letter | [A-Za-z] ;
token fragment LetterEtc | ⟨Letter⟩ | [$_] ;
token fragment Digit | [0-9] ;

token fragment Escape | \n | [''""\\] | [nt] | 'x' ⟨Hex⟩ ⟨Hex⟩ ;
token fragment Hex | [0-9A-Fa-f] ;

//TYPES

sort Type
| ⟦ any ⟧ | ⟦ boolean ⟧ | ⟦ number ⟧ | ⟦ string ⟧ | ⟦ void ⟧
| ⟦ ⟨Type⟩ [ ] ⟧
| ⟦ ⟨Identifier⟩ ⟧
| ⟦ ( ⟨Formals⟩ ) => ⟨Type⟩ ⟧
| ⟦ ( ) => ⟨Type⟩ ⟧
;

//ISNUMBER PREDICATE
sort Type | scheme Isnumber(Type);
Isnumber(⟦  ⟨Type ⟦number⟧⟩ ⟧) →⟦ number⟧ ;
Isnumber(⟦  ⟨Type ⟦any⟧⟩ ⟧) →error⟦ number type expected⟧;
Isnumber(⟦  ⟨Type ⟦boolean⟧⟩ ⟧) →error⟦ number type expected⟧;
Isnumber(⟦ ⟨Type ⟦void⟧⟩ ⟧) →error⟦ number type expected⟧;
Isnumber(⟦  ⟨Type ⟦string⟧⟩ ⟧) →error⟦ number type expected⟧;
Isnumber(⟦ ⟨Type ⟦⟨Type#1⟩ [ ] ⟧⟩ ⟧) →error⟦ number type expected⟧ ;
Isnumber (⟦ ⟨Type⟦ ⟨Identifier#1⟩ ⟧⟩ ⟧)→error⟦ number type expected⟧ ;
Isnumber ( ⟦ ⟨Type⟦  (⟨Formals#1⟩)  => ⟨Type#2⟩ ⟧⟩ ⟧)→error⟦ number type expected⟧ ;
Isnumber ( ⟦ ⟨Type⟦  ( )  => ⟨Type#2⟩ ⟧⟩ ⟧)→error⟦ number type expected⟧ ;



//TYPE EXISTENCE WITHIN A top DECLARATION CONTEXT



sort Type | scheme ⟦ Exists_t ⟨Type⟩ ⟧ ↓top ;
 ⟦Exists_t ⟨Type ⟦ any ⟧ ⟩⟧ →⟦any ⟧;
 ⟦Exists_t ⟨Type ⟦ boolean ⟧ ⟩⟧ →⟦boolean⟧;
 ⟦Exists_t ⟨Type ⟦ number ⟧ ⟩⟧ →⟦number⟧;
 ⟦Exists_t ⟨Type ⟦ string ⟧ ⟩⟧ →⟦string⟧;
 ⟦Exists_t ⟨Type ⟦ void ⟧ ⟩⟧ →⟦void⟧;
 ⟦Exists_t ⟨Type ⟦  ⟨Type#1⟩ [ ]⟧ ⟩⟧ → ⟦Exists_t ⟨Type#1⟩⟧;
 ⟦ Exists_t  ⟨Type ⟦⟨Identifier id⟩  ⟧ ⟩⟧  ↓top{⟦⟨Identifier id⟩⟧ : #t} → #t;
 ⟦ Exists_t ⟨Type ⟦⟨Identifier id⟩  ⟧ ⟩ ⟧ ↓top{¬⟦⟨Identifier id⟩⟧ } → error⟦undeclared type  ⟨Identifier id⟩ ⟧ ;
 ⟦Exists_t ⟨Type ⟦  (⟨Formals#1⟩) =>⟨Type#2⟩ ⟧ ⟩⟧ → 
 ⟦ (⟨Formals ⟦ Exists_fs ⟨Formals#1⟩ ⟧⟩)=> ⟨Type ⟦Exists_t ⟨Type#2⟩⟧⟩ ⟧; 
 ⟦Exists_t ⟨Type ⟦  ( ) =>⟨Type#2⟩ ⟧ ⟩⟧ →   ⟦ ( )=> ⟨Type ⟦Exists_t ⟨Type#2⟩⟧⟩ ⟧;

//FORMAL EXISTENCE - VIA TYPE EXISTENCE
sort Formal | scheme ⟦ Exists_f ⟨Formal⟩ ⟧ ↓top ;
⟦Exists_f ⟨Formal ⟦ ⟨Identifier#1⟩ : ⟨Type#2⟩ ⟧ ⟩⟧  →⟦  ⟨Formal ⟦⟨Identifier#1⟩ : ⟨Type ⟦Exists_t ⟨Type#2⟩⟧⟩⟧⟩⟧;


//Formals existence - inductive formal existence
sort Formals | scheme ⟦ Exists_fs ⟨Formals⟩ ⟧ ↓top ;
⟦Exists_fs ⟨Formals ⟦ ⟨Formal#1⟩ , ⟨Formals#2⟩ ⟧ ⟩⟧ → 
⟦  ⟨Formals ⟦⟨Formal ⟦ Exists_f ⟨Formal#1⟩⟧⟩  , ⟨Formals ⟦ Exists_fs ⟨Formals#2⟩⟧⟩⟧ ⟩⟧;
⟦Exists_fs ⟨Formals ⟦ ⟨Formal#1⟩  ⟧ ⟩⟧ → 
 ⟦⟨Formals ⟦ Exists_f ⟨Formal#1⟩⟧⟩ ⟧ ;

// Formals sorts definitions

//nonempty formals list
sort Formals         | ⟦ ⟨Formal⟩ , ⟨Formals⟩ ⟧ | ⟦ ⟨Formal⟩ ⟧ ;
//single formal
sort Formal          | ⟦ ⟨Identifier⟩ : ⟨Type⟩ ⟧ ;
//possibly empty list of formals
sort FormalsOption | ⟦ ⟨Formals⟩ ⟧ | ⟦ ⟧;

//CLASS CONTEXT REPRESENTS A CLASS: BINDING FROM 
//IDENTIFIERS TO TYPES!
attribute ↓classcontext{Identifier:Type};

//Context of Formals for a class
//to be validated for unicity of member names
attribute ↓classcontextsig{Identifier:Type};


sort FormalsOption | scheme ⟦AppendF ⟨Formal⟩⟨FormalsOption⟩⟧  ;

⟦AppendF ⟨Formal #f⟩ ⟨FormalsOption ⟦ ⟧⟩ ⟧  → ⟦⟨FormalsOption ⟦ ⟨Formals⟦ ⟨Formal#f⟩ ⟧⟩ ⟧⟩ ⟧;
⟦AppendF  ⟨Formal #f⟩⟨FormalsOption  ⟦⟨Formals ⟦ ⟨Formal#f⟩ ⟧⟩⟧⟩⟧  → ⟦ ⟨FormalsOption ⟦ ⟨Formals⟦ ⟨Formal#f⟩ ⟧⟩ ⟧⟩ ⟧;
⟦AppendF ⟨Formal #f1⟩   ⟨FormalsOption ⟦⟨Formals  ⟦ ⟨Formal#f2⟩ , ⟨Formals#fs⟩ ⟧⟩ ⟧⟩ ⟧  → ⟦ ⟨FormalsOption ⟦ ⟨Formals⟦ ⟨Formal#f1⟩,⟨Formal#f2⟩ , ⟨Formals#fs⟩ ⟧⟩ ⟧⟩ ⟧;

//Unicity of members return the class formals only if there are not repetition
//otherwise invokes an error
sort FormalsOption | scheme UnicityMembers(FormalsOption,FormalsOption) ↓classcontextsig;
UnicityMembers(⟦ ⟨FormalsOption ⟦ ⟧⟩ ⟧, ⟦ ⟨FormalsOption ⟦⟨Formals #fs⟩ ⟧⟩ ⟧)  → ⟦⟨FormalsOption ⟦⟨Formals #fs⟩ ⟧⟩⟧;
UnicityMembers(⟦ ⟨FormalsOption ⟦ ⟨Formals ⟦ ⟨Formal ⟦ ⟨Identifier#1⟩ : ⟨Type#2⟩ ⟧   ⟩ ⟧⟩⟧⟩ ⟧, ⟦ ⟨FormalsOption ⟦⟨Formals #fs⟩ ⟧⟩ ⟧) ↓classcontextsig{¬⟦⟨Identifier#1⟩⟧} 
→
UnicityMembers ( ⟦ ⟨FormalsOption ⟦ ⟧⟩ ⟧ ,  ⟦ ⟨FormalsOption ⟦AppendF ⟨Formal ⟦ ⟨Identifier#1⟩ : ⟨Type#2⟩ ⟧⟩ ⟨FormalsOption ⟦⟨Formals #fs⟩ ⟧⟩⟧⟩ ⟧) ;
UnicityMembers(⟦ ⟨FormalsOption ⟦ ⟨Formals ⟦ ⟨Formal ⟦ ⟨Identifier#1⟩ : ⟨Type#2⟩ ⟧   ⟩ ⟧⟩⟧⟩ ⟧, ⟦ ⟨FormalsOption ⟦⟨Formals #fs⟩ ⟧⟩ ⟧) ↓classcontextsig{⟦⟨Identifier#1⟩⟧} 
→
error ⟦rmember names in a class should be unique⟧;
UnicityMembers(⟦ ⟨FormalsOption ⟦⟨Formals  ⟦ ⟨Formal ⟦ ⟨Identifier#1⟩ : ⟨Type#2⟩ ⟧⟩ , ⟨Formals#fs⟩ ⟧⟩ ⟧⟩ ⟧, ⟦ ⟨FormalsOption ⟦⟨Formals #fs2⟩ ⟧⟩ ⟧) ↓classcontextsig{¬⟦⟨Identifier#1⟩⟧} 
→UnicityMembers ( ⟦ ⟨FormalsOption ⟦ ⟨Formals#fs⟩⟧⟩ ⟧ ,  ⟦ ⟨FormalsOption ⟦AppendF ⟨Formal ⟦ ⟨Identifier#1⟩ : ⟨Type#2⟩ ⟧⟩ ⟨FormalsOption ⟦⟨Formals #fs2⟩ ⟧⟩⟧⟩ ⟧) ;
;


sort Type | scheme Memberapp(FormalsOption,Identifier) ↓classcontext;

//NEEDS FIXING HERE! DUPLICATION HAS ALREADY BEEN FIXED IN UNICITYMEMBERS!!
//embedding formalsoption of a class to a context
// and fiding the type of an possible-member
//if we have exhausted the members of the class then look in the context
Memberapp(⟦ ⟨FormalsOption ⟦ ⟧⟩ ⟧, ⟦ ⟨Identifier #id⟩ ⟧) ↓classcontext{⟦⟨Identifier#id⟩⟧:  ⟦ ⟨Type #2⟩⟧} → #2;

//if id is not in the context then give error
Memberapp(⟦ ⟨FormalsOption ⟦ ⟧⟩ ⟧, ⟦ ⟨Identifier #id⟩ ⟧) ↓classcontext{¬⟦ ⟨Identifier #id⟩ ⟧} → error⟦ member  ⟨Identifier #id⟩  not in class ⟧;



Memberapp(⟦ ⟨FormalsOption ⟦⟨Formals ⟦⟨Formal ⟦⟨Identifier#1⟩ : ⟨Type#2⟩  ⟧⟩ ⟧⟩ ⟧⟩ ⟧, ⟦ ⟨Identifier #id⟩ ⟧)  ↓classcontext{¬⟦⟨Identifier#1⟩⟧} → Memberapp(⟦ ⟨FormalsOption ⟦ ⟧⟩ ⟧, ⟦ ⟨Identifier #id⟩ ⟧) ↓classcontext{⟦⟨Identifier#1⟩⟧: ⟦ ⟨Type #2⟩⟧} ;
Memberapp(⟦ ⟨FormalsOption ⟦⟨Formals ⟦⟨Formal ⟦⟨Identifier#1⟩ : ⟨Type#2⟩  ⟧⟩ ⟧⟩ ⟧⟩ ⟧, ⟦ ⟨Identifier #id⟩ ⟧)  ↓classcontext{⟦⟨Identifier#1⟩⟧:⟦ ⟨Type #3⟩⟧} → error⟦not well definition of class in use. Duplicate member definition!⟧;

// if the are more formals add them recursively extend the context  consuming them 
//recursively 
Memberapp(⟦ ⟨FormalsOption ⟦⟨Formals  ⟦ ⟨Formal ⟦⟨Identifier#1⟩ : ⟨Type#2⟩  ⟧⟩, ⟨Formals#3⟩ ⟧ ⟩ ⟧⟩ ⟧, ⟦ ⟨Identifier #id⟩ ⟧) ↓classcontext{¬⟦⟨Identifier#1⟩⟧} → Memberapp(⟦ ⟨FormalsOption ⟦⟨Formals#3⟩⟧⟩ ⟧, ⟦ ⟨Identifier #id⟩ ⟧) ↓classcontext{⟦⟨Identifier#1⟩⟧: ⟦ ⟨Type #2⟩⟧} ;
Memberapp(⟦ ⟨FormalsOption ⟦⟨Formals  ⟦ ⟨Formal ⟦⟨Identifier#1⟩ : ⟨Type#2⟩  ⟧⟩, ⟨Formals#3⟩ ⟧ ⟩ ⟧⟩ ⟧, ⟦ ⟨Identifier #id⟩ ⟧) ↓classcontext{⟦⟨Identifier#1⟩⟧: ⟦ ⟨Type #3⟩⟧} →  error⟦not well definition of class in use. Duplicate member definition!⟧;//WITHING A CLASS CONTEXT WE GIVE TYPES TO EACH MEMBER.

//TYPELISTS ARE LISTS/INDEXED COLLECTIONS OF TYPES
//USEFUL FOR FUNCTION APPLICATIONS 
//AND ALSO CHECNG HOMOGEINITY IN LISTS
//HELPERSORT
sort Typelist
|⟦⟨Type⟩⟧|⟦⟨Type⟩;⟨Typelist⟩⟧
;

|scheme  FormalstoList(Formals);
FormalstoList(⟦⟨Formals ⟦⟨Formal⟦⟨ Identifier#1⟩: ⟨ Type#2⟩⟧ ⟩ ⟧⟩ ⟧)→⟦ ⟨Typelist ⟦⟨Type#2⟩⟧⟩⟧ ;
 FormalstoList (⟦⟨ Identifier#1⟩: ⟨ Type#2⟩ ,⟨Formals  #fs⟩ ⟧)→⟦⟨Type #2⟩;⟨Typelist FormalstoList(#fs)⟩⟧;
//defining equality of typelists as identity???
| scheme Equiv(Typelist,Typelist);
 Equiv(#t,#t)→ #t;
default Equiv(#t,#v)→ error ⟦ ill-typed function application⟧ ;


//type compatibility ON ASSIGNMENTS! (NOT ON LISTS remember)
//returns singleton list for convenience with the enhanced pt attribute
sort Typelist | scheme Compatible(Type,Type);
Compatible(#t,#t) → ⟦  ⟨Typelist ⟦  ⟨Type #t⟩ ⟧⟩ ⟧;
Compatible(#t,⟦any⟧)→  ⟦ ⟨Typelist ⟦  ⟨Type ⟦any⟧ ⟩ ⟧⟩ ⟧;
default Compatible(#t1,#t2)→error⟦ non-compatible type assignment⟧ ;



|scheme ⟦AppendSingleton ⟨Typelist⟩ ⟨Typelist⟩⟧;
 ⟦AppendSingleton  ⟨Typelist  ⟦  ⟨Type #t1⟩ ⟧⟩  ⟨Typelist   ⟦  ⟨Type #t2⟩ ⟧⟩⟧  → ⟦  ⟨Typelist ⟦  ⟨Type #t1⟩; ⟨Type #t2⟩⟧⟩ ⟧;
⟦AppendSingleton ⟨Typelist  ⟦⟨Type #t1⟩ ; ⟨Typelist #tl⟩ ⟧⟩  ⟨Typelist   ⟦  ⟨Type #t2⟩ ⟧⟩⟧ →

 ⟦  ⟨Typelist ⟦ ⟨Type #t1⟩; ⟨Typelist ⟦AppendSingleton ⟨Typelist #tl⟩   ⟨Typelist   ⟦  ⟨Type #t2⟩ ⟧⟩⟧⟩ ⟧⟩ ⟧; 
default ⟦AppendSingleton ⟨Typelist#1⟩ ⟨Typelist#2⟩⟧ → error⟦ bad assumptions on assiociativity of args? ⟧;

//HELPERSORT
sort ArrayType
| ⟦ ⟨Type⟩ ⟧
| ⟦ ArrayEmpty ⟧
;
sort Type| scheme ArrayUnif(Type,ArrayType) ;
//defining homeogenous array property of well formed arrays
//HOPE THE UNIFICATION WORKS WITH DIFFERENT KINDS
ArrayUnif(⟦⟨Type#t1 ⟩⟧, ⟦⟨ArrayType ⟦ ArrayEmpty ⟧⟩⟧) →  #t1;
ArrayUnif( ⟦⟨Type#t1 ⟩⟧,⟦⟨ArrayType ⟦ ⟨Type#t1⟩ ⟧⟩⟧  ) → #t1;
default ArrayUnif( #t1, #2 ) →error⟦non contiguous arrays are not permitted ⟧ ;

//MORE FOR ARRAYS: INDEXING HAS TO HAPPEN ONLY WITH NUMS AS INDEXES
//VALIDITY OF ARRAY APPLICATION REDUCES TO ISNUMBER(INDEX)
sort Type | scheme ValidArrayApp(Type,Type);
ValidArrayApp(⟦ ⟨Type ⟦⟨Type#1⟩ [ ] ⟧⟩ ⟧,  ⟦  ⟨Type#2⟩ ⟧) → ValidArrayApp2(⟦ ⟨Type ⟦⟨Type#1⟩ [ ] ⟧⟩ ⟧,  ⟦  ⟨Type Isnumber(#2)⟩ ⟧) ;
default ValidArrayApp( #t1, #2 ) →error⟦shouldn't be here ⟧ ;

|scheme ValidArrayApp2(Type,Type);
ValidArrayApp2(⟦ ⟨Type ⟦⟨Type#1⟩ [ ] ⟧⟩ ⟧,  ⟦  ⟨Type#2⟩ ⟧) → ⟦⟨Type#1⟩⟧ ;
default ValidArrayApp2( #t1, #2 ) →error⟦shouldn't be here ⟧ ;
//HELPER SORT BOOLEANS
sort Boolean
| ⟦ tru⟧
| ⟦ fls⟧;

//TYPE ATTRIBUTES
//classic type attribute for expressions
attribute ↑t(Type);  // synthesized expression type
//attribtte in the extended type universe for arraychecking
attribute ↑lt(ArrayType); //synthesized in the extended universe for array checking

//LVALUE ATTRIBUTE
attribute ↑lval(Boolean);


// Variables have a special production to permit symbol tables.
sort Variable | symbol ⟦⟨Identifier⟩⟧ ;

// Literals are split in simple/complex to restrict the latter to assignments.

sort SimpleLiteral 
 |⟦ ⟨String⟩ ⟧ ;
 |⟦ ⟨Decimal⟩ ⟧ ;
 
sort SimpleLiteral | ↑t;
⟦ ⟨String#⟩ ⟧ ↑t(⟦ string ⟧); 
⟦ ⟨Decimal#⟩ ⟧  ↑t(⟦ number ⟧);
 


sort ComplexLiteral  | ⟦ [ ⟨LiteralList⟩ ] ⟧ ; //| ⟦ { ⟨Actual+_,⟩ } ⟧ ;

sort ComplexLiteral | ↑t;
⟦ [ ⟨LiteralList# ↑t(#t1) ⟩ ] ⟧ ↑t( ⟦⟨Type #t1⟩ []⟧ );
//⟦ [ ⟨LiteralList ↑t(#1)⟩ ] ⟧  ↑pt(Typelist  ⟦⟨Type #1⟩⟧);
 //| ⟦ { ⟨Actual+_,⟩ } ⟧ ;
 
sort Literal     
 |⟦ ⟨SimpleLiteral⟩ ⟧  ;
 |⟦ - ⟨SimpleLiteral⟩ ⟧ ;
 |⟦ + ⟨SimpleLiteral⟩⟧; 
 |⟦ ⟨ComplexLiteral⟩ ⟧ ;
 
 sort  Literal | ↑t;
⟦ ⟨SimpleLiteral# ↑t(#t1) ⟩  ⟧ ↑t(#t1);
⟦ - ⟨SimpleLiteral# ↑t(#t1) ⟩  ⟧ ↑t(Isnumber(#t1));  
⟦ + ⟨SimpleLiteral# ↑t(#t1) ⟩    ⟧ ↑t(Isnumber(#t1)); 
⟦ ⟨ComplexLiteral# ↑t(#t1) ⟩  ⟧ ↑t(#t1);


sort LiteralList | ⟦  ⟨Literal⟩ ⟨LiteralTailOption⟩  ⟧;

sort LiteralList | ↑t;
⟦ ⟨Literal# ↑t(#t1) ⟩ ⟨LiteralTailOption# ↑lt(#t2) ⟩ ⟧ ↑t(ArrayUnif(#t1,#t2));

sort LiteralTailOption | ⟦  , ⟨Literal⟩ ⟨LiteralTailOption⟩  ⟧ | ⟦ ⟧ ;

sort  LiteralTailOption | ↑lt;
⟦   , ⟨Literal# ↑t(#t1) ⟩ ⟨LiteralTailOption# ↑lt(#t2) ⟩   ⟧ ↑lt(ArrayUnif(#t1,#t2));
⟦  ⟧ ↑lt( ⟦ ArrayEmpty ⟧ );
 
sort Actual          | ⟦ ⟨Key⟩ : ⟨Literal⟩ ⟧ ;
sort Key             | ⟦ ⟨Identifier⟩ ⟧ | ⟦ ⟨String⟩ ⟧ ;

sort Expression 
| sugar ⟦  ( ⟨Expression#e⟩ ) ⟧@16 → #e
| ⟦ ⟨SimpleLiteral⟩ ⟧@16 | ⟦ ⟨Variable⟩ ⟧@16 | ⟦ this ⟧@16 | ⟦ new ⟨Identifier⟩ ( ) ⟧@16
| ⟦ ⟨Expression@15⟩ . ⟨Identifier⟩ ⟧@15
| ⟦ ⟨Expression@15⟩ [ ⟨Expression⟩ ] ⟧@15
| ⟦ ⟨Expression@14⟩ ( ⟨Expression⟩ ) ⟧@14
| ⟦ ⟨Expression@14⟩ ( ) ⟧@14
| ⟦ ⟨Expression@13⟩ ++ ⟧@13
| ⟦ ⟨Expression@13⟩ -- ⟧@13
| ⟦ ! ⟨Expression@12⟩ ⟧@12
| ⟦ ~ ⟨Expression@12⟩ ⟧@12
| ⟦ - ⟨Expression@12⟩ ⟧@12
| ⟦ + ⟨Expression@12⟩ ⟧@12
| ⟦ ⟨Expression@11⟩ * ⟨Expression@12⟩ ⟧@11
| ⟦ ⟨Expression@11⟩ / ⟨Expression@12⟩ ⟧@11
| ⟦ ⟨Expression@11⟩ % ⟨Expression@12⟩ ⟧@11
| ⟦ ⟨Expression@10⟩ + ⟨Expression@11⟩ ⟧@10
| ⟦ ⟨Expression@10⟩ - ⟨Expression@11⟩ ⟧@10
| ⟦ ⟨Expression@10⟩ < ⟨Expression@10⟩ ⟧@9
| ⟦ ⟨Expression@10⟩ > ⟨Expression@10⟩ ⟧@9
| ⟦ ⟨Expression@10⟩ <= ⟨Expression@10⟩ ⟧@9
| ⟦ ⟨Expression@10⟩ >= ⟨Expression@10⟩ ⟧@9
| ⟦ ⟨Expression@9⟩ == ⟨Expression@9⟩ ⟧@8
| ⟦ ⟨Expression@9⟩ != ⟨Expression@9⟩ ⟧@8
| ⟦ ⟨Expression@7⟩ & ⟨Expression@8⟩ ⟧@7
| ⟦ ⟨Expression@6⟩ ^ ⟨Expression@7⟩ ⟧@6
| ⟦ ⟨Expression@5⟩ | ⟨Expression@6⟩ ⟧@5
| ⟦ ⟨Expression@4⟩ && ⟨Expression@5⟩ ⟧@4
| ⟦ ⟨Expression@3⟩ || ⟨Expression@4⟩ ⟧@3
| ⟦ ⟨Expression@3⟩ ? ⟨Expression@2⟩ : ⟨Expression@2⟩ ⟧@2
| ⟦ ⟨Expression@2⟩ = ⟨Expression@1⟩ ⟧@1
| ⟦ ⟨Expression@2⟩ = ⟨ComplexLiteral⟩ ⟧@1
| ⟦ ⟨Expression@2⟩ += ⟨Expression@1⟩ ⟧@1
| ⟦ ⟨Expression@1⟩ , ⟨Expression⟩ ⟧
;
//TYPE ATTRIBUTES


//atribute that represents a typelist relevant to an expression
//mainly for argument *lists i.e PRODUCT TYPES
//it is synthesized from the t (Type) one
//mainly an enhanced type attrubute to easily check FUNCTION applications
//PT STANDS FOR PRODUCT TYPES
//it replaces the usual t attribute (which is the singleton product here!)

attribute ↑pt(Typelist);
sort Expression | ↑pt;
//trivial -
⟦ ⟨SimpleLiteral#1 ↑t(Type#t) ⟩⟧↑pt(Typelist ⟦⟨Type #t⟩⟧);
 
 
⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ ++ ⟧↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);

 ⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ -- ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);
//negation on booleans
 ⟦ ! ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦boolean⟧⟩⟧)⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦boolean⟧⟩⟧);
//TILDE ON NUMBERS
 ⟦ ~ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);
//SIGNED NUMBERS
 ⟦ - ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);
 ⟦ + ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);

//MUL DIV NUMBERS

 ⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ * ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);
 ⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧ ) ⟩ / ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);
 ⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ % ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧ )⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧ );

//PLUS FOR NUMBERS
 ⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧) ⟩ + ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧ )⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);

//PLUS FOR Strings
 ⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦string⟧⟩⟧) ⟩ + ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦string⟧⟩⟧ )⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦string⟧⟩⟧);

//SUB NUMBERS
⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧) ⟩ - ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧ )⟩ ⟧ ↑pt( Typelist  ⟦⟨Type ⟦number⟧⟩⟧ );
//CONJUNCTIoN BOOLEANS

⟦  ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦boolean⟧⟩⟧)⟩ &  ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦boolean⟧⟩⟧)⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦boolean⟧⟩⟧ ); 
//Exp numbers
⟦  ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧ )⟩ ^  ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧); 
//PIPE NUMBERS
⟦  ⟨Expression#1 ↑pt(#t)⟩ |  ⟨Expression#2 ↑pt(#t )⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);
//ARRAY APPLICATION
⟦ ⟨Expression#1 ↑pt(Typelist ⟦⟨Type#t2⟩ [ ] ⟧)⟩ [ ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧)⟩  ] ⟧ ↑pt(Typelist ⟦⟨Type #t2⟩⟧);

//COMPARISONS STRING/NUM =>BOOL
⟦  ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧ )⟩ >  ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt( Typelist ⟦⟨Type ⟦boolean⟧⟩⟧ ); 

⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧)⟩ >  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧)⟩ ⟧ ↑pt( Typelist ⟦⟨Type ⟦boolean⟧⟩⟧ ); 

⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧)⟩ <  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧)⟩ ⟧ ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧ ); 

⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧)⟩ <  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt( Typelist ⟦⟨Type ⟦boolean⟧⟩⟧ );  

⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧)⟩ >=  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧)⟩⟧ ↑pt( Typelist ⟦⟨Type ⟦boolean⟧⟩⟧ );

⟦  ⟨Expression#1 ↑pt(Typelist⟦⟨Type ⟦string⟧⟩⟧)⟩ >=  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧)⟩⟧ ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧ );

⟦  ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧ )⟩ <=  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧ );

⟦  ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦string⟧⟩⟧)⟩ <=  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧)⟩ ⟧ ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧);
//APPLICABLE IMPORTANT

⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦ ( ) => ⟨Type#2⟩ ⟧⟩⟧) ⟩ ( ) ⟧ ↑pt(Typelist ⟦⟨Type #2⟩⟧ );
⟦ ⟨Expression#1 ↑pt(Typelist ⟦⟨Type⟦ ( ⟨Formals#3⟩) => ⟨Type#2⟩ ⟧⟩⟧) ⟩
 ( ⟨Expression#4 ↑pt(#5) ⟩)⟧ 
↑pt(Equiv(FormalstoList(#3),#5));

//BOOLEAN EQUALITY
⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type#1⟩ ⟧)⟩ == ⟨Expression#2 ↑pt(Typelist ⟦⟨Type#1⟩ ⟧)⟩ ⟧ ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧); 
//boolean inequality
⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type#1⟩ ⟧)⟩ !=  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type#1⟩ ⟧)⟩ ⟧ ↑pt(Type ⟦⟨Type ⟦boolean⟧⟩⟧ ); 
//boolean conjucntion
⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧)⟩ &&  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧)⟩ ⟧ ↑pt( Typelist ⟦⟨Type ⟦boolean⟧⟩⟧); 
//boolean disjuntion
⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧)⟩ ||  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧)⟩ ⟧ ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧);
//question mark
⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧)⟩ ?  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type#2⟩ ⟧)⟩ : ⟨Expression#3 ↑pt(Typelist ⟦⟨Type#4⟩ ⟧)⟩ ⟧ 
// Questionmark scheme applies to types
↑pt(QuestionMark(#2,#4)); 
//LVALUE CHECK TODO
//ASSIGNMENTS
//complexobj TODO
//this should be delayed on lvalue check



⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type#2⟩ ⟧) ↑lvalue(⟦Tru⟧)⟩ =  ⟨Expression#3 ↑pt(Typelist ⟦⟨Type#4⟩ ⟧)⟩ ⟧ ↑pt( Compatible(#2,#4)); 
//assignment compatibility checked on types

//complexarrays have simple type attribute not pt
⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type#2⟩ ⟧)⟩ =  ⟨ComplexLiteral#3 ↑t(#4)⟩ ⟧ ↑pt(Compatible(#2,#4) ); 
//complexobj TODO?? verify complexileteralobj type
//⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type#2⟩ ⟧)⟩ =  ⟨ComplexLiteralObject#2 ↑t(#t2)⟩ ⟧ ↑t( #t2 ); 

//lvalue check has to happen here simultaneously
⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧)⟩ += ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧);
⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧)⟩ += ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧)⟩ ⟧ ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧);
//here due to associativiety the second list should be singleton
 ⟦ ⟨Expression#1 ↑pt(Typelist #ls) ⟩ , ⟨Expression#2 ↑pt(Typelist #ls2)⟩ ⟧↑pt(Typelist ⟦AppendSingleton ⟨Typelist#ls⟩ ⟨Typelist#ls⟩⟧);

attribute ↑lval(Boolean);

sort Expression | ↑lval;
⟦ ⟨Variable#1⟩ ⟧↑lval( ⟦⟨Boolean ⟦tru⟧⟩⟧);
⟦ this ⟧↑lval( ⟦⟨Boolean ⟦fls⟧⟩⟧);
⟦ new ⟨Identifier#1⟩ ( ) ⟧↑lval( ⟦⟨Boolean ⟦fls⟧⟩⟧);

 ⟦ ⟨Expression#1⟩ . ⟨Identifier#2⟩ ⟧↑lval( ⟦⟨Boolean ⟦tru⟧⟩⟧);
⟦ ⟨SimpleLiteral#1 ⟩⟧↑lval( ⟦⟨Boolean ⟦fls⟧⟩⟧);

 ⟦ ⟨Expression#1⟩ ++ ⟧↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧);

 ⟦ ⟨Expression#1⟩ -- ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧);
//negation on booleans
 ⟦ ! ⟨Expression#1⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧);
//TILDE ON NUMBERS
 ⟦ ~ ⟨Expression#1⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧);
//SIGNED NUMBERS
 ⟦ - ⟨Expression#1⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧);
 ⟦ + ⟨Expression#1⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧);

//MUL DIV NUMBERS

 ⟦ ⟨Expression#1⟩ * ⟨Expression#2⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧);
 ⟦ ⟨Expression#1 ⟩ / ⟨Expression#2 ⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧);
 ⟦ ⟨Expression#1 ⟩ % ⟨Expression#2⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧);

//PLUS 
 ⟦ ⟨Expression#1  ⟩ + ⟨Expression#2⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧);

//SUB
⟦ ⟨Expression#1⟩ - ⟨Expression#2 ⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ );
//CONJUNCTIoN BOOLEANS

⟦  ⟨Expression#1⟩ &  ⟨Expression#2 ⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ ); 
//Exponantiation numbers
⟦  ⟨Expression#1 ⟩ ^  ⟨Expression#2⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ ); 
//PIPE NUMBERS
⟦  ⟨Expression#1⟩ |  ⟨Expression#2⟩ ⟧ ↑lval( ⟦⟨Boolean ⟦fls⟧⟩⟧ );
//ARRAY APPLICATION
⟦ ⟨Expression#1⟩ [ ⟨Expression#2 ⟩  ] ⟧ ↑lval(⟦⟨Boolean ⟦tru⟧⟩⟧ );

//COMPARISONS
⟦  ⟨Expression#1⟩ >  ⟨Expression#2⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ );

⟦  ⟨Expression#1⟩ <  ⟨Expression#2 ⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ ); 

⟦  ⟨Expression#1⟩ >=  ⟨Expression#2 ⟩⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ );


⟦  ⟨Expression#1 ⟩ <=  ⟨Expression#2⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ );

//APPLICABLE

⟦ ⟨Expression#1  ⟩ ( ) ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ );
⟦ ⟨Expression#1  ⟩
 ( ⟨Expression#4 ⟩)⟧ 
↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ );

⟦  ⟨Expression#1 ⟩ == ⟨Expression#2 ⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ );
⟦  ⟨Expression#1⟩ !=  ⟨Expression#2 ⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ );

⟦  ⟨Expression#1 ⟩ &&  ⟨Expression#2 ⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ ); 
⟦  ⟨Expression#1 ⟩ ||  ⟨Expression#2 ⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ );
⟦  ⟨Expression#1 ⟩ ?  ⟨Expression#2 ⟩ : ⟨Expression#3 ⟩ ⟧ 
↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ ); 

⟦  ⟨Expression#1⟩ =  ⟨Expression#3⟩ ⟧↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ );; 

⟦  ⟨Expression#1 ⟩ =  ⟨ComplexLiteralArray#3 ⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ );
//complexlits assignments are not lvalues of course
⟦  ⟨Expression#1 ⟩ =  ⟨ComplexLiteralObject#2 ⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ );; 


⟦  ⟨Expression#1 ⟩ += ⟨Expression#2 ⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ );

⟦  ⟨Expression#1 ⟩ += ⟨Expression#2 ⟩ ⟧ ↑lval(⟦⟨Boolean ⟦fls⟧⟩⟧ );

//EXPRESSIONS HAVE PRODUCT TYPES FOR THE COMPILER - AT THIS POINT TYPESCRIPT TYPES 
//ARE ABSORBED AS SINGLETON PRODUCTS
attribute ↑pt(Typelist);
sort Expression | ↑pt;
⟦ ⟨SimpleLiteral#1 ↑t(Type#t) ⟩⟧↑pt(Typelist ⟦⟨Type #t⟩⟧);
//lvalue check!
//TODO
// thar does not look like synthesizing here since it requires context
//⟦ ⟨Expression#1⟩ . ⟨Identifier⟩ ⟧@15
 ⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ ++ ⟧↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);

 ⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ -- ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);
//negation on booleans
 ⟦ ! ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦boolean⟧⟩⟧)⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦boolean⟧⟩⟧);
//TILDE ON NUMBERS
 ⟦ ~ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);
//SIGNED NUMBERS
 ⟦ - ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);
 ⟦ + ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);

//MUL DIV NUMBERS

 ⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ * ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);
 ⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧ ) ⟩ / ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);
 ⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ % ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧ )⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧ );

//PLUS FOR NUMBERS
 ⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧) ⟩ + ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧ )⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);

//PLUS FOR Strings
 ⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦string⟧⟩⟧) ⟩ + ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦string⟧⟩⟧ )⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦string⟧⟩⟧);

//SUB NUMBERS
⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧) ⟩ - ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧ )⟩ ⟧ ↑pt( Typelist  ⟦⟨Type ⟦number⟧⟩⟧ );
//CONJUNCTIoN BOOLEANS

⟦  ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦boolean⟧⟩⟧)⟩ &  ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦boolean⟧⟩⟧)⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦boolean⟧⟩⟧ ); 
//Exp numbers
⟦  ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧ )⟩ ^  ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧); 
//PIPE NUMBERS
⟦  ⟨Expression#1 ↑pt(#t)⟩ |  ⟨Expression#2 ↑pt(#t )⟩ ⟧ ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧);
//ARRAY APPLICATION
⟦ ⟨Expression#1 ↑pt(Typelist ⟦⟨Type#t2⟩ [ ] ⟧)⟩ [ ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧)⟩  ] ⟧ ↑pt(Typelist ⟦⟨Type #t2⟩⟧);

//COMPARISONS STRING/NUM =>BOOL
⟦  ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧ )⟩ >  ⟨Expression#2 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt( Typelist ⟦⟨Type ⟦boolean⟧⟩⟧ ); 

⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧)⟩ >  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧)⟩ ⟧ ↑pt( Typelist ⟦⟨Type ⟦boolean⟧⟩⟧ ); 

⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧)⟩ <  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧)⟩ ⟧ ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧ ); 

⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧)⟩ <  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt( Typelist ⟦⟨Type ⟦boolean⟧⟩⟧ );  

⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧)⟩ >=  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧)⟩⟧ ↑pt( Typelist ⟦⟨Type ⟦boolean⟧⟩⟧ );

⟦  ⟨Expression#1 ↑pt(Typelist⟦⟨Type ⟦string⟧⟩⟧)⟩ >=  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧)⟩⟧ ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧ );

⟦  ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦number⟧⟩⟧ )⟩ <=  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧ );

⟦  ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦string⟧⟩⟧)⟩ <=  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧)⟩ ⟧ ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧);
//APPLICABLE

⟦ ⟨Expression#1 ↑pt(Typelist  ⟦⟨Type ⟦ ( ) => ⟨Type#2⟩ ⟧⟩⟧) ⟩ ( ) ⟧ ↑pt(Typelist ⟦⟨Type #2⟩⟧ );
⟦ ⟨Expression#1 ↑pt(Typelist ⟦⟨Type⟦ ( ⟨Formals#3⟩) => ⟨Type#2⟩ ⟧⟩⟧) ⟩
 ( ⟨Expression#4 ↑pt(#5) ⟩)⟧ 
↑pt(Equiv(FormalstoList(#3),#5));

//BOOLEAN EQUALITY
⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type#1⟩ ⟧)⟩ == ⟨Expression#2 ↑pt(Typelist ⟦⟨Type#1⟩ ⟧)⟩ ⟧ ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧); 
//boolean inequality
⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type#1⟩ ⟧)⟩ !=  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type#1⟩ ⟧)⟩ ⟧ ↑pt(Type ⟦⟨Type ⟦boolean⟧⟩⟧ ); 
//boolean conjucntion
⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧)⟩ &&  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧)⟩ ⟧ ↑pt( Typelist ⟦⟨Type ⟦boolean⟧⟩⟧); 
//boolean disjuntion
⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧)⟩ ||  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧)⟩ ⟧ ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧);
//question mark
⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦boolean⟧⟩⟧)⟩ ?  ⟨Expression#2 ↑pt(Typelist ⟦⟨Type#2⟩ ⟧)⟩ : ⟨Expression#3 ↑pt(Typelist ⟦⟨Type#4⟩ ⟧)⟩ ⟧ 
// Questionmark scheme applies to types
↑pt(QuestionMark(#2,#4)); 
//complexobj TODO



⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type#2⟩ ⟧)⟩ =  ⟨Expression#3 ↑pt(Typelist ⟦⟨Type#4⟩ ⟧)⟩ ⟧ ↑pt( Compatible(#2,#4)); 
//assignment compatibility checked on types
//complexarrays have simple type attribute not pt we absorb to singleton product as usual
⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type#2⟩ ⟧)⟩ =  ⟨ComplexLiteralArray#3 ↑t(#4)⟩ ⟧ ↑pt(Compatible(#2,#4) ); 
//complexobj TODO?? verify complexileteralobj type
//⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type#2⟩ ⟧)⟩ =  ⟨ComplexLiteralObject#2 ↑t(#t2)⟩ ⟧ ↑t( #t2 ); 

⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧)⟩ += ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧)⟩ ⟧ ↑pt(Typelist ⟦⟨Type ⟦number⟧⟩⟧);
⟦  ⟨Expression#1 ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧)⟩ += ⟨Expression#2 ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧)⟩ ⟧ ↑pt(Typelist ⟦⟨Type ⟦string⟧⟩⟧);


//LVALUED-NESS CHECK FOR EXPRESSIONS
sort Expression | scheme ⟦AssignmentChck ⟨Expression⟩⟧;
⟦  ⟨Expression#1 ↑lval( ⟦⟨Boolean ⟦tru⟧⟩⟧)⟩ =  ⟨Expression#3⟩ ⟧ → ⟦  ⟨Expression#1⟩ =  ⟨Expression#3⟩ ⟧; 
⟦  ⟨Expression#1 ↑lval( ⟦⟨Boolean ⟦tru⟧⟩⟧)⟩ += ⟨Expression#2⟩ ⟧ → ⟦ ⟨Expression#1⟩ =  ⟨Expression#2⟩ ⟧; 
default ⟦  ⟨Expression#1⟩⟧ → ⟦ ⟨Expression#1⟩⟧; 

//EXTENDING LVALUE-CHECK FOR THE WHOLE PROGRAM
//Starting from scopes and statements
sort Scope | scheme ⟦AssignmentChck_sc ⟨Scope⟩⟧;
 ⟦AssignmentChck_sc ⟨Scope ⟦ var v : ⟨Type#1⟩ ; ⟨Scope#2⟩ ⟧ ⟩ ⟧ →  ⟦AssignmentChck_sc ⟨Scope#2 ⟩ ⟧;
 ⟦AssignmentChck_sc ⟨Scope ⟦ ⟨Statement#1⟩ ⟨Scope#2⟩ ⟧ ⟩ ⟧ →  ⟦AssignmentChck_sc_h ⟨Statement  ⟦AssignmentChck_st ⟨Statement#1⟩ ⟧⟩  ⟨Scope#2⟩⟧;
 ⟦AssignmentChck_sc ⟨Scope ⟦ ⟨Statement#1⟩ ⟧⟩ ⟧ →  ⟦⟨Scope  ⟦AssignmentChck_st ⟨Statement#1⟩ ⟧⟩⟧;
 ⟦AssignmentChck_sc ⟨Scope ⟦ var v : ⟨Type#1⟩ ; ⟧ ⟩ ⟧ → 
 ⟦ ⟨Scope ⟦ var v : ⟨Type#1⟩ ; ⟧ ⟩ ⟧ ;


sort Scope | scheme ⟦AssignmentChck_sc_h  ⟨Statement⟩ ⟨Scope⟩⟧;
 ⟦AssignmentChck_sc_h  ⟨Statement#1⟩ ⟨Scope#2⟩⟧ →  ⟦ AssignmentChck_sc ⟨Scope#2⟩⟧;

//EXTENDING Lvalue check for the whole program
//CHECKS HAVE TO BE RECURSIVELY CALLED WHENEVER SCOPE APPEARS


sort Declarations | scheme ⟦ AssignmentChck_decl  ⟨Declarations⟩ ⟧ ;

⟦ AssignmentChck_decl  ⟨Declarations ⟦ class ⟨Identifier#1⟩ {  }⟨DeclarationsTail#2⟩ ⟧ ⟩ ⟧ →  ⟦ AssignmentChck_decl_tl ⟨DeclarationsTail#2⟩⟧;
//skip members since they don't have assignments
⟦  AssignmentChck_decl ⟨Declarations ⟦ class ⟨Identifier#1⟩ {⟨ Member#2⟩ ⟨ MembersTail#3⟩}  ⟨DeclarationsTail#4⟩ ⟧⟩ ⟧;
→
⟦ AssignmentChck_decl ⟨Declarations ⟦ class ⟨Identifier#1⟩ {⟨ Member#2⟩ ⟨ MembersTail#3⟩}  ⟨DeclarationsTail ⟦AssignmentChck_decl_tl  ⟨DeclarationsTail#4⟩⟧ ⟩ ⟧;⟩ ⟧

⟦ AssignmentChck_decl ⟨Declarations ⟦ function ⟨Identifier#1⟩ ⟨CallSignatureAndScope#2⟩⟨DeclarationsTail#3⟩ ⟧ ⟩ ⟧→  ⟨Declarations ⟦ function ⟨Identifier#1⟩ ⟨CallSignatureAndScope ⟦AssignmnetChck_css ⟨CallSignatureAndScope#2⟩⟧ ⟩⟨DeclarationsTail ⟦ AssignmentChck_decl_tl ⟨DeclarationsTail#2⟩⟧  ⟩ ⟧ ⟩;


sort DeclarationsTail | scheme  ⟦AssignmentChck_decl_tl  ⟨DeclarationsTail⟩⟧;

sort CallSignatureAndScope | scheme ⟦ AssignmnetChck_css ⟨CallSignatureAndScope⟩⟧;
//SIMILARILY we obtaion AN LVALUE CHECK FOR THE WHOLE PROGRAM .... 

sort Program | scheme ⟦ LvalueCheck ⟨Program⟩⟧;




//| ⟦ var ⟨[v:Identifier]⟩ : ⟨Type⟩ ; ⟨Scope[v:Identifier]⟩ ⟧
//| ⟦ ⟨Statement⟩ ⟨Scope⟩ ⟧
//| ⟦ ⟨Statement⟩  ⟧
//| ⟦ var ⟨[v:Identifier]⟩ : ⟨Type⟩ ;⟧
//;

//STATEMENT - RELEVANT ATTRIBUTES TODO
sort Scope | scheme ⟦AssignmentChck_s ⟨Scope⟩⟧;


sort Statement | scheme ⟦AssignmentChck_st ⟨Statement⟩ ⟧;
⟦AssignmentChck_st  ⟨Statement ⟦⟨Expression#1⟩ ;⟧⟩ ⟧→  ⟦⟨Statement ⟦AssignmentChck ⟨Expression#1⟩ ;⟧⟩ ⟧;
⟦AssignmentChck_st ⟨Statement ⟦;⟧⟩⟧→  ⟦⟨Statement ⟦;⟧⟩⟧;
⟦AssignmentChck_st ⟨Statement ⟦ { } ⟧⟩⟧→  ⟦⟨Statement ⟦{ }⟧⟩⟧ ;

⟦AssignmentChck_st  ⟨Statement ⟦if (⟨Expression#1⟩) ⟨IfTail#2⟩ ⟧⟩ ⟧→  ⟦AssignmentChck_help  ⟨IfTail#1⟩⟨Expression#2⟩⟧   ;
⟦ AssignmentChck_st  ⟨Statement ⟦while (⟨Expression#1⟩) ⟨Statement#2⟩ ⟧⟩ ⟧ →  ⟦⟨Statement ⟦while (⟨Expression ⟦AssignmentChck ⟨Expression#1⟩⟧⟩)
																			⟨Statement#2⟩ ⟧⟩ ⟧  ;
⟦ AssignmentChck_st  ⟨Statement ⟦ for ( var v : ⟨Type#1⟩ in ⟨Expression#2⟩ ) ⟨Statement#3⟩ ⟧⟩ ⟧ 
→
⟦AssignmentChck_help2 ⟨Statement#3⟩ ⟨Expression#2⟩⟧; 
⟦ AssignmentChck_st  ⟨Statement ⟦ return  ⟨Expression#1⟩ ;⟧⟩ ⟧ →  ⟦ return ⟨Expression ⟦AssignmentChck ⟨Expression#1⟩⟧⟩ ;⟧;
⟦ AssignmentChck_st  ⟨Statement ⟦ return   ;⟧⟩ ⟧ →  ⟦ return ; ⟧;




sort IfTail | scheme ⟦AssignmentChck_tl  ⟨IfTail⟩⟧;
 
sort Statement | scheme ⟦AssignmentChck_help ⟨IfTail⟩ ⟨Expression⟩⟧;
 ⟦AssignmentChck_help ⟨IfTail#1⟩ ⟨Expression#2⟩⟧ →  ⟦⟨Statement ⟦if (⟨Expression ⟦AssignmentChck ⟨Expression#2⟩⟧⟩) 
																		⟨IfTail ⟦AssignmentChck_tl ⟨IfTail#1⟩⟧⟩ ⟧⟩ ⟧  ;

 sort Statement | scheme ⟦AssignmentChck_help2 ⟨Statement⟩ ⟨Expression⟩⟧;
 ⟦AssignmentChck_help2 ⟨Statement#1⟩ ⟨Expression#2⟩⟧  →
⟦ ⟨Statement ⟦ for ( var v : ⟨Type#1⟩ in ⟨Expression⟦AssignmentChck ⟨Expression#2⟩⟧⟩ ) ⟨Statement#1⟩ ⟧⟩ ⟧;

 // SIMILARILY ONE CAN EXTEND TRIVIALLY THE LVALUE ANALYSIS FOR THE WHOLE PROGRAM - DISTRIBUTING THE ANALYSIS TO 
 //SCOPES AND STATEMENTS
 //WE WILL NOT DO IT BECAUSE IT IS TEDIOUS AND THE HIGH-LIGHTS OF THIS PROCESS ARE SIMILAR TO THE ABOVE
 // SOME NEED FOR HELPER FUNCTIONS MAYBE REQUIRED BUT WE SKETCH THAT ALREADY!

 
 //⟦ {  } ⟧  → ⟦ ⟨Scope ⟦Assignme⟦ntChck_sc ⟨Scope⟩⟧#1⟩⟧⟩⟧; 

//| ⟦ ⟨Expression⟩ ; ⟧
//| ⟦  ; ⟧
//| ⟦ if ( ⟨Expression⟩ ) ⟨IfTail⟩ ⟧
//| ⟦ while ( ⟨Expression⟩ ) ⟨Statement⟩ ⟧
//| ⟦ for ( var ⟨[v:Identifier]⟩ : ⟨Type⟩ in ⟨Expression⟩ ) ⟨Statement[v:Identifier]⟩ ⟧
//| ⟦ return ⟨Expression⟩ ; ⟧
//|⟦ return ; ⟧
//;

//sort Statement | scheme ⟦AssignmentChck_tl ⟨IfTail⟩⟧;


//sort Scope | scheme ⟦AssignmentChck_s ⟨Scope⟩⟧;
//⟦  ⟨Expression#1 ↑lval( ⟦⟨Boolean ⟦tru⟧⟩⟧)⟩ =  ⟨Expression#3⟩ ⟧ → ⟦  ⟨Expression#1⟩ =  ⟨Expression#3⟩ ⟧; 
//⟦  ⟨Expression#1 ↑lval( ⟦⟨Boolean ⟦tru⟧⟩⟧)⟩ += ⟨Expression#2⟩ ⟧ → ⟦ ⟨Expression#1⟩ =  ⟨Expression#2⟩ ⟧; 
//default ⟦  ⟨Expression#1⟩⟧ → ⟦ ⟨Expression#1⟩⟧; 




//DOWNWARD ATTRIBUTE CURRENT CLASS CONTEXT CurClOption DEFINED BELOW
	
//HELPER SORT
sort CurClOption
|⟦⟨Identifier⟩  ⟧ ;
|⟦ ⟧ ;


//this attribute is the class-local contex to use with "this"
//for toplevel functions is Empty (i.e "this" does not make sense)
attribute ↓current(CurClOption);


//HELPER SORT 
//EXTRA TYPE CLASSES IN THE TOPLEVEL
//TO BE UTILIZED SO THAT WE CHECK WELLFORMEDNESS OF FUNCTIONS IN THE TOP LEVEL
// AND MEMBER DECLARATIONS INSIDE CLASSES
//toplevelist of declaration signatures
//to be turned 
//MAINLY JUST ACCUMULATE ALL CLASS NAMES WE HAVE SEEN!
//MAYBE WE SHOULD TRANSFORM TO A HACS CONTEXT TO CHECK UNICITY? YES WE DID!!! SEE LATER!
sort TopLevelList | ⟦  ⟨Identifier⟩ ⟨Type⟩; ⟨TopLevelList⟩ ⟧ | ⟦⟧ ;

//UPWARD ATTRIBUTE
attribute  ↑toplevels(TopLevelList);
//DOWNWORD ATTRUBUTE for class types (e.g. Car:Car)
attribute ↓top{Identifier : Type };

//toplevels gets consumes into top


//HELPER SORT UNION OF FUN AND CLASSES FOR TOPLEVEL DECLARATIONS (DOES NOT INCLUDE MEMBERS OF CLASSES!)
sort Ftu
| ⟦  Trm ⟨Type⟩⟧ //For functional toplevel defs
| ⟦ Cl ⟨FormalsOption⟩⟧; //for class toplevel defs 
//HELPER SORT
sort SigList | ⟦  ⟨Identifier⟩ ⟨Ftu⟩; ⟨SigList⟩ ⟧ | ⟦ ⟧ ;
//UPWARD ATTRIBUTE SIGLOB ACCUMULATES WELLFORMED  CLASSES' AND FUN'S SIGNATURES
//USING TOP
attribute ↑sglob(SigList);
//DOWNWARD ATTRIBUTE SIGS :WHEN SGLOB TUNRS TO A CONTEXT FOR THE CONTINUATION OF THE 
//TYPE ANALYSIS 
attribute  ↓sigs{Identifier : Ftu }; 
//context induced after accumulating WELL FORMED classes and functiondeclarations

//DECLARATIONS AND THEIR ATTRIBUTE CONSTRUCTION AND THEIR ANALYSIS

sort Declarations 
| ⟦ class ⟨Identifier⟩ {  }⟨DeclarationsTail⟩ ⟧;
| ⟦  class ⟨Identifier⟩ {⟨ Member⟩ ⟨ MembersTail⟩}  ⟨DeclarationsTail⟩ ⟧;
| ⟦ function ⟨Identifier⟩ ⟨CallSignatureAndScope⟩⟨DeclarationsTail⟩ ⟧;
//TOPLEVELS --SEE THAT MEMBERS ARE IRRELEVANT AT THIS POINT

sort Declarations | ↑toplevels ;
 ⟦ class ⟨Identifier#1⟩ {  } ⟨DeclarationsTail#3 ↑toplevels(#2)⟩ ⟧ ↑toplevels(⟦  ⟨Identifier#1⟩⟨Type ⟦⟨Identifier#1⟩⟧⟩; ⟨TopLevelList#2⟩ ⟧) ;
⟦  class ⟨Identifier#1⟩ {⟨ Member#2⟩ ⟨ MembersTail#3⟩}  ⟨DeclarationsTail#4 ↑toplevels(#5)⟩ ⟧
↑toplevels(⟦  ⟨Identifier#1⟩⟨Type ⟦⟨Identifier#1⟩⟧⟩ ; ⟨TopLevelList#5⟩ ⟧) ;

 ⟦ function ⟨Identifier#1⟩ ⟨CallSignatureAndScope#2⟩⟨DeclarationsTail#3 ↑toplevels(#4)⟩ ⟧
 ↑toplevels(⟦  ⟨TopLevelList#4⟩ ⟧)
;

//WELLTYPEDNESS (TYPABILITY OF TYPE DECLARATIONS) CHECK UNDER TOPLEVEL
sort Declarations | WellFormed (Declarations) ↓top;
//trivial function just calling the approproate functions on each declaration
 WellFormed (⟦ class ⟨Identifier#1⟩ {  } ⟨DeclarationsTail#2  ⟩⟧ ) ↓top(#g) →
//a no members class is wellformed
 ⟦ class ⟨Identifier#1⟩ {  }   ⟨DeclarationsTail ⟦WellFormed_dt  ⟨DeclarationsTail#2⟩⟧  ↓top(#g)⟩⟧;
//for a class with members we should check that member typing is welldeclared
WellFormed ( ⟦  class ⟨Identifier#1⟩ {⟨ Member#2⟩ ⟨ MembersTail#3⟩}  ⟨DeclarationsTail#4⟩ ⟧) ↓top(#g)→

⟦  class ⟨Identifier#1⟩ { ⟨Member ⟦WellDeclared_m ⟨Member#2⟩⟧ ↓top(#g) ⟩   ⟨ MembersTail ⟦WellDeclared_mtl ⟨MembersTail#3⟩⟧ ↓top(#g)⟩}  ⟨DeclarationsTail ⟦WellFormed_dt  ⟨DeclarationsTail#4⟩⟧ ↓top(#g)⟩ ⟧;
//similarly for function definitions
WellFormed (⟦ function ⟨Identifier#1⟩ ⟨CallSignatureAndScope#2⟩⟨DeclarationsTail#3 ⟩ ⟧) ↓top(#g)→
⟦ function ⟨Identifier#1⟩ ⟨CallSignatureAndScope ⟦WellDeclared_cs ⟨CallSignatureAndScope#2⟩⟧ ↓top(#g)⟩⟨DeclarationsTail  ⟦WellFormed_dt  ⟨DeclarationsTail#3⟩⟧ ↓top(#g)⟩ ⟧;






 
//SIGNATURE GLOBAL --SEE THAT MEMBERS HERE ARE RELEVANT

sort Declarations | ↑sglob;
 ⟦ class ⟨Identifier#1⟩ {  }⟨DeclarationsTail#2 ↑sglob(#tlsig)⟩ ⟧ ↑sglob( ⟦⟨Identifier#1⟩ Cl ⟨FormalsOption ⟦ ⟧⟩; ⟨SigList #tlsig⟩⟧);
 ⟦  class ⟨Identifier#1⟩ {⟨ Member#2 ↑membersig(#m)⟩ ⟨ MembersTail#5 ↑tailsig(#4) ⟩}  ⟨DeclarationsTail#6 ↑sglob(#tlsig) ⟩ ⟧↑sglob (⟦⟨Identifier#1⟩ Cl ⟨Formal #m⟩,⟨Formals #4⟩; ⟨SigList #tlsig⟩⟧) ;
⟦ function ⟨Identifier#1⟩ ⟨CallSignatureAndScope#2 ↑t(#t)⟩⟨DeclarationsTail#3 ↑sglob(#tlsig)⟩ ⟧
↑sglob (⟦⟨Identifier#1⟩ Trm ⟨Type #t⟩; ⟨SigList #tlsig⟩⟧);


//SIMILARLY FOR DECLARATIONSTAIL
sort DeclarationsTail 
| ⟦ class ⟨Identifier⟩ {  }⟨DeclarationsTail⟩ ⟧;
| ⟦  class ⟨Identifier⟩ {⟨ Member⟩ ⟨ MembersTail⟩}  ⟨DeclarationsTail⟩ ⟧;
| ⟦ function ⟨Identifier⟩ ⟨CallSignatureAndScope⟩⟨DeclarationsTail⟩ ⟧;
| ⟦ ⟧;



//TOPLEVELS
sort DeclarationsTail |  ↑toplevels ;

 ⟦ class ⟨Identifier#1⟩ {  } ⟨DeclarationsTail#3 ↑toplevels(#2)⟩ ⟧ ↑toplevels(⟦ ⟨Identifier#1⟩⟨Type ⟦⟨Identifier#1⟩⟧⟩ ; ⟨TopLevelList#2⟩ ⟧) ;
⟦  class ⟨Identifier#1⟩ {⟨ Member#2⟩ ⟨ MembersTail#3⟩}  ⟨DeclarationsTail#4 ↑toplevels(#5)⟩ ⟧
 ↑toplevels(⟦ ⟨Identifier#1⟩⟨Type ⟦⟨Identifier#1⟩⟧⟩ ; ⟨TopLevelList#5⟩ ⟧) ;
 ⟦ function ⟨Identifier#1⟩ ⟨CallSignatureAndScope#2⟩⟨DeclarationsTail#3 ↑toplevels(#4)⟩ ⟧
  ↑toplevels(⟦  ⟨TopLevelList#4⟩ ⟧);
 ⟦ ⟧ ↑toplevels(⟦⟨TopLevelList⟦   ⟧⟩ ⟧);


//TRIVIAL FUNCTION INVOKING WELLFORMEDNESS (typeability) CHECKS ON A TAIL

sort DeclarationsTail | scheme ⟦WellFormed_dt ⟨DeclarationsTail⟩⟧ ↓top;

⟦WellFormed_dt  ⟨DeclarationsTail  ⟦class ⟨Identifier#1⟩ {  } ⟨DeclarationsTail#3⟩ ⟧⟩⟧ ↓top(#g) → 
 ⟦ class ⟨Identifier #1⟩ {  } ⟨DeclarationsTail ⟦WellFormed_dt ⟨DeclarationsTail#3⟩⟧ ↓top(#g)⟩⟧;
⟦WellFormed_dt  ⟨DeclarationsTail ⟦  class ⟨Identifier#1⟩ {⟨ Member#2⟩ ⟨ MembersTail#3⟩}  ⟨DeclarationsTail#4⟩ ⟧⟩⟧ ↓top(#g)→
//check if members are welldeclared
 ⟦  class ⟨Identifier#1⟩ { ⟨Member ⟦WellDeclared_m ⟨Member#2⟩⟧ ↓top(#g) ⟩   ⟨ MembersTail ⟦WellDeclared_mtl ⟨MembersTail#3⟩⟧ ↓top(#g)⟩}  ⟨DeclarationsTail ⟦WellFormed_dt ⟨DeclarationsTail#4⟩⟧ ↓top(#g)⟩ ⟧;

⟦WellFormed_dt ⟨DeclarationsTail  ⟦ function ⟨Identifier#1⟩ ⟨CallSignatureAndScope#2⟩⟨DeclarationsTail#3 ⟩ ⟧⟩⟧ ↓top(#g)→
⟦ function ⟨Identifier#1⟩ ⟨CallSignatureAndScope ⟦WellDeclared_cs ⟨CallSignatureAndScope#2⟩⟧ ↓top(#g)⟩⟨DeclarationsTail  ⟦WellFormed_dt ⟨DeclarationsTail#3⟩⟧ ↓top(#g)⟩ ⟧;
⟦WellFormed_dt ⟨DeclarationsTail ⟦⟧⟩⟧→⟦⟨DeclarationsTail ⟦⟧⟩⟧;

//SGLOB UPARROW ATTRIBUTE
sort DeclarationsTail | ↑sglob ;
 ⟦ class ⟨Identifier#1⟩ {  }⟨DeclarationsTail#2 ↑sglob(#tlsig)⟩ ⟧ ↑sglob( ⟦⟨Identifier#1⟩ Cl ⟨FormalsOption ⟦ ⟧⟩; ⟨SigList #tlsig⟩⟧);
 ⟦  class ⟨Identifier#1⟩ {⟨ Member#2 ↑membersig(#m)⟩ ⟨ MembersTail#5 ↑tailsig(#4) ⟩}  ⟨DeclarationsTail#6 ↑sglob(#tlsig) ⟩ ⟧↑sglob (⟦⟨Identifier#1⟩ Cl ⟨Formal #m⟩,⟨Formals #4⟩; ⟨SigList #tlsig⟩⟧) ;
 ⟦ function ⟨Identifier#1⟩ ⟨CallSignatureAndScope#2 ↑t(#t)⟩⟨DeclarationsTail#3 ↑sglob(#tlsig)⟩ ⟧
 ↑sglob(  ⟦⟨Identifier#1⟩ Trm ⟨Type #t⟩; ⟨SigList #tlsig⟩⟧ )
;
 ⟦ ⟧ ↑sglob(⟦   ⟧);

//MEMBERS and their attribute construction
sort Member 
| ⟦ ⟨Identifier⟩ : ⟨Type⟩ ; ⟧
| ⟦ ⟨Identifier⟩ ⟨CallSignatureAndScope⟩ ;⟧
;


//well declared member boils down to type existence under the toplevel context 
sort Member | scheme ⟦WellDeclared_m ⟨Member⟩⟧ ↓top;
⟦WellDeclared_m ⟨Identifier #1⟩ : ⟨Type #2⟩ ;⟧ ↓top(#g)→ ⟦⟨Member ⟦⟨Identifier #1⟩ : ⟨Type⟦Exists_t ⟨Type#2⟩⟧ ↓top(#g)⟩ ;⟧⟩⟧ ;
⟦WellDeclared_m ⟨Identifier #1⟩⟨CallSignatureAndScope#2 ⟩; ⟧ ↓top(#g)→ ⟦⟨Member ⟦⟨Identifier #1⟩  ⟨CallSignatureAndScope ⟦WellDeclared_cs ⟨CallSignatureAndScope#2⟩⟧ ↓top(#g)⟩ ;⟧⟩⟧ ;


//CHCKNG 
//UPARROW ATTRIBUTE
//MEMBER SIG
//THE MEMBERS CONTRIBUTION TO THE CLASS SIGNATURE
attribute  ↑membersig(Formal);

sort Member | ↑membersig;
⟦ ⟨Identifier#1⟩ : ⟨Type#2⟩ ; ⟧ ↑membersig(⟦⟨Formal ⟦⟨Identifier#1⟩ : ⟨Type#2⟩⟧⟩⟧);
⟦ ⟨Identifier#1⟩ ⟨CallSignatureAndScope#3 ↑t(#2)⟩ ;⟧
↑membersig(⟦⟨Formal ⟦⟨Identifier#1⟩ :⟨Type#2⟩⟧⟩⟧);


//MEMBERS TAIL SIMILARILY
sort MembersTail 
 | ⟦ ⟨ Member⟩ ⟨ MembersTail⟩⟧
  | ⟦  ⟧ ;

//chekign wellformendness of a tail regarding type signatures (type existence under the toplevel context)
sort MembersTail | scheme ⟦WellDeclared_mtl ⟨MembersTail⟩⟧ ↓top;
 //an empty tail is welltyped under any context
// otherwise we call welltyped on its head recursively
⟦WellDeclared_mtl ⟨Member#1⟩ ⟨MembersTail#2⟩ ⟧ ↓top(#g) →
 ⟦⟨Member ⟦WellDeclared_m ⟨Member#1⟩⟧ ↓top(#g) ⟩  ⟨MembersTail ⟦WellDeclared_mtl ⟨MembersTail#2⟩⟧↓top(#g) ⟩⟧ ;
⟦WellDeclared_mtl ⟨MembersTail ⟦ ⟧⟩⟧→  ⟦⟨MembersTail ⟦ ⟧⟩⟧;



//WITH UPARROW ATTRIBUTE  TAILSIG
//CONTRIBUTION OF THE TAIL OF MEMBERS TO THE SIGNATURE OF CLASS
attribute ↑tailsig(FormalsOption);
sort MembersTail | ↑tailsig;
 
⟦⟨Member#1 ↑membersig(#m) ⟩ ⟨MembersTail#2 ↑tailsig(#fs)⟩ ⟧  ↑tailsig(Concat(#m,#fs));
 ⟦⟨MembersTail ⟦  ⟧⟩ ⟧ ↑tailsig( ⟦⟨FormalsOption ⟦  ⟧⟩⟧); 




//CALLSIGNATUREANDSCOPE --RELEVANT ATTRIBUTES TODO
sort CallSignatureAndScope 
| ⟦ ( ) : ⟨Type⟩ { ⟨Scope⟩ } ⟧
| ⟦ ( ) : ⟨Type⟩ {  } ⟧
| ⟦ ( ⟨OpenCallSignatureAndScope⟩ ⟧             //open parenthesis.
;

//UPARROW ATTRIBUTE TYPE FOR CALLSIGANDSCOPE
//COMMENT: ONE COULD STAGE THE CONSTRUCTION HERE
//first: ignore the type in the scope in the synthesization 
//of the t and then verify that a callsignatureandscope is type correct
//see:inaccord_css scheme below
//this way you get an explicit error on return type/ body mismatch

sort CallSignatureAndScope | ↑t;
⟦ ( ) : ⟨Type#1⟩ { ⟨Scope#2⟩ } ⟧ ↑t( ⟦  ( )  => ⟨Type#1⟩ ⟧);
//here type should be void but this is checked later with inaccordance!
⟦ ( ) : ⟨Type#1⟩ {  } ⟧ ↑t( ⟦  ( )  => ⟨Type#1⟩ ⟧);
⟦ ( ⟨OpenCallSignatureAndScope#1 ↑t(#2)⟩ ⟧   ↑t(#2) ; 


//WELLFORMEDNESSOFFUNSIGNATURE UNDER A TOPLEVEL
//SCOPE TYPES ARE IRRELEVANT AT THAT POINT 
//ONLY THE WELLFORMEDNESS OF THE "CONTRACT" IS CHECKED

sort CallSignatureAndScope | scheme ⟦WellDeclared_cs ⟨CallSignatureAndScope⟩⟧ ↓top;
		           | scheme ⟦Inaccord_cs ⟨CallSignatureAndScope⟩⟧ ;

⟦ WellDeclared_cs ( ) : ⟨Type#1⟩ { ⟨Scope#2 ⟩ } ⟧ ↓top(#g) → ⟦⟨CallSignatureAndScope ⟦  ( ) : ⟨Type ⟦ Exists_t ⟨Type#1⟩ ⟧ ↓top(#g)⟩ { ⟨Scope#2 ⟩ } ⟧⟩⟧ ;
//in the case of empty scope only void could be given as a declared type
//but this is checked later
⟦ WellDeclared_cs ( ) : ⟨Type#1⟩ {  } ⟧ ↓top(#g) →  ⟦⟨CallSignatureAndScope ⟦  ( ) : ⟨Type ⟦ Exists_t ⟨Type#1⟩ ⟧ ↓top(#g)⟩ {  } ⟧⟩⟧ ;
⟦ WellDeclared_cs ( ⟨OpenCallSignatureAndScope#1 ⟩ ⟧ ↓top(#g)   →  ⟦⟨CallSignatureAndScope⟦ ( ⟨OpenCallSignatureAndScope ⟦ WellDeclared_ocs ⟨OpenCallSignatureAndScope#1⟩ ⟧ ↓top(#g)⟩ ⟧  ⟩⟧;  

//INACCORDNCE DEFINITION
//SHOULD RUN AFTER TA OF THE SCOPE TO CHECK CONFORMANCE
⟦ Inaccord_cs ( ) : ⟨Type#1⟩ { ⟨Scope#2 ↑t( ⟦⟨Type#1⟩ ⟧)⟩ } ⟧ → ⟦⟨CallSignatureAndScope ⟦  ( ) : ⟨Type#1⟩   { ⟨Scope#2 ⟩ } ⟧⟩⟧ ;
//in the case of empty scope only void could be given as a declared type

⟦ Inaccord_cs ( ) : ⟨Type ⟦ void⟧⟩ {  } ⟧  →  ⟦⟨CallSignatureAndScope ⟦  ( ) :  ⟨Type⟦ void⟧⟩  {  } ⟧⟩⟧ ;
⟦ Inaccord_cs ( ⟨OpenCallSignatureAndScope#1 ⟩ ⟧  →  ⟦⟨CallSignatureAndScope⟦ ( ⟨OpenCallSignatureAndScope ⟦ Inaccord_ocs ⟨OpenCallSignatureAndScope#1⟩ ⟧⟩ ⟧  ⟩⟧; 
default ⟦ Inaccord_cs  ⟨CallSignatureAndScope#1⟩ ⟧  →  error ⟦return type does not conform to signatrure⟧; 

sort OpenCallSignatureAndScopeTail  
| ⟦ , ⟨OpenCallSignatureAndScope⟩ ⟧
| ⟦ ) : ⟨Type ⟩ { ⟨Scope⟩ } ⟧                    //close parenthesis.
| ⟦ ) : ⟨Type ⟩ {  } ⟧  
;

//SIMILARILY WITH ABOVE FOR TYPE EXISTENCE
sort OpenCallSignatureAndScopeTail 
| scheme ⟦WellDeclared_ocst ⟨OpenCallSignatureAndScopeTail⟩⟧ ↓top; 
| scheme ⟦Inaccord_ocst ⟨OpenCallSignatureAndScopeTail⟩⟧ ;


 ⟦WellDeclared_ocst , ⟨OpenCallSignatureAndScope#1 ⟩ ⟧ ↓top(#g)  →
 ⟦ ⟨OpenCallSignatureAndScopeTail ⟦,  ⟨OpenCallSignatureAndScope  ⟦WellDeclared_ocs ⟨OpenCallSignatureAndScope#1⟩⟧↓top(#g)  ⟩⟧ ⟩⟧ ;
 ⟦ WellDeclared_ocst ) : ⟨Type#1⟩ { ⟨Scope#2  ⟩ } ⟧  ↓top(#g)→
 ⟦ ⟨OpenCallSignatureAndScopeTail ⟦  ) : ⟨Type⟦Exists_t ⟨Type#1⟩⟧ ↓top(#g)⟩  { ⟨Scope#2  ⟩ }⟧⟩⟧;                    //close parenthesis.
 ⟦ WellDeclared_ocst ) : ⟨Type #1 ⟩ {  } ⟧ ↓top(#g) →⟦ ⟨OpenCallSignatureAndScopeTail ⟦  ) : ⟨Type⟦Exists_t ⟨Type#1⟩⟧ ↓top(#g)⟩ {  } ⟧⟩⟧;


//INACCORD OCST

 ⟦Inaccord_ocst , ⟨OpenCallSignatureAndScope#1 ⟩ ⟧  →
 ⟦ ⟨OpenCallSignatureAndScopeTail ⟦,  ⟨OpenCallSignatureAndScope  ⟦Inaccord_ocs ⟨OpenCallSignatureAndScope#1⟩⟧  ⟩⟧ ⟩⟧ ;
 ⟦ Inaccord_ocst ) : ⟨Type#1⟩ { ⟨Scope#2  ↑t( ⟦⟨Type#1⟩ ⟧) ⟩ } ⟧  →
//QUESTION: SHOULD ATTRIBUTE BE CARRIED?
 ⟦ ⟨OpenCallSignatureAndScopeTail ⟦  ) :⟨Type#1⟩  { ⟨Scope#2  ↑t( ⟦⟨Type#1⟩ ⟧)⟩ }⟧⟩⟧;                    //close parenthesis.
 ⟦ Inaccord_ocst ) : ⟨Type ⟦void ⟧⟩ {  } ⟧  →⟦ ⟨OpenCallSignatureAndScopeTail ⟦  ) : ⟨Type ⟦void ⟧⟩ {  } ⟧⟩⟧;
default ⟦ Inaccord_ocst  ⟨OpenCallSignatureAndScopeTail#1⟩ ⟧  →  error ⟦return type does not conform to signatrure⟧; 


//opencallsignatureandscope

sort OpenCallSignatureAndScope 
| ⟦ ⟨[v:Identifier]⟩ : ⟨Type⟩ ⟨OpenCallSignatureAndScopeTail[v:Identifier]⟩ ⟧
;

//TYPE EXISTENCE CHECK FOR WELLFORMEDNESS OF TYPE DECLARATION
sort OpenCallSignatureAndScope 
| scheme ⟦WellDeclared_ocs ⟨OpenCallSignatureAndScope⟩⟧ ↓top;
| scheme ⟦Inaccord_ocs ⟨OpenCallSignatureAndScope⟩⟧;


 ⟦ WellDeclared_ocs v : ⟨Type#1⟩ ⟨OpenCallSignatureAndScopeTail#2[v]⟩ ⟧ ↓top(#g)→ 

⟦ ⟨OpenCallSignatureAndScope⟦  v : ⟨Type⟦Exists_t ⟨Type#1⟩ ⟧ ↓top(#g)⟩  ⟨OpenCallSignatureAndScopeTail ⟦ WellDeclared_ocst ⟨OpenCallSignatureAndScopeTail#2[v]⟩ ⟧ ↓top(#g)⟩  ⟧⟩ ⟧;

 ⟦ Inaccord_ocs v : ⟨Type#1⟩ ⟨OpenCallSignatureAndScopeTail#2[v]⟩ ⟧ → 

⟦ ⟨OpenCallSignatureAndScope⟦  v :  ⟨Type#1⟩  ⟨OpenCallSignatureAndScopeTail ⟦ Inaccord_ocst ⟨OpenCallSignatureAndScopeTail#2[v]⟩ ⟧⟩  ⟧⟩ ⟧;



//SCOPE-RELEVANT ATTRIBUTES TODO
sort Scope
| ⟦ var ⟨[v:Identifier]⟩ : ⟨Type⟩ ; ⟨Scope[v:Identifier]⟩ ⟧
| ⟦ ⟨Statement⟩ ⟨Scope⟩ ⟧
| ⟦ ⟨Statement⟩  ⟧
| ⟦ var ⟨[v:Identifier]⟩ : ⟨Type⟩ ;⟧
;

//STATEMENT - RELEVANT ATTRIBUTES TODO
sort Statement
| ⟦ { ⟨Scope⟩ } ⟧
| ⟦ {  } ⟧
| ⟦ ⟨Expression⟩ ; ⟧
| ⟦  ; ⟧
| ⟦ if ( ⟨Expression⟩ ) ⟨IfTail⟩ ⟧
| ⟦ while ( ⟨Expression⟩ ) ⟨Statement⟩ ⟧
| ⟦ for ( var ⟨[v:Identifier]⟩ : ⟨Type⟩ in ⟨Expression⟩ ) ⟨Statement[v:Identifier]⟩ ⟧
| ⟦ return ⟨Expression⟩ ; ⟧
|⟦ return ; ⟧
;
// Dangling else "solved" by eager predictive parsing.
sort IfTail | ⟦ ⟨Statement⟩ else ⟨Statement⟩ ⟧ | ⟦ ⟨Statement⟩ ⟧ ;



//WE ARE ABLE TO WRITE THE FIRST STEPS OF THE ANALYSIS ON DECLARATIONS
//AND HENCE OF THE WHOLE PROGRAM.

sort Declarations | scheme CheckClassDecls_first (Declarations);
                  | scheme CheckClassDecls_hfirst(TopLevelList,Declarations) ↓top ;
	          | scheme Typability_Decl(Declarations);
	          | scheme Typability_Decl_h(TopLevelList,Declarations) ↓top ;
//uniciity of toplevel fun names--for class is already happening before
		  | scheme SigGlobalUnicityCheck(Declarations);
	          | scheme SigGlobalUnicityCheck_h(SigList,Declarations)  ↓sigs;
	          
	          
//THE GROUND ZERO TEST IS DOES AN LVALUE CHECK -- WHICH IS PURELY SYNTACTICAL
Lvaluel	          
//The fist check asks for the toplevelist types attribute
//of the declarations and updates it into a HACS context with all defined class types checking for unicity all along
//see helper!
CheckClassDecls_first(#dcls↑toplevels(#top)) → CheckClassDecls_hfirst (#top,#dcls) ;



//helper function for testing purposes 
//only checks unicity of class type declarations
CheckClassDecls_hfirst( ⟦ ⟨TopLevelList ⟦ ⟨Identifier#id⟩  ⟨Type#t⟩ ; ⟨TopLevelList#tl⟩ ⟧⟩ ⟧, #dcls) ↓top{⟦⟨Identifier#id⟩⟧ : #u} →error⟦mutlitple toplevel declarations with name  ⟨id⟩ ⟧  ;
CheckClassDecls_hfirst(⟦⟨TopLevelList ⟦ ⟧⟩ ⟧, #dcls)↓top(#toplevel) → #dcls;
//the return of dcls is for testing purposes only
//in reality we should continue the analysis the the downward top as context
//as we do in the ChackClassDecls_continue
default CheckClassDecls_hfirst(⟦ ⟨Identifier#id⟩  ⟨Type#t⟩ ; ⟨TopLevelList#tl⟩ ⟧, #dcls) → CheckClassdecls_hfirst(#tl, #dcls) ↓top{⟦⟨Identifier#id⟩⟧ :⟦⟨Type#t⟩⟧ } ;


//TYPABILITY CHECKS CONTINUE after the unicity (testing functions accumulate tests for debugging-  all tests are upto!)
//Using WellFormed scheme for checking that types in signatures exist!

Typability_Decl_h( ⟦ ⟨TopLevelList ⟦ ⟨Identifier#id⟩  ⟨Type#t⟩ ; ⟨TopLevelList#tl⟩ ⟧⟩ ⟧, #dcls) ↓top{⟦⟨Identifier#id⟩⟧ : #u} →error⟦mutlitple toplevel declarations with name  ⟨id⟩ ⟧  ;
//Accumulate toplevel and check wellformedness of declarations
Typability_Decl_h(⟦⟨TopLevelList ⟦ ⟧⟩ ⟧, #dcls) ↓top(#toplevel)  → WellFormed(#dcls) ↓top(#toplevel) ; 
default Typability_Decl_h(⟦ ⟨Identifier#id⟩  ⟨Type#t⟩ ; ⟨TopLevelList#tl⟩ ⟧, #dcls)  → CheckClassdecls_hfirst(#tl, #dcls) ↓top{⟦⟨Identifier#id⟩⟧ :⟦⟨Type#t⟩⟧ } ;
;




//We have checked the uniqueness of class definitions and their well declaredness
//we should chekc the unicity of function definitions
//and also unicity of members WITHIN a class
//after that check the global signature is checked and well defined!
SigGlobalUnicityCheck(#dcls↑sglob(#glsig)) → SigGlobalUnicityCheck_h (#glsig,#dcls)  ;
SigGlobalUnicityCheck_h( ⟦⟨SigList ⟦⟨Identifier#1⟩ ⟨Ftu ⟦Cl ⟨FormalsOption #m⟩⟧⟩; ⟨SigList #tlsig⟩⟧⟩⟧, #dcls)  →SigGlobalUnicityCheck_h(#tlsig,#dcls) ↓sigs{ ⟦⟨Identifier#1⟩⟧: ⟦ ⟨Ftu ⟦Cl ⟨FormalsOption UnicityMembers(#m,#m)⟩⟧⟩⟧};
SigGlobalUnicityCheck_h( ⟦⟨SigList ⟦⟨Identifier#1⟩ ⟨Ftu ⟦Trm ⟨Type #t⟩⟧⟩; ⟨SigList #tlsig⟩⟧⟩⟧, #dcls) ↓sigs{ ⟦⟨Identifier#1⟩⟧: ⟦ ⟨Ftu ⟦Trm ⟨Type #u⟩⟧⟩⟧} →error ⟦ toplevel fun definition is beeing redifined? use a different name⟧;
//when done just return the declarations
//from here we will continue checking of course!
SigGlobalUnicityCheck_h( ⟦⟨SigList ⟦ ⟧⟩⟧, #dcls) → #dcls;
default SigGlobalUnicityCheck_h( ⟦⟨SigList ⟦⟨Identifier#1⟩ ⟨Ftu ⟦Trm ⟨Type #t⟩⟧⟩; ⟨SigList #tlsig⟩⟧⟩⟧, #dcls)  →SigGlobalUnicityCheck_h(#tlsig,#dcls) ↓sigs{ ⟦⟨Identifier#1⟩⟧: ⟦ ⟨Ftu ⟦Trm ⟨Type #t⟩⟧⟩⟧};


//ZERO AND FIRST CHECK: UNICITY OF TOPLEVEL CLASS DECLARATIons

sort Program | ⟦ ⟨Declarations⟩ ⟧ ;
|scheme UnicityClassDecls(Program);
| scheme Lvaluedness(Program);
UnicityClassDecls( ⟦⟨Program ⟦ ⟨Declarations#dcl⟩ ⟧ ⟩⟧ )→  ⟦⟨Program CheckClassDecls_first(Lvaluedness(#dcl))⟩ ⟧ ;
Lvaluedness( ⟦⟨Program ⟦ ⟨Declarations#dcl⟩ ⟧ ⟩⟧ )→  ⟦⟨Program Assignment_chk(#dcl)⟩ ⟧ ;

//SECOND CHECK: ACCUMULATE THE TOPLEVEL CONTEXT AND ADDITIONALLY
//CHECK THE WELLFORMEDNESS OF ALL APPEARING SIGNATURES
// I.E IF THEIR TYPES EXIST!
// USE THE WELLFORMEDNESS FUNCTIONS FROM BEFORE
//ALL CHECKS ARE "UP TO" I.E CUMMULATIVE

sort Program
|scheme Typability(Program);
|scheme UnicityOfFunGlobal(Program);

Typability( ⟦⟨Program ⟦ ⟨Declarations#dcl⟩ ⟧ ⟩⟧ )→  ⟦⟨Program Typability_Decl(#dcl)⟩ ⟧ ;

Typability_Decl(#dcls↑toplevels(#top)) → Typeability_Decl_h (#top,#dcls) ;
//THIRD CHECK
//AFTER WE HAVE CHECKED THAT THE TOPLEVEL CLASS TYPES ARE UNIQUE
//AND THAT THE TYPE DECLARATIONS ARE TYPEABLE WITH RESPECT TO THE 
//TYPE UNIVERSE 
//WE CHECK ALSO THAT (TYPABLE) FUNCTION signatures IN THE TOP LEVEL ARE
//ALSO UNIQUE 
//VIA SigGlobalUnicityCheck
//Again the checking is cummulative 
UnicityOfFunGlobal( ⟦⟨Program ⟦ ⟨Declarations#dcl⟩ ⟧ ⟩⟧)→  ⟦⟨Program SigGlobalUnicityCheck(Typability_Decl(#dcl))⟩ ⟧;

//fourth check 
//AFTER WE HAVE A WELL GLOBAL SIGNATURE 






}
