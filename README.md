Gottlob
=======
Data Type Declaration
-----
*data* Name params *where*  
&nbsp;&nbsp; constr :: Type  
&nbsp;&nbsp; constr :: Type  
&nbsp;&nbsp; constr :: Type  
&nbsp;&nbsp; ...
&nbsp;&nbsp; (deriving Ind)?

Name ::= upperVar  
constr ::= lowerVar  
params ::= (var)*  
Type ::= Type -> Type | ...
 
Program 
----
A proper subset of Haskell without explicit type declaration.

Theorem Proving
------
*thoerem* proofName ([formulaName])? . formula  
*proof*  
&nbsp;&nbsp; [name = proof (: formula)? | [assumption] : formula ]  
&nbsp;&nbsp; [name = proof (: formula)? | [assumption] : formula ]  
&nbsp;&nbsp; [name = proof (: formula)? | [assumption] : formula ]  
...
  
*qed*

name, proofName, assumption ::= lowerVar  
proof ::= p  
formula ::= F

Tactic Declaration
----
*tactic* name params = [oneLine | multipleLine]  
oneLine ::= q  
multipleLine ::=    
&nbsp;&nbsp; [name = proof (: formula)? | [assumption] : formula ]  
&nbsp;&nbsp; [name = proof (: formula)? | [assumption] : formula ]  
&nbsp;&nbsp; [name = proof (: formula)? | [assumption] : formula ]  

Fixability Declaration
------
e.g.  
*prog* *infixr* 10 >>=  
*proof* *infixl* 10 >>-  
*formula* *infixl* 3 *  


Atomic Syntax
-------

**variable** var ::= lowerVar | upperVar

**formula** F ::= upperVar | F -> F' | *forall* var . F | t :: S | S S' | S t

**set/property** S ::= upperVar | *iota* var . F | *iota* var . S | S S' | S t

**program** t ::= lowerVar | t t' | \ lowerVar . t 

**proof** : p ::= lowerVar | *mp* p *by* p'   | *inst* p *by* [S | F | t]   
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| *ug* var . p | *cmp* p | *invcmp* p *from* F   
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| *simpCmp* p | *invSimp* p from F | *beta* p   
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| *invBeta* p | *discharge* a (: F)? . p    
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| q [p | t | F | S ]
                
**tactic** q ::= lowerVar | \ lowerVar . p | \ lowerVar . q | q q | q [p | t | F | S ]