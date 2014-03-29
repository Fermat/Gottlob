Gottlob
=======
Syntax
-------

**variable** var ::= lowerVar | upperVar

**formula** F ::= upperVar | F -> F' | *forall* var . F | t :: S | S S' | S t

**set/property** S ::= *iota* var . F | *iota* var . S

**program** t ::= lowerVar | t t' | \ lowerVar . t 

**proof** : p ::= lowerVar | *mp* p *by* p' | *inst* p *by* [S | F | t]    
                           | *ug* var . p | *cmp* p | *invcmp* p *from* F   
                      | *simpCmp* p | *invSimp* p from F | *beta* p   
                  | *invBeta* p | *discharge* a (: F)? . p    
                  | q [p | t | F | S ]
                
**tactic** q ::= lowerVar | \ lowerVar . q | q q | q [p | t | F | S ]