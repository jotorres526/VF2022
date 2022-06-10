-------------------------------- MODULE ex1 --------------------------------
EXTENDS Integers

CONSTANT N

Filosofos == 0..(N-1)
Garfos == 0..(N-1)

VARIABLES waiter, filosofos, garfos, requests

Proc == 1..N

vars == <<waiter, filosofos, garfos, requests>>

Init == 
    /\ waiter = "true"
    /\ filosofos = [f \in Filosofos |-> "think"]
    /\ garfos = [g \in Garfos |-> "true"]
    /\ requests = [f \in Filosofos |-> 0] 
    
callWaiter(i) ==
    /\ waiter = "true"
    /\ waiter' = "false"
    /\ requests[i] = 0
    /\ requests' = [requests EXCEPT ![i] = 1] 
    /\ UNCHANGED << filosofos >>

releaseWaiter(i) ==
    /\ waiter = "false"
    /\ waiter' = "true"
    /\ requests[i] = 1 
    /\ requests' = [requests EXCEPT ![i] = 0] 
    /\ UNCHANGED << garfos, filosofos >>    

left(i) ==
    /\ filosofos[i] = "think"
    /\ garfos[i] = "true"
    /\ garfos' = [garfos EXCEPT ![i] = "false"]
    /\ callWaiter(i)
    /\ UNCHANGED << filosofos >>

right(i) == 
    /\ filosofos[i] = "think"
    /\ garfos[(i+1) % N] = "true"
    /\ garfos' = [garfos EXCEPT ![(i+1) % N] = "false"]
    /\ waiter' = "true"
    /\ UNCHANGED << filosofos >>
       
eat(i) ==
    /\ filosofos[i] = "think"
    /\ filosofos' = [filosofos EXCEPT ![i] = "eat"]
    /\ UNCHANGED << waiter, garfos, requests >>
     
release(i) ==
    /\ filosofos[i] = "eat"
    /\ filosofos' = [filosofos EXCEPT ![i] = "think"]
    /\ garfos' = [garfos EXCEPT ![(i+1) % N] = "true"]
    /\ garfos' = [garfos EXCEPT ![i] = "true"]
    /\ UNCHANGED << waiter, requests >>

    
execute(i) == left(i) \/ right(i) \/ eat(i) \/ release(i)
    
Next == \E i \in Filosofos: execute(i)

Spec == Init /\ [][Next]_vars

MutualExclusion == [] ~(\E i \in Filosofos: \E j \in Filosofos: i#j /\ (i-1 <= j) /\ (j <= i+1)  /\ filosofos[i] = "eat" /\ filosofos[j] = "eat")
    
AlwaysEat ==  \E i \in Filosofos: <>([] (filosofos[i] = "eat")) => ~(<> (\A j \in Filosofos: i#j /\ filosofos[j] = "eat"))

EatsAgain == \E i \in Filosofos: (\A j \in Filosofos: <>(filosofos[j] = "eat")) ~> <>(filosofos[i] = "eat")

ReqWaiter == \A i \in Filosofos: requests[i] = 1 ~> filosofos[i] = "eat"

=============================================================================

(* RES.

B)

C) Mutual Exclusion. 
   Para verificar esta propriedade temos de ver que não há um estado onde hajam dois filosofos vizinhos (i =/= j && i-1<=j<=i+1) que estejam ambos a comer
    
D) ReqWaiter
   Para resolver esta alinea foi criada uma lista de requests que quando um filosofo chama um empregado, levanta uma flag na sua posiçao da lista requests
   Com esta lista basta verificar que para todos os filosofos i, se requests[i] = 1 eventualmente o filosofo vai comer.
    
E) EatsAgain
   Podemos adicionar uma propriedade que expresse que há um filosofo que se todos os filosofos (o próprio incluido) tiverem comido, 
   eventualmente vai haver um estado onde esse filosofo come novamente.

F) AlwaysEat
   Se existir um filosofo que quando comece a comer vai ficar a comer em todos os estados, então é falso que qualquer filosofo que não seja ele mesmo vá ter um estado em que esteja a comer 

*)