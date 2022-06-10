-------------------------------- MODULE ex2 --------------------------------
EXTENDS Integers

CONSTANT N

Arr == 0..(N-1)

VARIABLES array, counter, inicial

vars == <<array, counter, inicial>>

Init == 
    /\ array = [i \in Arr |-> array[i] <= N /\ array[i] > 0]
    /\ counter = 0
    /\ inicial = array

swap ==
    /\ array[counter] > array[counter + 1]
    /\ array[counter]' = array[counter + 1] 
    /\ array[counter + 1]' = array[counter]
    
innerloop ==
    /\ counter < (N - 1)
    /\ swap
    /\ counter' = counter + 1 
    
outerloop ==
    /\ counter = (N - 1)
    /\ counter' = 0

execute == innerloop \/ outerloop
    
Next == execute

Spec == Init /\ [][Next]_vars 
    

Sorted == <>([](\A i \in Arr: \A j \in Arr: i >= j => array[i] >= array[j]))

Permutation == [](\A i \in Arr: array[i] \in inicial)

UltimoMaior == [](counter = N-1 => (\A i \in Arr: array[i] <= array[N-1]))


=============================================================================

(* RES.

B) Para verificar esta propriedade temos de verificar que vai haver um estado que a partir dai vai ser sempre verdade que 
   todos os indices i,j pertencente a {0..N-1} se i >= j então array[i] >= array[j]

C) Em todos os estados, se o counter for igual a N-1 (significando que estamos no fim da iteração do ciclo exterior),
   então todos os elementos do array tem de ser menor ou igual que o último elemento

D) É necessário inicializar o array de modo a que o primeiro elemento seja o maior elemento do array

E) No init foi criada uma variavel que guarda a configuração do array inicial, 
   assim é possível verificar que em todos os estados todos os elementos do array estão contidos no array inicial

F) Esta propriedade diz que em todos os estados se o último elemento for 0 então o primeiro elemento do array também tem de ser 0, 
   pelo que é uma propriedade de safety, garantindo que o primeiro elemento nunca vai ser maior do que o último no caso de o último ser 0
*)