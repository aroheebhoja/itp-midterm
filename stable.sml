(* EXTREMELY SLOW Gale Shapley algorithm implemented in SML! *)

(* search for an element in a list, and return the index of the element if found *)
fun search L target = 
  let
    (* helper function to search starting at index i *)
    fun search' [] i target = ~1
      | search' (x::xs) i target = 
          if x = target
          then i
          else search' xs (i+1) target
  in
    search' L 0 target
  end

(* write to the ith index in a list. Runtime: SCARY!!! Happy halloween *)
fun update L i n = 
  let 
    fun update' [] M i n = (rev M)
      | update' (l::ls) M 0 n = (rev M) @ [n] @ ls
      | update' (l::ls) M i n = update' ls (l::M) (i-1) n
  in
    update' L [] i n
  end

(* get ith indexed element in list *)
fun get (x::xs) 0 = x
  | get (x::xs) k = get xs (k-1)

(* Elements of A are of the form (i, [p1, ..., pn])
   Elements of B are of the form (i, [p1, ..., pn])
   M[i] =  SOME (k, [p1, ..., pn]) where i is in B, k is in A, and [p1, ..., pn] is k's pref list
           NONE if element i in B is currently unmatched
   *)

(* we terminate when every member of A has exhausted its preference list -- can probably speed this up
   by terminating early if every member of A is matched but ehhhhh *)

fun match [] B M = M
  | match ((k, [])::As) B M = match As B M (* if k has already exhausted its pref list, skip it *)
  | match ((k, (p::ps))::As) B M = 
    let 
      val (_, pPrefs) = get B p 
      val M' = (case (get M p) of
        (* p is already matched *)

        SOME (k', _) => 
            if ((search pPrefs k) < (search pPrefs k'))
            (* k is preferred to p's current match *)
            then (update M p (SOME (k, ps)))
            else M

        (* p is unmatched *)
        | NONE => (update M p (SOME (k, ps))))

      (* enqueue k so we only visit it again after we've seen everything else in A *)
      val A' = As @ [(k, ps)]
    in
      match A' B M'
    end