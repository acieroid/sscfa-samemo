let order_comp x y =
  if x = 0 then y else x

let order_concat l =
  let rec aux last = function
    | [] -> last
    | (h::t) ->
      if last <> 0 then last else aux (order_comp last (Lazy.force h)) t
  in aux 0 l

let compare_list cmp l1 l2 =
  order_concat
    (lazy (Pervasives.compare (BatList.length l1) (BatList.length l2))
     :: (BatList.map
           (fun (el1, el2) -> lazy (cmp el1 el2))
           (BatList.combine l1 l2)))

module StringSet = BatSet.Make(struct
    type t = string
    let compare = Pervasives.compare
  end)
