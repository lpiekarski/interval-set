(* Author: Lukasz Piekarski *)
(* Code review: Kamil Poniewierski *) 
(*
 * ISet - Interval sets
 * Copyright (C) 1996-2003 Xavier Leroy, Nicolas Cannasse, Markus Mottl, Jacek Chrzaszcz, Lukasz Piekarski
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version,
 * with the special exception on linking described in file LICENSE.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

(* Type of an interval set. *)
(*   [Empty] - the empty set. *)
(*   [Node (l, i, r, h)] - set of interval [i] and elements of [l] and [r] *)
(*     that has height [h]. [h] - 1 is always equal to the height of [l] or [r]. *)
type t =
  | Empty
  | Node of t * (int * int) * t * int

(* The empty set *)
let empty = Empty

(* [is_empty s] returns true if [s] is empty. *)
let is_empty = function
	| Empty -> true
	| _ -> false

(* [safe_minus a] returns -[a] handling integer overflow. *)
let safe_minus a = if a = min_int then max_int else (-a)

(* [safely_add a b] returns [a] + [b] with controlled integer overflow behaviour. *)
let safely_add a b = 
	if a >= 0 then
		if b < max_int - a then
			a + b
		else
			max_int
	else
		if b >= 0 then
			if a < max_int - b then
				a + b
			else
				max_int
		else
			if b > min_int - a then
				a + b
			else
				min_int

(* [height s] returns the height of [s]. *)
let height = function
  | Node (_, _, _, h) -> h
  | Empty -> 0

(* [make l k r] returns a set with value [k] in the root *)
(*  and sets [l] and [r] as right and left subsets. *)
(*  If [l] and [r] were balanced the result is also balanced. *)
let make l k r = Node (l, k, r, max (height l) (height r) + 1)

(* [bal l k r] returns balanced set containing value [k] *)
(*  and sets [l] and [r] *)
(* Assumes: difference of heights of [l] and [r] is at most 3. *)
let bal l k r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _) ->
        if height ll >= height lr then make ll lk (make lr k r)
        else
          (match lr with
          | Node (lrl, lrk, lrr, _) ->
              make (make ll lk lrl) lrk (make lrr k r)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _) ->
        if height rr >= height rl then make (make l k rl) rk rr
        else
          (match rl with
          | Node (rll, rlk, rlr, _) ->
              make (make l k rll) rlk (make rlr rk rr)
          | Empty -> assert false)
    | Empty -> assert false
  else Node (l, k, r, max hl hr + 1)

(* [mem x s] returns [true] if [s] contains [x], and [false] otherwise. *)
let rec mem x = function
	| Empty -> false
	| Node (l, (a, b), r, _) ->
		if a <= x && x <= b then true
		else mem x (if x < a then l else r)

(* [iter f s] applies [f] to all continuous intervals in the set [s]. *)
(*  The intervals are passed to [f] in increasing order. *)
let rec iter f = function
	| Empty -> ()
	| Node (l, p, r, _) -> iter f l; f p; iter f r

(* [fold f s a] computes [(f xN ... (f x2 (f x1 a))...)], *)
(*  where [x1] ... [xN] are all continuous intervals of [s], in increasing order. *)
let fold f set acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, k, r, _) ->
          loop (f k (loop acc l)) r in
  loop acc set

(* [elements s] Return the list of all continuous intervals of [s]. *)
(*  The returned list is sorted in increasing order. *)
let elements =
	let rec loop acc = function
		| Empty -> acc
		| Node (l, p, r, _) -> loop (p :: loop acc r) l in
	loop []

(* [below n s] returns the number of elements of [s] that are lesser *)
(*  or equal to [n]. If there are more than max_int such elements, *)
(*  the result is max_int. *)
let below t =
	let rec loop acc = function
		| Empty -> acc
		| Node (l, (a, b), r, _) ->
			if a <= t && t <= b then 
				let na = 
					if a <> min_int then 
						safely_add (safely_add t (safe_minus a)) 1 
					else
						safely_add (safely_add t (safe_minus a)) 2 
				in
				loop (safely_add acc na) l
			else if t < a then loop acc l
			else 
				let na = 
					if a <> min_int then 
						safely_add (safely_add b (safe_minus a)) 1 
					else
						safely_add (safely_add b (safe_minus a)) 2 
				in
				safely_add (loop acc r) (loop na l)
			in
		loop 0

(* [get_below t s] returns set of members of [s] lesser than [t]. *)
(*  If [s] was balanced the result is also balanced. *)
let rec get_below t = function
	| Empty -> Empty
	| Node (l, (a, b), r, _) ->
		if a <= t && t <= b then
			if t = a then
				l
			else
				bal l (a, t - 1) Empty
		else if t < a then
			get_below t l
		else 
			bal l (a, b) (get_below t r)

(* [get_above t s] returns set of members of [s] greater than [t]. *)
(*  If [s] was balanced the result is also balanced. *)
let rec get_above t = function
	| Empty -> Empty
	| Node (l, (a, b), r, _) ->
		if a <= t && t <= b then
			if t - b = 0 then
				r
			else
				bal Empty (t + 1, b) r
		else if t > b then
			get_above t r
		else
			bal (get_above t l) (a, b) r

(* [split x s] returns a triple [(l, present, r)], where *)
(*  [l] is the set of elements of [s] that are strictly lesser than [x]; *)
(*  [r] is the set of elements of [s] that are strictly greater than [x]; *)
(*  [present] is [false] if [s] contains no element equal to [x], *)
(*  or [true] if [s] contains an element equal to [x]. *)
(*  If [s] was balanced [l] and [r] are also balanced. *)
let split x s = (get_below x s, mem x s, get_above x s)

(* [min_elt s] returns the least member of [s]. *)
let rec min_elt = function
  | Node (Empty, k, _, _) -> k
  | Node (l, _, _, _) -> min_elt l
  | Empty -> raise Not_found

(* [max_elt s] returns the greatest member of [s]. *)
let rec max_elt = function
	| Node (_, k, Empty, _) -> k
	| Node (_, _, r, _) -> max_elt r
	| Empty -> raise Not_found

(* [remove_min_elt s] returns the set with the least member removed. *)
(*  If [s] was balanced the result is also balanced. *)
let rec remove_min_elt = function
  | Node (Empty, _, r, _) -> r
  | Node (l, k, r, _) -> bal (remove_min_elt l) k r
  | Empty -> invalid_arg "ISet.remove_min_elt"

(* [remove_max_elt s] returns the set with the greatest member removed *)
(*  If [s] was balanced the result is also balanced. *)
let rec remove_max_elt = function
  | Node (l, _, Empty, _) -> l
  | Node (l, k, r, _) -> bal l k (remove_max_elt r)
  | Empty -> invalid_arg "ISet.remove_min_elt"

(* [merge t1 t2] returns set of elements from t1 and t2. *)
(*  If [t1] and [t2] were balanced the result is also balanced. *)
(*  Assumes: [t1] and [t2] have an empty intersection *)
(*    and elements of [t1] are lesser than elements of [t2]. *)
let merge t1 t2 =
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ -> bal t1 (min_elt t2) (remove_min_elt t2)

(* [add (x, y) s] returns a set containing the same elements as [s], *)
(*    plus all elements of the interval [[x,y]] including [x] and [y]. *)
(*  Resulting set is balanced. *)
(*  Assumes: [x] <= [y] and [s] is balanced. *)
let rec add (x, y) = function
	| (Node (l, (a, b), r, h)) as s ->
		if y < safely_add a (-1) then
			let nl = add (x, y) l in
			bal nl (a, b) r
		else if b < safely_add x (-1) then
			let nr = add (x, y) r in
			bal l (a, b) nr
		else 
			(match get_below x s, get_above y s with
				| Empty, Empty -> make Empty (x, y) Empty
				| Empty, tr -> 
					let (min_r1, min_r2) = min_elt tr in
					let nr = if min_r1 = safely_add y 1 then remove_min_elt tr else tr in
					let nk1 = x in
					let nk2 = if min_r1 = safely_add y 1 then min_r2 else y in
					bal Empty (nk1, nk2) nr
				| tl, Empty ->
					let (max_l1, max_l2) = max_elt tl in
					let nl = if max_l2 = safely_add x (-1) then remove_max_elt tl else tl in
					let nk1 = if max_l2 = safely_add x (-1) then max_l1 else x in
					let nk2 = y in
					bal nl (nk1, nk2) Empty
				| tl, tr ->
					let (max_l1, max_l2) = max_elt tl in
    			let (min_r1, min_r2) = min_elt tr in
    			let nl = if max_l2 = safely_add x (-1) then remove_max_elt tl else tl in
    			let nr = if min_r1 = safely_add y 1 then remove_min_elt tr else tr in
    			let nk1 = if max_l2 = safely_add x (-1) then max_l1 else x in
    			let nk2 = if min_r1 = safely_add y 1 then min_r2 else y in
    			bal nl (nk1, nk2) nr)
	| Empty -> make Empty (x, y) Empty
			
(* [remove (x, y) s] returns a set containing the same elements as [s], *)
(*    except for all those which are included between [x] and [y]. *)
(*  If [s] was balanced the result is also balanced. *)
(*  Assumes [x] <= [y]. *)
let remove (x, y) s = merge (get_below x s) (get_above y s)
