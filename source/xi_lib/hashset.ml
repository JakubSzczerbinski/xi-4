
type 'a t = ('a, unit) Hashtbl.t 

let create () : 'a t = Hashtbl.create 101

let clear = Hashtbl.clear

let add t x = Hashtbl.replace t x ()

let mem = Hashtbl.mem

let to_seq t = Hashtbl.to_seq_keys t

let length t = Hashtbl.length t

let remove t v = Hashtbl.remove t v

let iter f t =
  let g k _ = f k in
  Hashtbl.iter g t


let fold f t acc =
  let g k () = f k in 
  Hashtbl.fold g t acc

let of_seq seq : 'a t =
  let result = create () in
  Seq.iter (add result) seq;
  result