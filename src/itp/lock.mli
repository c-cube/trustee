(** Value protected by a mutex *)

type 'a t
(** A value surrounded with a lock *)

val create : 'a -> 'a t
(** Create a new protected value. *)

val with_lock : 'a t -> ('a -> 'b) -> 'b
(** [with_lock l f] runs [f x] where [x] is the value protected with the lock
    [l], in a critical section. If [f x] fails, [with_lock l f] fails too but
    the lock is released. *)

val update : 'a t -> ('a -> 'a) -> unit
(** [update l f] replaces the content [x] of [l] with [f x], atomically. *)

val update_map : 'a t -> ('a -> 'a * 'b) -> 'b
(** [update_map l f] computes [x', y = f (get l)], then puts [x'] in [l] and
    returns [y]. *)

val mutex : _ t -> Mutex.t
(** Underlying mutex. *)

val get : 'a t -> 'a
(** Atomically get the value in the lock. The value that is returned isn't
    protected! *)

val set : 'a t -> 'a -> unit
(** Atomically set the value. *)

val exchange : 'a t -> 'a -> 'a
(** [exchange lock x] atomically sets [lock := x] and returns the previous value
*)

(** Type allowing to manipulate the lock as a reference when one is holding it.
*)
module LockRef : sig
  type 'a t

  val as_ref : 'a t -> 'a ref
  val get : 'a t -> 'a
  val set : 'a t -> 'a -> unit
end

val with_lock_as_ref : 'a t -> ('a LockRef.t -> 'b) -> 'b
(** [with_lock_as_ref l f] calls [f] with a reference-like object that allows to
    manipulate the value of [l] safely. The object passed to [f] must not escape
    the function call. *)

val pp : 'a Fmt.printer -> 'a t Fmt.printer
