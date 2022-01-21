
(** Log reporter *)

type t

val create : unit -> t

val as_reporter : t -> Logs.reporter

val log_to_chan : t -> out_channel -> unit

val setup_logs : ?files:string list -> debug:bool -> unit -> unit
(** Setup reporter and debug level for {!Logs} *)

val setup_trustee : unit -> unit
(** Installer logger as the main logger for Trustee *)
