module Make :
functor (A:Arch_herd.S) ->
  sig
    val print_converted : Test_herd.Make(A).result -> unit
  end
