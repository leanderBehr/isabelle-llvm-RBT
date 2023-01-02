theory Append
  imports 
    Main
    "HOL-Eisbach.Eisbach_Tools"
begin

method_setup append = \<open>
  let 
    fun APPEND_LIST tacs = fold_rev (curry (op APPEND)) tacs (no_tac);
  in
   Scan.repeat1 Method.text_closure >>
   (fn ms => fn ctxt => fn facts => let
      val tacs = map (fn m => method_evaluate m ctxt facts) ms
    in
      SIMPLE_METHOD (APPEND_LIST tacs) facts
    end)
  end
\<close>

end