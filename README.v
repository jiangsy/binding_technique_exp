Require Import common.prop_as_core.
Require Import common.prop_as_unscoped.

Require stlc.autosubst2.prop_type_safety.
Require stlc.lngen.prop_type_safety.
Require systemf.autosubst2.prop_type_safety.
Require systemf.lngen.prop_type_safety.
Require fsub.autosubst2_dctx.prop_typing.
Require fsub.autosubst2_sctx.prop_typing.


Section stlc.
  Goal True. idtac "". idtac "". idtac "Simple Typed Lambda Calculus". idtac "". idtac "". Abort.
  Section autosubst2.
    Goal True. idtac "". idtac "Autosusbt2". idtac "". Abort.
    Import stlc.autosubst2.def_as2.
    Import stlc.autosubst2.def_extra.
    Import stlc.autosubst2.prop_type_safety.

    Print typing.
    Print step.
    Check preservation.
    Print Assumptions preservation. 
    Check progress.
    Print Assumptions progress.
  End autosubst2.

  Section lngen.
    Goal True. idtac "". idtac "LNgen". idtac "". Abort.
    Import Metalib.Metatheory.
    Import stlc.lngen.def_ott.
    Import stlc.lngen.def_extra.
    Import stlc.lngen.prop_type_safety.
    
    Print typing.
    Print step.
    Check preservation.
    Print Assumptions preservation. 
    Check progress.
    Print Assumptions progress.
  End lngen.

End stlc.


Section systemf.
  Goal True. idtac "". idtac "". idtac "System F". idtac "". idtac "". Abort.
  Section autosubst2.
    Goal True. idtac "". idtac "Autosusbt2". idtac "". Abort.
    Import systemf.autosubst2.def_as2.
    Import systemf.autosubst2.def_extra.
    Import systemf.autosubst2.prop_type_safety.

    Print typing.
    Print step.

    Check preservation.
    Print Assumptions preservation. 
    Check progress.
    Print Assumptions progress.
  End autosubst2.

  Section lngen.
    Goal True. idtac "". idtac "LNgen". idtac "". Abort.
    Import Metalib.Metatheory.
    Import systemf.lngen.def_ott.
    Import systemf.lngen.def_extra.
    Import systemf.lngen.prop_type_safety.

    Print typing.
    Print step.
    
    Check preservation.
    Print Assumptions preservation. 
    Check progress.
    Print Assumptions progress.
  End lngen.

End systemf.


Section fsub.
  Goal True. idtac "". idtac "". idtac "System F-sub". idtac "". idtac "". Abort.

  Section autosubst2_dctx.
    Goal True. idtac "". idtac "Autosusbt2". idtac "". Abort.

    Import fsub.autosubst2_dctx.def_as2.
    Import fsub.autosubst2_dctx.def_extra.
    Import fsub.autosubst2_dctx.prop_typing.

    Print typing.
    Print step.

    Check preservation.
    Print Assumptions preservation. 
    Check progress.
    Print Assumptions progress.
  End autosubst2_dctx.

  (* for reference, this is another version using combined context, with plain De Brujin *)
  (* https://www.seas.upenn.edu/~plclub/poplmark/vouillon.html *)
  Section autosubst2_sctx.
    Goal True. idtac "". idtac "Autosusbt2". idtac "". Abort.

    Import fsub.autosubst2_sctx.def_as2.
    Import fsub.autosubst2_sctx.def_extra.
    Import fsub.autosubst2_sctx.prop_typing.

    Print typing.
    Print step.

    Check preservation.
    Print Assumptions preservation. 
    Check progress.
    Print Assumptions progress.
  End autosubst2_sctx.

End fsub.