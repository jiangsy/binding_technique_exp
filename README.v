Require Import common.prop_as_core.
Require Import common.prop_as_unscoped.

Require stlc.autosubst2.prop_type_safety.
Require stlc.lngen.prop_type_safety.
Require systemf.autosubst2.prop_type_safety.
Require systemf.lngen.prop_type_safety.
Require fsub.autosubst2_dctx.prop_typing.


Section stlc.

  Section autosubst2.
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

  Section autosubst2.
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

  Section autosubst2.
    Import fsub.autosubst2_dctx.def_as2.
    Import fsub.autosubst2_dctx.def_extra.
    Import fsub.autosubst2_dctx.prop_typing.

    Print typing.
    Print step.

    Check preservation.
    Print Assumptions preservation. 
    Check progress.
    Print Assumptions progress.
  End autosubst2.

End fsub.