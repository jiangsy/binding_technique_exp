Require stlc.autosubst2.prop_type_safety.
Require stlc.lngen.prop_type_safety.
Require systemf.autosubst2.prop_type_safety.
Require fsub.autosubst2_dctx.prop_typing.

Section stlc.

  Section autosubst2.
    Import stlc.autosubst2.def_extra.
    Import stlc.autosubst2.prop_type_safety.

    Check preservation.
    Print Assumptions preservation. 
    Check progress.
    Print Assumptions progress.
  End autosubst2.

  Section lngen.
    Import stlc.lngen.def_extra.
    Import stlc.lngen.prop_type_safety.
    
    Check preservation.
    Print Assumptions preservation. 
    Check progress.
    Print Assumptions progress.
  End lngen.

End stlc.


Section systemf.

  Section autosubst2.
    Import systemf.autosubst2.def_extra.
    Import systemf.autosubst2.prop_type_safety.

    Check preservation.
    Print Assumptions preservation. 
    Check progress.
    Print Assumptions progress.
  End autosubst2.

End systemf.


Section fsub.

  Section autosubst2.
    Import fsub.autosubst2_dctx.def_extra.
    Import fsub.autosubst2_dctx.prop_typing.

    Check preservation.
    Print Assumptions preservation. 
    Check progress.
    Print Assumptions progress.
  End autosubst2.

End fsub.