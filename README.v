Require stlc.autosubst2.prop_type_safety.
Require stlc.lngen.prop_type_safety.

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