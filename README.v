Require stlc.autosubst2.prop_typing.
Require stlc.lngen.prop_typing.

Section stlc.

  Section autosubst2.
    Import stlc.autosubst2.prop_typing.

    Check preservation.
    Print Assumptions preservation. 
    Check progress.
    Print Assumptions progress.
  End autosubst2.

  Section lngen.
    Import stlc.lngen.prop_typing.

    Check preservation.
    Print Assumptions preservation. 
    Check progress.
    Print Assumptions progress.
  End lngen.

End stlc.