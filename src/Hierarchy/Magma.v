Local Open Scope mag_scope.


Context `{Magma A}
        {rel : relation A}
        `{!MagCongruence rel}.

Instance : @Magma _ rel _.
Proof. repeat split; try apply _. Qed.
