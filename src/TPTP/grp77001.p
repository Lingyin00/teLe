fof(f01,axiom,
    ! [B,A] : mult(A,ld(A,B)) = B ).

fof(f02,axiom,
    ! [B,A] : ld(A,mult(A,B)) = B ).

fof(f03,axiom,
    ! [B,A] : mult(rd(A,B),B) = A ).

fof(f04,axiom,
    ! [B,A] : rd(mult(A,B),B) = A ).

fof(f05,axiom,
    ! [A] : mult(A,unit) = A ).

fof(f06,axiom,
    ! [A] : mult(unit,A) = A ).

fof(f07,axiom,
    ! [C,B,A] : mult(mult(mult(A,B),A),mult(A,C)) = mult(A,mult(mult(mult(B,A),A),C)) ).

fof(f08,axiom,
    ! [C,B,A] : mult(mult(A,B),mult(B,mult(C,B))) = mult(mult(A,mult(B,mult(B,C))),B) ).

fof(goals,conjecture,
    ! [X0] :
    ? [X1] :
      ( mult(X1,X0) = unit
      & mult(X0,X1) = unit ) ).