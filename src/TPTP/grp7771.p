fof(sos01,axiom,
    ! [B,A] : difference(A,product(A,B)) = B ).

fof(sos02,axiom,
    ! [B,A] : product(A,difference(A,B)) = B ).

fof(sos03,axiom,
    ! [B,A] : quotient(product(A,B),B) = A ).

fof(sos04,axiom,
    ! [B,A] : product(quotient(A,B),B) = A ).

fof(sos05,axiom,
    ! [D,C,B,A] : product(product(A,B),product(C,D)) = product(product(A,C),product(B,D)) ).

fof(sos06,axiom,
    ! [A] : product(A,A) = A ).
%----Napoleon
fof(sos07,axiom,
    ! [B,A] : product(product(product(A,B),B),product(B,product(B,A))) = B ).

fof(sos08,axiom,
    ! [C,B,A] : bigC(A,B,C) = product(product(A,B),product(C,A)) ).

fof(sos09,axiom,
    product(product(a,c),product(c,b)) = product(a,b) ).

fof(goals,conjecture,
    ! [X0] : bigC(a,b,X0) = bigC(c,c,X0) ).