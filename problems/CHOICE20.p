% Chad E Brown, Jan 2011
% A case operator from oo (with 4 elements) to i is defined using a choice operator on i.
% Check constant true equation.
% Difficulty: Easy
thf(eps,type,(eps : (($i > $o) > $i))).
thf(choiceax,axiom,(! [P : ($i > $o)] : ((? [X : $i] : (P @ X)) => (P @ (eps @ P))))).
thf(caseoo,type,(case : (($o > $o) > ($i > ($i > ($i > ($i > $i))))))).
thf(caseood,definition,(case = (^ [B : ($o > $o), X : $i, Y : $i, U : $i, V : $i] : (eps @ (^ [Z : $i] : (((B = (^ [A : $o] : $false)) & (Z = X)) | ((B = ~) & (Z = Y)) | ((B = (^ [A : $o] : A)) & (Z = U)) | ((B = (^ [A : $o] : $true)) & (Z = V)))))))).
thf(f,type,(f : ($o > $o))).
thf(ff,axiom,((f @ $false) = $true)).
thf(ft,axiom,((f @ $true) = $true)).
thf(conj,conjecture,(! [X : $i, Y : $i, U : $i, V : $i] : ((((((case @ f) @ X) @ Y) @ U) @ V) = V))).



