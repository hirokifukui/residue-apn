
SetSeed(20261025);
print "checker_magma_v2 (R03-08): 64 DISTINCT exceptional directions per m=5 case; m=7 invariants only";
Seqelt := func<a | Seqint([Integers()!c : c in Eltseq(a)], 2)>;
procedure Check(name, m, cf, terms, ndirs)
  Z8 := Integers(8); P<t> := PolynomialRing(Z8);
  R<w> := quo<P | P!cf>;
  K<g> := ext<GF(2) | Polynomial(GF(2), cf)>;
  q := 2^m;
  pad := func<x | [Integers()!c : c in Eltseq(x)] cat [0 : i in [1..m-#Eltseq(x)]]>;
  res := func<x | &+[K| (pad(x)[i] mod 2)*g^(i-1) : i in [1..m]]>;
  half := func<x | &+[K| ((pad(x)[i] div 2) mod 2)*g^(i-1) : i in [1..m]]>;
  quarter := func<x | &+[K| ((pad(x)[i] div 4) mod 2)*g^(i-1) : i in [1..m]]>;
  liftK := function(a) s := [Integers()!c : c in Eltseq(a)]; s := s cat [0 : j in [1..m-#s]]; return &+[R| s[i]*w^(i-1) : i in [1..m]]; end function;
  PR<X> := PolynomialRing(R);
  co := func<tt | &+[R| tt[2][i]*w^(i-1) : i in [1..m]]>;
  F := &+[ co(tt)*X^tt[1] : tt in terms];
  Fd := Derivative(F);
  H2 := &+[PR| Binomial(tt[1],2)*co(tt)*X^(tt[1]-2) : tt in terms | tt[1] ge 2];
  Kel := [K!0] cat [g^i : i in [0..q-2]];
  pv := AssociativeArray(); dv := AssociativeArray();
  for a in Kel do x := liftK(a); pv[a] := res(Evaluate(F,x)); dv[a] := res(Evaluate(Fd,x)); end for;
  assert #{pv[a] : a in Kel} eq q;
  assert K!0 notin {dv[a] : a in Kel};
  rho := [b : b in Kel | b ne 0 and dv[b] eq dv[K!0]][1];
  tau := liftK(rho);
  mu := res(Evaluate(H2,tau)) + res(Evaluate(H2,R!0));
  Lam := AssociativeArray(); for a in Kel do Lam[a] := pv[a+rho]+pv[a]+rho*dv[a]; end for;
  Z := [a : a in Kel | Lam[a] eq 0];
  A := AssociativeArray();
  for a in Kel do x := liftK(a); A[a] := half(Evaluate(Fd,x+tau)-Evaluate(Fd,x)); end for;
  Azero := #[a : a in Kel | A[a] eq 0];
  nu := 0; Echeck := true;
  for a in Z do
    x := liftK(a);
    E := quarter(Evaluate(F,x+2*tau) - 2*Evaluate(F,x+tau) + Evaluate(F,x));
    x2 := liftK(a+rho);
    E2 := quarter(Evaluate(F,x2+2*tau) - 2*Evaluate(F,x2+tau) + Evaluate(F,x2));
    if E+E2 ne rho*A[a]+rho^2*mu then Echeck := false; end if;
    if mu ne 0 and A[a] ne 0 then
      if Trace(mu*E/A[a]^2) eq 0 then nu +:= 1; end if;
    end if;
  end for;
  printf "CASE %o m=%o rho=%o mu=%o |Z|=%o Azeros=%o nu=%o Eidentity=%o\n", name, m, Seqelt(rho), Seqelt(mu), #Z, Azero, nu, Echeck;
  if ndirs gt 0 then
    idx := func<x | &+[ pad(x)[i]*8^(i-1) : i in [1..m]]>;
    elts := [ &+[R| e[i]*w^(i-1) : i in [1..m]] : e in CartesianPower([0..7], m)];
    Ftab := AssociativeArray();
    for x in elts do Ftab[idx(x)] := Evaluate(F,x); end for;
    hists := {* *};
    dirs := {@ @};
    tries := 0;
    while #dirs lt ndirs do
      tries +:= 1;
      Include(~dirs, tau + 2*Random(R));
    end while;
    printf "DIRS %o tries=%o distinct=%o
", name, tries, #dirs;
    for alpha in dirs do
      printf "DIR %o %o
", name, pad(alpha);
      cnt := AssociativeArray();
      for x in elts do
        dkey := idx(Ftab[idx(x+alpha)] - Ftab[idx(x)]);
        if IsDefined(cnt,dkey) then cnt[dkey] +:= 1; else cnt[dkey] := 1; end if;
      end for;
      hists := hists join {* Sprint(SequenceToMultiset([cnt[k] : k in Keys(cnt)])) *};
    end for;
    printf "ROWS %o ndirs=%o histograms=%o\n", name, ndirs, hists;
  end if;
end procedure;

Check("c0_A1", 5, [1,0,1,0,0,1], [<1,[1,1,0,1,1]>,<2,[0,1,1,0,0]>,<3,[0,0,1,1,0]>,<4,[0,0,0,1,0]>,<6,[0,1,1,0,0]>,<8,[0,1,1,1,0]>,<9,[1,1,0,1,0]>,<10,[1,0,0,1,1]>,<12,[0,1,1,1,1]>,<16,[0,0,0,0,1]>,<17,[1,1,1,1,1]>,<18,[1,0,1,1,1]>,<20,[0,0,1,1,0]>,<24,[1,0,1,1,0]>,<3,[2,2,0,0,2]>,<5,[0,0,0,2,2]>,<7,[2,0,0,2,2]>,<9,[0,2,2,0,2]>,<11,[2,2,0,2,2]>,<13,[2,2,2,2,0]>,<17,[2,2,2,2,2]>,<19,[0,2,2,0,2]>,<21,[2,0,2,2,0]>,<25,[2,0,2,0,0]>,<33,[0,0,2,2,0]>,<35,[2,0,2,0,0]>,<37,[2,2,2,2,2]>,<41,[0,2,0,0,0]>,<49,[2,0,2,0,0]>], 64);
Check("F1_c0A1_plus2X2", 5, [1,0,1,0,0,1], [<1,[1,1,0,1,1]>,<2,[0,1,1,0,0]>,<3,[0,0,1,1,0]>,<4,[0,0,0,1,0]>,<6,[0,1,1,0,0]>,<8,[0,1,1,1,0]>,<9,[1,1,0,1,0]>,<10,[1,0,0,1,1]>,<12,[0,1,1,1,1]>,<16,[0,0,0,0,1]>,<17,[1,1,1,1,1]>,<18,[1,0,1,1,1]>,<20,[0,0,1,1,0]>,<24,[1,0,1,1,0]>,<3,[2,2,0,0,2]>,<5,[0,0,0,2,2]>,<7,[2,0,0,2,2]>,<9,[0,2,2,0,2]>,<11,[2,2,0,2,2]>,<13,[2,2,2,2,0]>,<17,[2,2,2,2,2]>,<19,[0,2,2,0,2]>,<21,[2,0,2,2,0]>,<25,[2,0,2,0,0]>,<33,[0,0,2,2,0]>,<35,[2,0,2,0,0]>,<37,[2,2,2,2,2]>,<41,[0,2,0,0,0]>,<49,[2,0,2,0,0]>,<2,[2,0,0,0,0]>], 64);
Check("P53nat", 5, [1,0,1,0,0,1], [<1,[1,0,0,0,0]>,<2,[1,0,0,0,0]>,<3,[1,0,0,0,0]>,<9,[1,0,0,0,0]>,<10,[1,0,0,0,0]>,<18,[1,0,0,0,0]>,<24,[1,0,0,0,0]>], 64);
Check("P53sp", 5, [1,0,1,0,0,1], [<1,[1,0,0,0,0]>,<2,[1,0,0,0,0]>,<3,[1,0,0,0,0]>,<9,[1,0,0,0,0]>,<10,[1,0,0,0,0]>,<18,[1,0,0,0,0]>,<24,[1,0,0,0,0]>,<20,[2,0,0,0,0]>], 64);
Check("P73nat", 7, [1,1,0,0,0,0,0,1], [<1,[1,0,0,0,0,0,0]>,<2,[1,0,0,0,0,0,0]>,<3,[1,0,0,0,0,0,0]>,<33,[1,0,0,0,0,0,0]>,<34,[1,0,0,0,0,0,0]>,<66,[1,0,0,0,0,0,0]>,<96,[1,0,0,0,0,0,0]>], 0);
Check("P73sp", 7, [1,1,0,0,0,0,0,1], [<1,[1,0,0,0,0,0,0]>,<2,[1,0,0,0,0,0,0]>,<3,[1,0,0,0,0,0,0]>,<33,[1,0,0,0,0,0,0]>,<34,[1,0,0,0,0,0,0]>,<66,[1,0,0,0,0,0,0]>,<96,[1,0,0,0,0,0,0]>,<68,[2,0,0,0,0,0,0]>], 0);
print "DONE";