//the functions DEE, ENN, ENNstar, ALFixedPointsCMOrder,CMPointsCardinality
//were taken from the code accompanying the paper 
//"RATIONAL POINTS ON ATKIN-LEHNER QUOTIENTS OF GEOMETRICALLY HYPERELLIPTIC SHIMURA CURVES" 
//by Oana Padurariu and Ciaran Schembri

allprod := function(seq)
	if seq eq [] then return 1;
	else return &*seq;
	end if;
end function;

allplus := function(seq)
	if seq eq [] then return 0;
	else return &+seq;
	end if;
end function;

GenusOfShim := function(D,N)
	//assert IsSquarefree(D*N);
    assert IsSquarefree(D);
	assert GCD(D,N) eq 1;
    assert IsEven(#PrimeDivisors(D)); 
	e2 := allprod([1-KroneckerSymbol(-4,p) : p in PrimeDivisors(D)])*allprod([1+KroneckerSymbol(-4,q) : q in PrimeDivisors(N)]);
	e3 := allprod([1-KroneckerSymbol(-3,p) : p in PrimeDivisors(D)])*allprod([1+KroneckerSymbol(-3,q) : q in PrimeDivisors(N)]);
	g := 1+ allprod([p-1 : p in PrimeDivisors(D)])*allprod([q+1 : q in PrimeDivisors(N)])/12-e2/4-e3/3;
	return Floor(g);
end function;

DEE := function(R,D)
	f:=Integers()!Index(MaximalOrder(R),R);
	k:=KroneckerCharacter(Discriminant(NumberField(R)));
		return &*([ p : p in PrimeDivisors(D) | GCD(f,p) eq 1 and k(p) eq -1 ] cat [1]);
end function;


ENN := function(R,N)
  f:=Integers()!Index(MaximalOrder(R),R);
  k:=KroneckerCharacter(Discriminant(NumberField(R)));
  return &*([ p : p in PrimeDivisors(N) | GCD(f,p) ne 1 or k(p) eq 1 ] cat [1]);
end function;


ENNstar := function(R,N)
  f:=Integers()!Index(MaximalOrder(R),R);
  k:=KroneckerCharacter(Discriminant(NumberField(R)));
  return &*([ p : p in PrimeDivisors(N) | GCD(f,p) eq 1 and k(p) eq 1 ] cat [1]);
end function;



ALFixedPointsCMOrder := function(D,N,m)
  // return the CM-order associated to the fixed points of w_m on X_0(D,N)
  Rx<x>:=PolynomialRing(Rationals());
  if m eq 2 then
    K1<u1>:=NumberField(x^2+1);
    K2<u2>:=NumberField(x^2+2);
    R1:=sub< MaximalOrder(K1) | u1 >;
    R2:=sub< MaximalOrder(K2) | u2 >;
    return [R1,R2];
  elif m mod 4 eq 3 mod 4 then
    K1<u1>:=NumberField(x^2+m);
    R1:=sub< MaximalOrder(K1) | u1 >;
    R2:=sub< MaximalOrder(K1) | (1+u1)/2 >;
    return [R1,R2];
  else
    K1<u1>:=NumberField(x^2+m);
    R1:=sub< MaximalOrder(K1) | u1 >;
    return [R1];
  end if;
end function;




CMPointsCardinality := function(R,D,N)
  f:=Integers()!Index(MaximalOrder(R),R);
  discR:=Integers()!Discriminant(R);
  DNast:=DEE(R,D)*ENNstar(R,N);
  Cl,m1:=RingClassGroup(R);

  if not(IsSplittingField(NumberField(R),QuaternionAlgebra(D))) then
    return 0;
  end if;

  sigma:= PrimeDivisors(D);
  if [ p : p in sigma | IsDivisibleBy(f,p) ] ne [] then
    return 0;
  end if;

  assert [ p : p in sigma | IsDivisibleBy(f,p) ] eq [];
  k:=KroneckerCharacter(Discriminant(NumberField(R)));
  if [ p : p in sigma | k(p) eq 1 ] ne [] then
    return 0;
  end if;

  if IsDivisibleBy(discR,Integers()!((D*N)/DNast)) then
    return (2^(#PrimeDivisors(DEE(R,D)*ENN(R,N))))*(#Cl);
  else
    return 0;
  end if;
end function;


NumberOfFixedPoints := function(D,N,m)
	return allplus([CMPointsCardinality(R,D,N) : R in ALFixedPointsCMOrder(D,N,m)]); 
end function;

degrees := [1..21];

genera := [Integers()!((d-1)*(d-2)/2) : d in degrees];

DNs := [DN : DN in [6..110011] | IsSquarefree(DN)];


pairs := [];

for DN in DNs do
    for D in Divisors(DN) do
        N := Integers()!(DN/D);
        if D gt 1 and IsEven(#PrimeDivisors(D)) and GenusOfShim(D,N) in genera then
        pairs := pairs cat [[D,N]];
        [D,N];
        end if;
    end for;
end for;

#pairs;

for d in [4..21] do
    g := (d-1)*(d-2)/2;
    f := d+ (1-(-1)^d)/2;
    gQuot := (2*g+2-f)/4;
    Dg := [pair : pair in pairs | GenusOfShim(pair[1],pair[2]) eq g];
    for pair in Dg do
        D := pair[1];
        N := pair[2];
        if [NumberOfFixedPoints(D,N,m) : m in Divisors(D*N) | m gt 1] eq [f : m in Divisors(D*N) | m gt 1] then
        print D,N;
        end if;
    end for;
end for;
