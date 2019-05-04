#!/usr/bin/env wolframscript
(* ::Package:: *)

(* ::Section:: *)
(*Definitions*)


(* ::Subsection:: *)
(*Define Function*)


f[x_] = (1/4 + 3/7x^2 + 7x^5)(*/(3x + 1/5x^3)*);


(* ::Subsection:: *)
(*Primes for mod p stuff*)


pnumber = 30;
pmax = Prime[pnumber];
fld = GF[pmax];


(* ::Subsection::Closed:: *)
(*Newton Form*)


adddiff[x0_] := Module[{i},
AppendTo[xs,x0];
i = Length [xs];
AppendTo[divdiff,{}]; 
AppendTo[divdiff[[1]],f[x0]];
Do[AppendTo[divdiff[[j]],(divdiff[[j-1,i+2-j]]-divdiff[[j-1,i+1-j]])/(xs[[i]]-xs[[i+1-j]])],{j,2,i}]
];

newton :=
divdiff[[1,1]]+Sum[Product[x-xs[[j]],{j,1,i-1}]*divdiff[[i,1]],{i,2,Length[xs]}];

newtonReconstruct := Module[{n,xi=1},
xs = {};
divdiff = {};
adddiff[xi];
n[x_] = newton//Expand;
While[Not[checkSimilar[f,n,3]],
xi+=1;
adddiff[xi];
n[x_] = newton//Expand;
];
n[x]//Expand
]


(* ::Subsection:: *)
(*Newton Form Mod p*)


adddiff2[x0_] := Module[{i},
AppendTo[xs,x0];
i = Length [xs];
AppendTo[divdiff,{}]; 
AppendTo[divdiff[[1]],fld[{rattoint[f[x0],pmax]}]];
Do[AppendTo[divdiff[[j]],(divdiff[[j-1,i+2-j]]-divdiff[[j-1,i+1-j]])*ModularInverse[xs[[i]]-xs[[i+1-j]],pmax]],{j,2,i}]
];

newtonReconstruct2 := Module[{n,n1,xi=1},
xs = {};
divdiff = {};
adddiff2[xi];
n[x_] = Expand[extract[newton]];
n1[x_] = 0;
While[n[x]=!=n1[x],
n1[x_] = n[x];
xi+=1;
adddiff2[xi];
n[x_] = Expand[extract[newton]];
(*Print[n[x]];*)
];
Expand[extract[n[x]]]
]


(* ::Subsection::Closed:: *)
(*Thiele Form *)


(* ::Subsubsection:: *)
(*Reciprocal Difference*)


p[{}] := 0;
p[{x0_}] := f[x0] ;
p[x_List] := (First[x] - Last[x])/(p[Drop[x,-1]]-p[Drop[x,1]])+p[Drop[Drop[x,-1],1]];


(* ::Subsubsection:: *)
(*Thiele Polynomial*)


thiele[xs_List,x_] := Factor[
p[{First[xs]}]+ContinuedFractionK[
x - Indexed[xs,i], p[xs[[1;;i+1]]]-p[xs[[1;;i-1]]], {i, 1, Length[xs]-1}
]
]


thieleReconstruct := Module[{y={1}, yi=1,t},
	t[x_]=thiele[y,x];
	TimeConstrained[
	While[Not[checkSimilar[f,t,3]],
	yi+=1;
	y = Append[y,yi];
	t[x_]=thiele[y,x]
	],
	3
	];
	thiele[y,x]
]


(* ::Subsection::Closed:: *)
(*Thiele Form Mod p*)


(* ::Subsubsection:: *)
(*Reciprocal Difference*)


p2[{}]:= 0;
p2[{x0_}]:= rattoint[f[x0],pmax];
p2[xs_List]:= PolynomialMod[(First[xs] - Last[xs])*modInverse2[( p2[Drop[xs,-1]]-p2[Drop[xs,1]]),pmax]+p2[Drop[Drop[xs,-1],1]],pmax];


(* ::Subsubsection:: *)
(*Thiele Polynomial*)


thiele2[xs_List,x_] := Factor[
PolynomialMod[p2[{First[xs]}]+ContinuedFractionK[
x - Indexed[xs,i], p2[xs[[1;;i+1]]]-p2[xs[[1;;i-1]]], {i, 1, Length[xs]-1}
],pmax]
]


thieleReconstruct2a := Module[{y={1,2}, yi=2},
	TimeConstrained[
	While[thiele2[y,x]=!=thiele2[Most[y],x],
	yi+=1;
	y = Append[y,yi];
	],
	60
	];
	thiele2[y,x]
]


thieleReconstruct2 := Module[{guess,guess1,guess2,pastprimes},
pastprimes = {};
guess1[x_] = thieleReconstruct2a;
guess[x_]=rationalratrec[thieleReconstruct2a,pmax];
TimeConstrained[
i=0;
While[
Not[checkSimilar[f,guess,3]],
pastprimes = Append[pastprimes,pmax];
pnumber = pnumber+1;
pmax = Prime[pnumber];
guess2[x_] = thieleReconstruct2a;
Print[pmax];
guess1[x_] = rationalcrtCombine[guess1[z],guess2[z],Product[i,{i,pastprimes}],pmax, z];
guess[x_]=rationalratrec[guess1[x],pmax*Product[i,{i,pastprimes}]];
],60];
guess[x]//Factor
]


(* ::Subsection:: *)
(*Rational Reconstruction*)


(* ::Subsubsection:: *)
(*Single Number*)


ratrec[n_,m_]:=Module[ 
{v = {m,0},
w = {n,1},
q,z},
While[w[[1]]^2>= m,
q = Floor[v[[1]]/w[[1]]];
z = v - q*w;
v = w;
w= z;
];
w[[1]]/w[[2]]
]


rattoint[r_,m_]:=Mod[Numerator[r]*ModularInverse[Denominator[r],m],m]


(* ::Subsubsection:: *)
(*Polynomial*)


polyratrec[poly_,m_]:= FromDigits[Reverse[
Table[ratrec[a,m], {a,CoefficientList[poly,x]}]],
x
]


polyrattoint[poly_,m_]:=FromDigits[Reverse[
Table[rattoint[r,m], {r,CoefficientList[poly,x]}]],
x
]


rationalratrec[rational_,m_]:= polyratrec[Numerator[rational],m]/polyratrec[Denominator[rational],m]


(* ::Subsubsection:: *)
(*Chinese Remainder Theorem*)


crtCombine[a1_,a2_,n1_,n2_]:= Module[
{m1,m2,a},
m1 = n2*ModularInverse[n2,n1];
m2 = n1*ModularInverse[n1,n2];
a = Mod[(m1*a1+m2*a2),n1*n2];
a
]


polycrtCombine[f1_,f2_,n1_,n2_,variable_] := Module[{a,b,len},
a = CoefficientList[f1,variable];
b = CoefficientList[f2,variable];
len = Max[Length[a],Length[b]];
FromDigits[Reverse[Table[crtCombine[a[[i]],b[[i]],n1,n2],{i,1,len}]],x]
]


rationalcrtCombine[f1_,f2_,n1_,n2_,variable_] := 
polycrtCombine[Numerator[f1],Numerator[f2],n1,n2,variable]/polycrtCombine[Denominator[f1],Denominator[f2],n1,n2,variable]


(* ::Section:: *)
(*Other Functions and Stuff*)


(* ::Subsubsection:: *)
(*Check similarity of functions*)


checkSimilar[f1_,f2_,n_] := Module[{point,tf}, For[i = 0, i < n, i++,
point = RandomReal[10^(i/2)];
 If[f1[point]==f2[point], tf=True, tf=False; Break[]]
 ];
 tf
 ]


(* ::Subsubsection:: *)
(*Product modulo*)


modProduct[f_,{i_,imin_,imax_}] := Module[{total,j},
function[k_]=f/.i->k;
total = 1;
j=imin; While[j<=imax,total=Mod[total*function[j],pmax];j++];
total
]


polymodProduct[f_,{i_,imin_,imax_}] := Module[{total,j},
function[k_]=f/.i->k;
total = 1;
j=imin; While[j<=imax,total=PolynomialMod[total*function[j],pmax];j++];
total
]


(* ::Subsubsection:: *)
(*Continued Fraction Modulo*)


modContinuedFraction[f_,g_,{i_,imin_,imax_}] := Module[{total,j,terms1,terms2},
function1[k_]=f/.i->k;
function2[k_]=g/.i->k;
terms1 = Reverse[Append[Table[function1[j],{j,imin,imax}],0]];
terms2 = Append[Reverse[Table[function2[j],{j,imin,imax}]],0];
total = 1;
Do[total = PolynomialMod[terms2[[j]] + terms1[[j]]*modInverse2[PolynomialMod[total,pmax],pmax],pmax],{j,imax+1}];
total
]


modInverse2[a_,m_] := If[a==0, ComplexInfinity, ModularInverse[a,m]]


(* ::Subsubsection:: *)
(*Extract polynomial from GF form*)


extract[poly_] := FromDigits[Reverse[
Table[First[First[a,0],0], {a,CoefficientList[poly,x]}]],
x
]
