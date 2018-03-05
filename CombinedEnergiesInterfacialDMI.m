(* ::Package:: *)

(* 
    Mathematica library to calculate the energy of skyrmions as well as their stable radius, DW width, etc.
    Copyright (C) 2018  Felix Buettner (felixbuettner@gmail.com)

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>. 
*)



BeginPackage["CombinedEnergiesInterfacialDMI`"]
(* Exported symbols added here with SymbolName::usage *)  

mz::usage="
some docstring
";
Rho0::usage="
some docstring
";

Rho::usage="";

EofR::usage="";
ElocalofR::usage="";
EnonlocalofR::usage="";
sigmaStraightWall::usage="";
DeltaPsiInf::usage="";
DMIorSFstabilized::usage="";
DMIorSFstabilizedFast::usage="";

FitRBzData::usage="";

FindAllExtrema::usage="";
DetermineEnergyBarriers::usage="";
CollapseRadiusMinimumEnergyBarrierVerbose3::usage="
some docstring
";
ReRunCollapseRadiusMinimumEnergyBarrierVerbose3::usage="
some docstring
";



Begin["`Private`"] (* Begin Private Context *) 


(* 
   **************************
    Energy functions
   **************************
*)

Needs["NumericalCalculus`"];
SetAttributes[debugPrint, HoldAll];
SetAttributes[debugPrintVerbose, HoldAll];

\[Mu]0=4\[Pi] 10^-7 10^-9;

Rho0[\[Rho]_]:=Log[Sinh[\[Rho]]+Sqrt[-1+Sinh[\[Rho]]^2]]
Rho[\[Rho]0_]:=ArcSinh[(1+E^(2\[Rho]0))/(2 E^\[Rho]0)]
\[Theta][\[CurlyRho]_, \[Rho]0_] :=2ArcTan[Exp[(\[CurlyRho]-\[Rho]0)]]+2ArcTan[Exp[(\[CurlyRho]+\[Rho]0)]]
mz1[\[CurlyRho]_,\[Rho]0_]:=Cos[\[Theta][\[CurlyRho],\[Rho]0]]
(*another way to write mz:*)
mz[\[CurlyRho]_,\[Rho]0_]:=-1+(4 Sinh[\[CurlyRho]]^2)/(Cosh[2 \[CurlyRho]]+Cosh[2 \[Rho]0])
(* EA *)
IA[\[Rho]_]:=2 \[Rho]+2 /\[Rho]+1.93(\[Rho]-.65)Exp[-1.48(\[Rho]-.65)]
EA[R_,\[CapitalDelta]_,d_,A_]:=2\[Pi] A d IA[R/\[CapitalDelta]]
(* EK *)
IK[\[Rho]_]:=2\[Rho]-1/3 Exp[-(\[Rho]/Sqrt[2])]
EK[R_,\[CapitalDelta]_,d_,Ku_]:=2\[Pi] Ku d \[CapitalDelta]^2 IK[R/\[CapitalDelta]]
(* ED *)
ID[\[Rho]_]:=\[Pi] \[Rho]+1/2 Exp[-\[Rho]]
ED[R_,\[CapitalDelta]_,d_,\[Psi]_,Di_,Db_]:=-2\[Pi] d  \[CapitalDelta](Di Cos[\[Psi]]-Db Sin[\[Psi]])ID[R/\[CapitalDelta]]
(* EZ *)
IZ[\[Rho]_]:=\[Rho]^2+\[Pi]^2/12-0.42Exp[-\[Rho]^2]
EZ[R_,\[CapitalDelta]_,d_,Ms_,Bz_]:=-2\[Pi] d \[CapitalDelta]^2 Ms Bz IZ[R/\[CapitalDelta]]
(* Eds *)
(* sigmaDeltaWinf in units of \[Mu]0Ms^2\[CapitalDelta] *)
sigmaDeltaWinf[t_]:=(t (2 \[Pi]+t+2 t Log[\[Pi]]-2 t Log[t]+4 \[Pi] LogGamma[t/\[Pi]])-4 \[Pi]^2 PolyGamma[-2,t/\[Pi]])/(2 \[Pi] t)
(* Mathematica uses unconventional definitions for elliptic function. Convert the definitions to one mathing the integral books. *)
LiteratureEllipticK[k_]:=EllipticK[k^2/(-1+k^2)]/Sqrt[1-k^2]
LiteratureEllipticE[k_]:=EllipticE[k^2]
LiteratureEllipticArgument[x_]:=(2x)/Sqrt[1+4x^2]
h[x_]:=Block[{k=LiteratureEllipticArgument[x],K=LiteratureEllipticK[k],E=LiteratureEllipticE[k]},
-((8x)/(3\[Pi]))(1-1/k^3 ((1-k^2)K+(2k^2-1)E))]
Is[R_,\[CapitalDelta]_,d_]:=IZ[R/\[CapitalDelta]]h[R/d]-1/2 IK[R/\[CapitalDelta]]sigmaDeltaWinf[d/\[CapitalDelta]]-(0.29-0.4Exp[-2R/\[CapitalDelta]])/Cosh[4/9 Log[d/(1.65R)]]^2
Eds[R_,\[CapitalDelta]_,d_,Ms_]:=-2\[Pi] \[Mu]0 Ms^2 d \[CapitalDelta]^2 Is[R,\[CapitalDelta],d]
Eds1[R_,\[CapitalDelta]_,d_,Ms_]:=-2\[Pi] \[Mu]0 Ms^2 d \[CapitalDelta]^2 IZ[R/\[CapitalDelta]]h[R/d]
Eds2[R_,\[CapitalDelta]_,d_,Ms_]:=-2\[Pi] \[Mu]0 Ms^2 d \[CapitalDelta]^2 (-(1/2)IK[R/\[CapitalDelta]]sigmaDeltaWinf[d/\[CapitalDelta]])
Eds3[R_,\[CapitalDelta]_,d_,Ms_]:=-2\[Pi] \[Mu]0 Ms^2 d \[CapitalDelta]^2 (-((0.58-0.8Exp[-2R/\[CapitalDelta]])/Cosh[4/9 Log[d/(1.65R)]]^2))
(* Edv *)
Ivt[\[Rho]_,t_]:=Block[{fv,n,kp,dIv0,Ivinf,a},
n=1/6\[Rho]^(2/3)Exp[-0.31\[Rho]]+1;
kp=10/(1+Exp[10\[Rho]-25])+(27/10+140/(10\[Rho]-8))/(1+Exp[-10\[Rho]+25]);
Ivinf=1/2(1-0.27 Exp[-1.164\[Rho]]);
dIv0=Log[2]+4.45(\[Rho]-0.283)/(\[Rho] (\[Rho]+0.93)^2);
a=dIv0/(2Log[2]Ivinf);
fv=(2\[Pi] t a)/((2\[Pi])^n+(2Log[2]t a)^n)^(1/n)-10^(-0.02kp^2+1.3kp-2.45)(t a)^2/(3\[Pi]+2Log[2]t a)^kp;
Return[Log[2]/\[Pi] Ivinf fv];
];
Edv[R_,\[CapitalDelta]_,d_,\[Psi]_,Ms_]:=4\[Pi] \[Mu]0 Ms^2 d \[CapitalDelta] R Cos[\[Psi]]^2 Ivt[R/\[CapitalDelta],d/\[CapitalDelta]]
EKeff[R_,\[CapitalDelta]_,d_,Ku_,Ms_]:=EK[R,\[CapitalDelta],d,Ku]+Eds2[R,\[CapitalDelta],d,Ms]
EZeff[R_,\[CapitalDelta]_,d_,Ms_,Bz_]:=EZ[R,\[CapitalDelta],d,Ms,Bz]+Eds1[R,\[CapitalDelta],d,Ms]
DeltaMin[R_,A_,Ku_,Ms_,Bz_]:=(2 Sqrt[10] A R)/Sqrt[A (68 A+5 R^2 (8 Ku+Ms^2 (-8 Bz+15 \[Mu]0)))]

(* Multilayers in effective mediumm model, assuming Db=0 *)
EtotalEM[R_,\[CapitalDelta]_,t_,p_,nl_,\[Psi]_,A_,Ku_,Di_,Ms_,Bz_]:=Block[{f=t/p,d=p nl,energy},
energy=1/(f A d) (EA[R,\[CapitalDelta],d,f A]+EK[R,\[CapitalDelta],d,f Ku-1/2 (f-f^2)\[Mu]0 Ms^2]+ED[R,\[CapitalDelta],d,\[Psi],f Di,0]+Eds[R,\[CapitalDelta],d,f Ms]+Edv[R,\[CapitalDelta],d,\[Psi],f Ms]+EZ[R,\[CapitalDelta],d,f Ms,Bz]);
Return[energy];
];

(* Conveniece function to plot / analyze the energy as a function of radius with Delta and psi being already minimized.
   Note that the function DeltaPsi is defined further below. *)
EofR[R_?NumericQ,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_,useLargeRapproximation_:Automatic]:=Piecewise[{
{Piecewise[{
{EtotalEM[R,"\[CapitalDelta]",t,p,nl,"\[Psi]",A,Ku,Di,Ms,Bz]/.DeltaPsi[R,t,p,nl,A,Ku,Di,Ms,Bz],R>0&&R<LargeRThresholdR[t,p,nl,A,Ku,Di,Ms]},
{LargeREnergy[R,t,p,nl,A,Ku,Di,Ms,Bz],R>LargeRThresholdR[t,p,nl,A,Ku,Di,Ms]},
{E0,R==0},
{Infinity,True}}],useLargeRapproximation===Automatic},
{Piecewise[{
{LargeREnergy[R,t,p,nl,A,Ku,Di,Ms,Bz],R>0},
{E0,R==0},
{Infinity,True}}],useLargeRapproximation},
{Piecewise[{
{EtotalEM[R,"\[CapitalDelta]",t,p,nl,"\[Psi]",A,Ku,Di,Ms,Bz]/.DeltaPsi[R,t,p,nl,A,Ku,Di,Ms,Bz],R>0},
{E0,R==0},
{Infinity,True}}],Not[useLargeRapproximation]}
}]

ElocalofR[R_?NumericQ,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_,useLargeRapproximation_:Automatic]:=Block[{f=t/p,d=p nl},Piecewise[{
{Piecewise[{
{(1/(f A d) (EA[R,"\[CapitalDelta]",d,f A]+EK[R,"\[CapitalDelta]",d,f Ku-1/2 (f-f^2)\[Mu]0 Ms^2]+ED[R,"\[CapitalDelta]",d,"\[Psi]",f Di,0]+Eds2[R,"\[CapitalDelta]",d,f Ms]+Edv[R,"\[CapitalDelta]",d,"\[Psi]",f Ms]))/.DeltaPsi[R,t,p,nl,A,Ku,Di,Ms,Bz],R>0&&R<LargeRThresholdR[t,p,nl,A,Ku,Di,Ms]},
{LargeRLocalEnergy[R,t,p,nl,A,Ku,Di,Ms,Bz],R>LargeRThresholdR[t,p,nl,A,Ku,Di,Ms]},
{E0,R==0},
{Infinity,True}}],useLargeRapproximation===Automatic},
{Piecewise[{
{LargeRLocalEnergy[R,t,p,nl,A,Ku,Di,Ms,Bz],R>0},
{E0,R==0},
{Infinity,True}}],useLargeRapproximation},
{Piecewise[{
{(1/(f A d) (EA[R,"\[CapitalDelta]",d,f A]+EK[R,"\[CapitalDelta]",d,f Ku-1/2 (f-f^2)\[Mu]0 Ms^2]+ED[R,"\[CapitalDelta]",d,"\[Psi]",f Di,0]+Eds2[R,"\[CapitalDelta]",d,f Ms]+Edv[R,"\[CapitalDelta]",d,"\[Psi]",f Ms]))/.DeltaPsi[R,t,p,nl,A,Ku,Di,Ms,Bz],R>0},
{E0,R==0},
{Infinity,True}}],Not[useLargeRapproximation]}
}]
];

ElocalofRFast[R_?NumericQ,\[CapitalDelta]_,\[Psi]_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=Block[{f=t/p,d=p nl},Piecewise[{
{(1/(f A d) (EA[R,\[CapitalDelta],d,f A]+EK[R,\[CapitalDelta],d,f Ku-1/2 (f-f^2)\[Mu]0 Ms^2]+ED[R,\[CapitalDelta],d,\[Psi],f Di,0]+Eds2[R,\[CapitalDelta],d,f Ms]+Edv[R,\[CapitalDelta],d,\[Psi],f Ms])),R>0&&R<LargeRThresholdR[t,p,nl,A,Ku,Di,Ms]},
{LargeRLocalEnergy[R,t,p,nl,A,Ku,Di,Ms,Bz],R>LargeRThresholdR[t,p,nl,A,Ku,Di,Ms]},
{E0,R==0},
{Infinity,True}}]
];

EnonlocalofR[R_?NumericQ,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_,useLargeRapproximation_:Automatic]:=Block[{f=t/p,d=p nl},Piecewise[{
{Piecewise[{
{(1/(f A d) (Eds1[R,"\[CapitalDelta]",d,f Ms]+Eds3[R,"\[CapitalDelta]",d,f Ms]+EZ[R,"\[CapitalDelta]",d,f Ms,Bz]))/.DeltaPsi[R,t,p,nl,A,Ku,Di,Ms,Bz],R>0&&R<LargeRThresholdR[t,p,nl,A,Ku,Di,Ms]},
{LargeRNonlocalEnergy[R,t,p,nl,A,Ku,Di,Ms,Bz],R>LargeRThresholdR[t,p,nl,A,Ku,Di,Ms]},
{0,R==0},
{Infinity,True}}],useLargeRapproximation===Automatic},
{Piecewise[{
{LargeRNonlocalEnergy[R,t,p,nl,A,Ku,Di,Ms,Bz],R>0},
{E0,R==0},
{Infinity,True}}],useLargeRapproximation},
{Piecewise[{
{(1/(f A d) (Eds1[R,"\[CapitalDelta]",d,f Ms]+Eds3[R,"\[CapitalDelta]",d,f Ms]+EZ[R,"\[CapitalDelta]",d,f Ms,Bz]))/.DeltaPsi[R,t,p,nl,A,Ku,Di,Ms,Bz],R>0},
{E0,R==0},
{Infinity,True}}],Not[useLargeRapproximation]}
}]
];

EnonlocalofRFast[R_?NumericQ,\[CapitalDelta]_,\[Psi]_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=Block[{f=t/p,d=p nl},Piecewise[{
{(1/(f A d) (Eds1[R,\[CapitalDelta],d,f Ms]+Eds3[R,\[CapitalDelta],d,f Ms]+EZ[R,\[CapitalDelta],d,f Ms,Bz])),R>0&&R<LargeRThresholdR[t,p,nl,A,Ku,Di,Ms]},
{LargeRNonlocalEnergy[R,t,p,nl,A,Ku,Di,Ms,Bz],R>LargeRThresholdR[t,p,nl,A,Ku,Di,Ms]},
{0,R==0},
{Infinity,True}}]
];

DMIorSFstabilized[R_?NumericQ,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=If[
EnonlocalofR[R+0.01+R/1000,t,p,nl,A,Ku,Di,Ms,Bz]-EnonlocalofR[R-0.01-R/1000,t,p,nl,A,Ku,Di,Ms,Bz]<
ElocalofR[R+0.01+R/1000,t,p,nl,A,Ku,Di,Ms,Bz]-ElocalofR[R-0.01-R/1000,t,p,nl,A,Ku,Di,Ms,Bz],"strayfield","DMI"];

DMIorSFstabilizedFast[R_?NumericQ,\[CapitalDelta]_,\[Psi]_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=If[
EnonlocalofRFast[R,\[CapitalDelta],\[Psi],t,p,nl,A,Ku,Di,Ms,Bz]-EnonlocalofR[R-0.01-R/1000,t,p,nl,A,Ku,Di,Ms,Bz]<
ElocalofRFast[R,\[CapitalDelta],\[Psi],t,p,nl,A,Ku,Di,Ms,Bz]-ElocalofR[R-0.01-R/1000,t,p,nl,A,Ku,Di,Ms,Bz],"strayfield","DMI"];

E0=Block[{\[CapitalDelta],d,A},Evaluate[EA[ArcSinh[1]\[CapitalDelta],\[CapitalDelta],d,A]/(A d)]];

(* Radii are determined numerically. Comparing them is possible only when considering numerical tolerances. Define appropriate functions here: *)
EqualRadii[R1_,R2_]:=Block[{},
If[Im[R1]!=0||Im[R2]!=0||Re[R1]<0||Re[R2]<0,Return[False];];
If[R1==0||R2==0,Return[R1==R2];];
If[Abs[R1-R2]/(R1+R2)<0.01,Return[True];];
If[Abs[R1-R2]<0.01,Return[True];];
Return[False];];

(* \[Psi] can be obtained analytically for pure interfacial DMI systems (i.e., when Db=0). However, we need an analytical equivalent of MinMax to limit the range of Cos[\[Psi]] to [-1,1]. This is done by MinMaxHelper[x]. Note: The larger exponent, the steeper the transition between the linear regime and the constant regime. Only even integer values should be used.
The factor (1-10^-10) in MinMaxHelper ensures that the magnitude of the return value of the function is \[LessEqual] 1 even within numerical noise. Otherwise, ArcCos might return a complex result that can't be dealt with in the following algorithms. *)
MinMaxHelper[x_]:=Block[{exponent=100},((1-10^-10)x)/(1+x^exponent)^(1/exponent)]

(* Analysis for large R (almost straight walls) *)
(* Straight wall domain wall energy density, normalized to  f Sqrt[A Ku]*)
sigmaSW[\[CapitalDelta]_,t_,p_,nl_,\[Psi]_,A_,Ku_,Di_,Ms_]:=Block[{f=t/p,d=p nl,sigma,Kup=f Ku-1/2 (f-f^2)\[Mu]0 Ms^2},
sigma=1/(f Sqrt[A Ku]) ((2f A)/\[CapitalDelta]+2Kup \[CapitalDelta]-\[Pi] f Di Cos[\[Psi]]+\[Mu]0 (f Ms)^2 \[CapitalDelta] sigmaDeltaWinf[d/\[CapitalDelta]]+1/\[Pi] Log[2]\[Mu]0 (f Ms)^2 \[CapitalDelta] Cos[\[Psi]]^2 ((2\[Pi] d)/(2\[Pi] \[CapitalDelta]+2Log[2]d)-(82(d/\[CapitalDelta])^2)/(10(2Log[2]d/\[CapitalDelta]+3\[Pi])^(27/10))));
Return[sigma];
];

(* Straight wall domain wall energy density, in units of Ad/nm, for public usage. *)
sigmaStraightWall[t_,p_,nl_,A_,Ku_,Di_,Ms_]:=Block[{f=t/p},
(1/A)(f Sqrt[A Ku])*sigmaSW["\[CapitalDelta]",t,p,nl,"\[Psi]",A,Ku,Di,Ms]/.DeltaPsiInf[t,p,nl,A,Ku,Di,Ms]
];

FitRBzData[data_(* expecting a list where each item contains replacement rules {"Bz"\[Rule]value,"R"\[Rule]value} and possibly others*)]:=Module[
{localData,Bzlist,Rlist,fitData,fit1,fit2,a,b,c,y},
localData=Select[data,("Bz"/.#)<0&];
Bzlist=Map["Bz"/.#&,localData];
Rlist=Map["R"/.#&,localData];
fitData=Transpose[{Bzlist,Rlist}];
fit1=Quiet[NonlinearModelFit[fitData,(a*Min[Rlist])/(y/Max[Bzlist])^c+b*Min[Rlist],{{a,1},{b,1},{c,1}},y,Weights->0.01/Rlist]];
fit2=Quiet[NonlinearModelFit[fitData,(a*Min[Rlist])/(y/Max[Bzlist])^c+b*Min[Rlist],{{a,1},{b,1},{c,-1}},y,Weights->0.01/Rlist]];
If[Quiet[fit1["RSquared"]<fit2["RSquared"]],Return[fit2]];
Return[fit1];
];


(* 
   **************************
    Large R approximation 
   **************************
*)

(* Psi as analytically obtained from the straight wall energy. The function returns a floating point value. *)
PsiDiInf[\[CapitalDelta]_,t_,p_,nl_,Di_,Ms_]:=Block[{f=t/p,d=p nl,\[Psi]s},
\[Psi]s=ArcCos[MinMaxHelper[((\[Pi] f Di)/(2/\[Pi] Log[2]\[Mu]0 (f Ms)^2 \[CapitalDelta] ((2\[Pi] d)/(2\[Pi] \[CapitalDelta]+2Log[2]d)-(82(d/\[CapitalDelta])^2)/(10(2Log[2]d/\[CapitalDelta]+3\[Pi])^(27/10)))))]];
Return[\[Psi]s];
];

(* Delta obtained by setting the derivative of the straight wall energy with respect to \[CapitalDelta] to zero. \[Psi] is used as determined by PsiDiInf. A replacement rule in the form {"\[CapitalDelta]"\[Rule]value,"\[Psi]"\[Rule]value} is returned. *)
DeltaPsiInf[t_,p_,nl_,A_,Ku_,Di_,Ms_]:=DeltaPsiInf[t,p,nl,A,Ku,Di,Ms]=Block[{\[CapitalDelta],\[CapitalDelta]s,\[Psi],\[Psi]s,result},
\[CapitalDelta]s=\[CapitalDelta]/.FindRoot[ {D[sigmaSW[\[CapitalDelta],t,p,nl,PsiDiInf[\[CapitalDelta],t,p,nl,Di,Ms],A,Ku,Di,Ms],\[CapitalDelta]]==0},{\[CapitalDelta],1},DampingFactor-> 1/2];
\[Psi]s=PsiDiInf[\[CapitalDelta]s,t,p,nl,Di,Ms];
result={"\[CapitalDelta]"->\[CapitalDelta]s,"\[Psi]"->\[Psi]s};
Return[result];
];

(* Total energy at large radii, including the non-local energies that depend on R. Will be used to calculate the equilibrium size of bubble skyrmions. A floating point number is returned. *)
LargeREnergy[R_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=Block[{\[CapitalDelta],\[Psi],f=t/p,d=p nl,Kup=f Ku-1/2 (f-f^2)\[Mu]0 Ms^2,energy,a,b,c},
{\[CapitalDelta],\[Psi]}={"\[CapitalDelta]","\[Psi]"}/.DeltaPsiInf[t,p,nl,A,Ku,Di,Ms];
a=2\[Pi] d (f Sqrt[A Ku]sigmaSW[\[CapitalDelta],t,p,nl,\[Psi],A,Ku,Di,Ms])-\[Mu]0 (f Ms)^2 d^2 (6 Log[2]-1);
b=\[Mu]0 (f Ms)^2 d^2 2;
c=-2\[Pi] (f Ms) Bz d ;
energy=1/(f A d) (a R-b R Log[R/d]+c R^2);
(*energy=1/(f A d) (2\[Pi] R d (f Sqrt[A Ku]sigmaSW[\[CapitalDelta],t,p,nl,\[Psi],A,Ku,Di,Ms])-\[Mu]0 (f Ms)^2 d^2 R (6 Log[2]-1+2Log[R/d])-2\[Pi] (f Ms) Bz d R^2);*)
Return[energy];
];

(* Total energy at large radii, including the non-local energies that depend on R. Will be used to calculate the equilibrium size of bubble skyrmions. A floating point number is returned. *)
LargeRLocalEnergy[R_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=Block[{\[CapitalDelta],\[Psi],f=t/p,d=p nl,Kup=f Ku-1/2 (f-f^2)\[Mu]0 Ms^2,energy,a1,a2,b,c},
{\[CapitalDelta],\[Psi]}={"\[CapitalDelta]","\[Psi]"}/.DeltaPsiInf[t,p,nl,A,Ku,Di,Ms];
a1=2\[Pi] d (f Sqrt[A Ku]sigmaSW[\[CapitalDelta],t,p,nl,\[Psi],A,Ku,Di,Ms]);
a2=-\[Mu]0 (f Ms)^2 d^2 (6 Log[2]-1);
b=\[Mu]0 (f Ms)^2 d^2 2;
c=-2\[Pi] (f Ms) Bz d ;
energy=1/(f A d) (a1 R);
(*energy=1/(f A d) (2\[Pi] R d (f Sqrt[A Ku]sigmaSW[\[CapitalDelta],t,p,nl,\[Psi],A,Ku,Di,Ms])-\[Mu]0 (f Ms)^2 d^2 R (6 Log[2]-1+2Log[R/d])-2\[Pi] (f Ms) Bz d R^2);*)
Return[energy];
];

(* Total energy at large radii, including the non-local energies that depend on R. Will be used to calculate the equilibrium size of bubble skyrmions. A floating point number is returned. *)
LargeRNonlocalEnergy[R_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=Block[{\[CapitalDelta],\[Psi],f=t/p,d=p nl,Kup=f Ku-1/2 (f-f^2)\[Mu]0 Ms^2,energy,a1,a2,b,c},
{\[CapitalDelta],\[Psi]}={"\[CapitalDelta]","\[Psi]"}/.DeltaPsiInf[t,p,nl,A,Ku,Di,Ms];
a1=2\[Pi] d (f Sqrt[A Ku]sigmaSW[\[CapitalDelta],t,p,nl,\[Psi],A,Ku,Di,Ms]);
a2=-\[Mu]0 (f Ms)^2 d^2 (6 Log[2]-1);
b=\[Mu]0 (f Ms)^2 d^2 2;
c=-2\[Pi] (f Ms) Bz d ;
energy=1/(f A d) (a2 R-b R Log[R/d]+c R^2);
(*energy=1/(f A d) (2\[Pi] R d (f Sqrt[A Ku]sigmaSW[\[CapitalDelta],t,p,nl,\[Psi],A,Ku,Di,Ms])-\[Mu]0 (f Ms)^2 d^2 R (6 Log[2]-1+2Log[R/d])-2\[Pi] (f Ms) Bz d R^2);*)
Return[energy];
];

(* LargeREnergy can be minimized with respect to R. It is not possible to obtain the R corresponding to a given value 
   of the magnetic field Bz analytically. However, it is possible to invert the question and calculate the Bz yielding 
   a skyrmion of radius R. Note that the field value is returned directly, i.e., as a float and not as a replacement rule.
   Also note the unit of the field is J/Anm^2, i.e., the value will be on the order of (10^-20).*)
LargeRBz[R_,t_,p_,nl_,A_,Ku_,Di_,Ms_]:=Block[{\[CapitalDelta],\[Psi],f=t/p,d=p nl,Bz,a,b,c},
{\[CapitalDelta],\[Psi]}={"\[CapitalDelta]","\[Psi]"}/.DeltaPsiInf[t,p,nl,A,Ku,Di,Ms];
a=(2\[Pi] d (f Sqrt[A Ku]sigmaSW[\[CapitalDelta],t,p,nl,\[Psi],A,Ku,Di,Ms])-\[Mu]0 (f Ms)^2 d^2 (6 Log[2]-1));
b=\[Mu]0 (f Ms)^2 d^2 2;
c=-2\[Pi] (f Ms) Bz d;
Bz= -((b Log[R/d]+b-a)/(4\[Pi] R d (f Ms)));
Return[Bz];
];

(* Minimum radius that can be used in the LargeRBz function to obtain a meaningful result. This is the radius that yields the minimum (most negative) field in LargeRBz. For smaller radii, larger (even positive) fields are returned, which is unphysical. *)
LargeRSmallestPossibleEquilibrium[t_,p_,nl_,A_,Ku_,Di_,Ms_]:=Block[{f=t/p,d=p nl,\[CapitalDelta],\[Psi],Rmin,a,b},
{\[CapitalDelta],\[Psi]}={"\[CapitalDelta]","\[Psi]"}/.DeltaPsiInf[t,p,nl,A,Ku,Di,Ms];
a=(2\[Pi] d (f Sqrt[A Ku]sigmaSW[\[CapitalDelta],t,p,nl,\[Psi],A,Ku,Di,Ms])-\[Mu]0 (f Ms)^2 d^2 (6 Log[2]-1));
b=\[Mu]0 (f Ms)^2 d^2 2;
Rmin=d Exp[a/b];
Return[Rmin];
];

(* Minimum (most negative) Bz that can be used in the LargeRBz function to obtain a meaningful result. This is the minimum (most negative) field in LargeRBz.  *)
LargeRSmallestPossibleFieldForEquilibrium[t_,p_,nl_,A_,Ku_,Di_,Ms_]:=Block[{f=t/p,d=p nl,\[CapitalDelta],\[Psi],Rmin,a,b},
{\[CapitalDelta],\[Psi]}={"\[CapitalDelta]","\[Psi]"}/.DeltaPsiInf[t,p,nl,A,Ku,Di,Ms];
a=(2\[Pi] d (f Sqrt[A Ku]sigmaSW[\[CapitalDelta],t,p,nl,\[Psi],A,Ku,Di,Ms])-\[Mu]0 (f Ms)^2 d^2 (6 Log[2]-1));
b=\[Mu]0 (f Ms)^2 d^2 2;
Rmin=LargeRSmallestPossibleEquilibrium[t,p,nl,A,Ku,Di,Ms];
Return[(a-b*(1+Log[Rmin/d]))/(4\[Pi] f Ms d Rmin)];
];

(* Numerically find the equilibrium radius corresponding to a given field, in the large radius approximation. Here, \[CapitalDelta] and \[Psi] do not depend on R and can be calculated separately before the numerical minimization. We cache the result for quickly returning the result if the function is called again with the same parameters. A replacement rule in the form {R\[Rule]value,\[CapitalDelta]\[Rule]value,\[Psi]\[Rule]value} is returned. *)
LargeRMinimum[t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=LargeRMinimum[t,p,nl,A,Ku,Di,Ms,Bz]=Block[{\[CapitalDelta]s,\[Psi]s,R,Rs,Rsnew,result,counter=1},
(* A solution can only exist if the field is > than LargeRSmallestPossibleFieldForEquilibrium. Check this first. *)
If[Bz<LargeRSmallestPossibleFieldForEquilibrium[t,p,nl,A,Ku,Di,Ms],Return[0]];
{\[CapitalDelta]s,\[Psi]s}={"\[CapitalDelta]","\[Psi]"}/.DeltaPsiInf[t,p,nl,A,Ku,Di,Ms];
Rs=R/.FindRoot[ D[LargeREnergy[R,t,p, nl,A,Ku,Di,Ms,Bz],R]==0,{R,10^10}];
If[Im[(Rs)]!=0||Re[(Rs)]<0||Not[IsExtremumLargeR[Rs,t,p,nl,A,Ku,Di,Ms,Bz]],
(* Maybe we found the maximum because the minimum is at R>10^10. Try to repeat the search with a larger R0 *)
Rs=R/.FindRoot[ D[LargeREnergy[R,t,p, nl,A,Ku,Di,Ms,Bz],R]==0,{R,10^20}];
];
If[Im[(Rs)]!=0||Re[(Rs)]<0,Return[0]];
(* Sometimes maximum and minimum are close together. In that case, we do a fine search around the maximum to find the minimum. *)
While[IsMaximumLargeR[Rs,t,p,nl,A,Ku,Di,Ms,Bz],
Rs=R/.FindRoot[D[LargeREnergy[R,t,p, nl,A,Ku,Di,Ms,Bz],R]==0,{R,Rs*1.2^counter}];
counter+=1;
If[counter>20,
debugPrint["RDeltaPsiLargeR: Could not find minimum in 20 iterations. Bz=",Bz];
Return[0];
];
];
Return[Rs];
];

(* *)
LargeRMaximum[R_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=Block[{\[CapitalDelta],\[Psi],Rs,R0,R1,R2,Rmax,counter=1},
(* Coarse sampling: find an inverval [R1,R2] of length 5 or less that contains the maximum. *)
R1=0;
R2=R;
If[R2===Infinity,
R2=LargeRThresholdR[t,p,nl,A,Ku,Di,Ms];
While[D[LargeREnergy[Rs,t,p, nl,A,Ku,Di,Ms,Bz],Rs]>0/.Rs->R2,
R2*=10];
];
While[R2-R1>5 && counter<100,
R0=(R1+R2)/2;
If[D[LargeREnergy[Rs,t,p, nl,A,Ku,Di,Ms,Bz],Rs]>0/.Rs->R0,
R1=R0,
R2=R0];
counter+=1;
(*If[counter>100,
debugPrint["MaximumPositionLargeR: Could not find suitable interval in 100 iterations"];
Return[0];
];*)
];
(* If R1=0 then there is no maximum. *)
If[R1==0,Return[0]];
(* Now find the actual maximum within this interval. *)
Rmax=Rs/.FindRoot[D[LargeREnergy[Rs,t,p, nl,A,Ku,Di,Ms,Bz],Rs]==0,{Rs,R1}];
If[Im[(Rmax)]!=0||Re[(Rmax)]<0,Return[0]];
If[Not[IsMaximimLargeR[Rmax,t,p,nl,A,Ku,Di,Ms,Bz]],Return[0]];
Return[Rmax];
];

LargeRThresholdR[t_,p_,nl_,A_,Ku_,Di_,Ms_]:=Max[10p nl,100 ("\[CapitalDelta]"/.DeltaPsiInf[t,p,nl,A,Ku,Di,Ms])];

(* Check that the given R at the provided material parameters and field value is really a minimum, which is characterized by a negative derivative D[E,R] for R slighly below the found value and a positive derivative slightly above the found value. For "slightly" we use 0.02 nm or 0.2%, whichever is greater. For some reason, the precision of FindRoot cannot be increased beyond this limit. *)
IsMinimumLargeR[R_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=Block[{Rp,Rm,Rs,checkp,checkm},
If[R<=0,Return[False]];
Rp=R+Max[0.02,2 10^-3 R];
Rm=R-Max[0.02,2 10^-3 R];
If[Rm<=0,Rm=2 10^-3 R];
(* Slightly above the minimum the energy must be larger. Check this. *)
checkp=(LargeREnergy[Rp,t,p,nl,A,Ku,Di,Ms,Bz]-LargeREnergy[R,t,p,nl,A,Ku,Di,Ms,Bz])>0;
(* Slightly below the minimum the energy must be larger. Check this. *)
checkm=(LargeREnergy[Rm,t,p,nl,A,Ku,Di,Ms,Bz]-LargeREnergy[R,t,p,nl,A,Ku,Di,Ms,Bz])>0;
(* Return if both checks were true. *)
Return[checkp && checkm];
];

IsMaximumLargeR[R_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=Block[{Rp,Rm,Rs,checkp,checkm},
If[R<=0,Return[False]];
Rp=R+Max[0.02,2 10^-3 R];
Rm=R-Max[0.02,2 10^-3 R];
If[Rm<=0,Rm=2 10^-3 R];
(* Slightly above the minimum the energy must be smaller. Check this. *)
checkp=(LargeREnergy[Rp,t,p,nl,A,Ku,Di,Ms,Bz]-LargeREnergy[R,t,p,nl,A,Ku,Di,Ms,Bz])<0;
(* Slightly below the minimum the energy must be smaller. Check this. *)
checkm=(LargeREnergy[Rm,t,p,nl,A,Ku,Di,Ms,Bz]-LargeREnergy[R,t,p,nl,A,Ku,Di,Ms,Bz])<0;
(* Return if both checks were true. *)
Return[checkp && checkm];
];

IsExtremumLargeR[R_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=Block[{},
(* Return if it's either a maximum or a minimum. *)
Return[IsMinimumLargeR[R,t,p,nl,A,Ku,Di,Ms,Bz] || IsMaximumLargeR[R,t,p,nl,A,Ku,Di,Ms,Bz]];
];


(* 
   **************************
    Small R energy minimization
   **************************
*)

PsiDi[R_,\[CapitalDelta]_,t_,p_,nl_,Di_,Ms_]:=Block[{f=t/p,d=p nl,psi},
psi=ArcCos[MinMaxHelper[((f Di ID[R/\[CapitalDelta]])/(4 \[Mu]0 (f Ms)^2 R Ivt[R/\[CapitalDelta],d/\[CapitalDelta]]))]];
Return[psi];
];


Delta[R_?NumericQ,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_,default_:Automatic]:=Delta[R,t,p,nl,A,Ku,Di,Ms,Bz]=Block[{\[CapitalDelta],\[CapitalDelta]0,\[CapitalDelta]1,\[CapitalDelta]2,\[CapitalDelta]max,\[CapitalDelta]s,counter=1,precision,result},
\[CapitalDelta]max=Min[R/ArcSinh[1],("\[CapitalDelta]"/.DeltaPsiInf[t,p,nl,A,Ku,Di,Ms])*1.05]; (* 1.05 to allow for some uncertainty in DeltaPsiInf *)
If[R>10^5,Return[\[CapitalDelta]max]];
(* Try to find the minimum using FindMinimum, which is very fast (typically, 0.026s) *)
\[CapitalDelta]s=\[CapitalDelta]/.Last[Quiet[FindMinimum[EtotalEM[R,\[CapitalDelta],t,p,nl,PsiDi[R,\[CapitalDelta],t,p,nl,Di,Ms],A,Ku,Di,Ms,Bz],{\[CapitalDelta],\[CapitalDelta]max/2}]]];
(* If we found the minimum already, return the result *)
If[IsMinimumDelta[R,\[CapitalDelta]s,t,p,nl,A,Ku,Di,Ms,Bz],Return[\[CapitalDelta]s]];
(* If \[CapitalDelta]s is roughly a minimum, try to manually increase the precision. If not, return default (or \[CapitalDelta]max). *)
precision=Min[1,0.95\[CapitalDelta]s];
If[Not[IsMinimumDelta[R,\[CapitalDelta]s,t,p,nl,A,Ku,Di,Ms,Bz,precision]],
If[default===Automatic,
debugPrintVerbose["Delta: Could not find minimum. Returning \[CapitalDelta]max."];
Return[\[CapitalDelta]max],
debugPrintVerbose["Delta: Could not find minimum. Returning default."];
Return[default]
]];
(* Find the smallest precision value at which \[CapitalDelta]s is still a minimum *)
While[IsMinimumDelta[R,\[CapitalDelta]s,t,p,nl,A,Ku,Di,Ms,Bz,precision],precision/=2];
Print[IsMinimumDelta[R,\[CapitalDelta]s,t,p,nl,A,Ku,Di,Ms,Bz,precision]];
precision*=2;
debugPrintVerbose["Delta: Minimum found but precision = ",precision," is too low. Resampling manually."];
\[CapitalDelta]1=\[CapitalDelta]s-precision;
\[CapitalDelta]2=\[CapitalDelta]s+precision;
While[\[CapitalDelta]2-\[CapitalDelta]1>0.01,
\[CapitalDelta]0=(\[CapitalDelta]1+\[CapitalDelta]2)/2;
(* If the E[(\[CapitalDelta]1+\[CapitalDelta]0)/2] > E[\[CapitalDelta]0], then for sure the minimum is not in [\[CapitalDelta]1,(\[CapitalDelta]1+\[CapitalDelta]0)/2]. Therefore, set \[CapitalDelta]1 as the new \[CapitalDelta]1. Same for \[CapitalDelta]2. *)
If[EtotalEM[R,(\[CapitalDelta]1+\[CapitalDelta]0)/2,t,p,nl,PsiDi[R,(\[CapitalDelta]1+\[CapitalDelta]0)/2,t,p,nl,Di,Ms],A,Ku,Di,Ms,Bz]>EtotalEM[R,\[CapitalDelta]0,t,p,nl,PsiDi[R,\[CapitalDelta]0,t,p,nl,Di,Ms],A,Ku,Di,Ms,Bz],\[CapitalDelta]1=(\[CapitalDelta]1+\[CapitalDelta]0)/2];
If[EtotalEM[R,(\[CapitalDelta]2+\[CapitalDelta]0)/2,t,p,nl,PsiDi[R,(\[CapitalDelta]2+\[CapitalDelta]0)/2,t,p,nl,Di,Ms],A,Ku,Di,Ms,Bz]>EtotalEM[R,\[CapitalDelta]0,t,p,nl,PsiDi[R,\[CapitalDelta]0,t,p,nl,Di,Ms],A,Ku,Di,Ms,Bz],\[CapitalDelta]2=(\[CapitalDelta]2+\[CapitalDelta]0)/2];
If[counter>20, 
debugPrint["Delta: Could not find exact minimum in 20 iterations. Call was:"];
debugPrint[ToExpression[ToString[StringForm["Delta[``,``,``,``,``,``,``,``,``]",
ToString[R,InputForm],ToString[t,InputForm],ToString[p,InputForm],ToString[nl,InputForm],ToString[A,InputForm],ToString[Ku,InputForm],ToString[Di,InputForm],ToString[Ms,InputForm],ToString[Bz,InputForm]]],
StandardForm,Hold]];
Return[0];
];];
\[CapitalDelta]s=\[CapitalDelta]0;
If[Not[IsMinimumDelta[R,\[CapitalDelta]s,t,p,nl,A,Ku,Di,Ms,Bz]],
If[default===Automatic,
debugPrintVerbose["Delta: Could not find minimum. Returning \[CapitalDelta]max."];
Return[\[CapitalDelta]max],
debugPrintVerbose["Delta: Could not find minimum. Returning default."];
Return[default]
]];
Return[\[CapitalDelta]s];
];

IsMinimumDelta[R_,\[CapitalDelta]_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_,precision_:0.02,accuracy_:2*^-3]:=Block[{\[CapitalDelta]p,\[CapitalDelta]m,checkp,checkm},
If[Im[\[CapitalDelta]]!=0 || Re[\[CapitalDelta]]<=0 || \[CapitalDelta]>R/ArcSinh[1],Return[False]];
\[CapitalDelta]p=\[CapitalDelta]+Max[precision,accuracy \[CapitalDelta]];
\[CapitalDelta]m=\[CapitalDelta]-Max[precision,accuracy \[CapitalDelta]];
If[\[CapitalDelta]m<=0,\[CapitalDelta]m=accuracy \[CapitalDelta]];
(* Slightly above the minimum the energy must be larger. Check this. *)
checkp=(EtotalEM[R,\[CapitalDelta]p,t,p,nl,PsiDi[R,\[CapitalDelta]p,t,p,nl,Di,Ms],A,Ku,Di,Ms,Bz]-EtotalEM[R,\[CapitalDelta],t,p,nl,PsiDi[R,\[CapitalDelta],t,p,nl,Di,Ms],A,Ku,Di,Ms,Bz])>0;
(* Slightly below the minimum the energy must be larger. Check this. *)
checkm=(EtotalEM[R,\[CapitalDelta]m,t,p,nl,PsiDi[R,\[CapitalDelta]m,t,p,nl,Di,Ms],A,Ku,Di,Ms,Bz]-EtotalEM[R,\[CapitalDelta],t,p,nl,PsiDi[R,\[CapitalDelta],t,p,nl,Di,Ms],A,Ku,Di,Ms,Bz])>0;
(* Return if both checks were true. *)
Return[checkp && checkm];
];

(* Obtain equilibrium parameters \[CapitalDelta] and \[Psi] for finite sized skyrmions with given radius. We cache the result for quickly returning the result if the function is called again with the same parameters. A replacement rule in the form {\[CapitalDelta]\[Rule]value,\[Psi]\[Rule]value} is returned. *)
DeltaPsi[R_?NumericQ,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=DeltaPsi[R,t,p,nl,A,Ku,Di,Ms,Bz]=Block[{\[CapitalDelta]s,\[Psi]s,result},
\[CapitalDelta]s=Delta[R,t,p,nl,A,Ku,Di,Ms,Bz];
\[Psi]s=PsiDi[R,\[CapitalDelta]s,t,p,nl,Di,Ms];
result={"\[CapitalDelta]"->\[CapitalDelta]s,"\[Psi]"->\[Psi]s};
Return[result];
];

(* Check that the given R at the provided material parameters and field value is really a minimum, which is characterized by a negative derivative D[E,R] for R slighly below the found value and a positive derivative slightly above the found value. For "slightly" we use 0.02 nm or 0.2%, whichever is greater. For some reason, the precision of FindRoot cannot be increased beyond this limit. *)
IsMinimum[R_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=Block[{Rp,Rm,Rs,checkp,checkm},
If[R<=0,Return[False]];
(*(* There is a small step discontinuity in E(R) at LargeRThresholdR. If we hit this
   point (or exceed it), use the LargeR version of IsMinimum instead. *)
If[R>=LargeRThresholdR[t,p,nl,A,Ku,Di,Ms],Return[IsMinimumLargeR[R,t,p,nl,A,Ku,Di,Ms,Bz]]];*)
(* If Delta is not a minimum then R is not, either *)
If[Not[IsMinimumDelta[R,Delta[R,t,p,nl,A,Ku,Di,Ms,Bz],t,p,nl,A,Ku,Di,Ms,Bz]],Return[False]];
Rp=R+Max[0.02,2 10^-3 R];
Rm=Max[2 10^-3 R,R-Max[0.02,2 10^-3 R]];
(* Slightly above the minimum the energy must be larger. Check this. *)
checkp=(EofR[Rp,t,p,nl,A,Ku,Di,Ms,Bz,False]-EofR[R,t,p,nl,A,Ku,Di,Ms,Bz,False])>0;
(* Slightly below the minimum the energy must be larger. Check this. *)
checkm=(EofR[Rm,t,p,nl,A,Ku,Di,Ms,Bz,False]-EofR[R,t,p,nl,A,Ku,Di,Ms,Bz,False])>0;
(* Return if both checks were true. *)
Return[checkp && checkm];
];

IsMaximum[R_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=Block[{Rp,Rm,Rs,checkp,checkm},
If[R<=0,Return[False]];
(* There is a small step discontinuity in E(R) at LargeRThresholdR. If we hit this
   point (or exceed it), use the LargeR version of IsMinimum instead. *)
(*If[R>=LargeRThresholdR[t,p,nl,A,Ku,Di,Ms],Return[IsMinimumLargeR[R,t,p,nl,A,Ku,Di,Ms,Bz]]];*)
Rp=R+Max[0.02,2 10^-3 R];
Rm=R-Max[0.02,2 10^-3 R];
If[Rm<=0,Rm=2 10^-3 R];
(* Slightly above the minimum the energy must be smaller. Check this. *)
checkp=(EofR[Rp,t,p,nl,A,Ku,Di,Ms,Bz,False]-EofR[R,t,p,nl,A,Ku,Di,Ms,Bz,False])<0;
(* Slightly below the minimum the energy must be smaller. Check this. *)
checkm=(EofR[Rm,t,p,nl,A,Ku,Di,Ms,Bz,False]-EofR[R,t,p,nl,A,Ku,Di,Ms,Bz,False])<0;
(* Return if both checks were true. *)
Return[checkp && checkm];
];

IsExtremum[R_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=Block[{},
(* Return if it's either a maximum or a minimum. *)
Return[IsMinimum[R,t,p,nl,A,Ku,Di,Ms,Bz] || IsMaximum[R,t,p,nl,A,Ku,Di,Ms,Bz]];
];

FindExtremumRadiusInIntervalByFindRoot[R0_,Rmin_,Rmax_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=Block[{R,Rs,\[CapitalDelta],\[CapitalDelta]s,\[CapitalDelta]0},
If[R0>10^5,debugPrint["RDeltaPsiGivenR0Delta0NoCheck: Warning: R0>1e5. Searching equilibrium radius might take a very long time."];];
\[CapitalDelta]0=Delta[R0,t,p,nl,A,Ku,Di,Ms,Bz];
{Rs,\[CapitalDelta]s}={R,\[CapitalDelta]}/.FindRoot[{
D[EtotalEM[R,\[CapitalDelta],t,p,nl,PsiDi[R,\[CapitalDelta],t,p,nl,Di,Ms],A,Ku,Di,Ms,Bz],R]+(R-Rmax)HeavisideTheta[R-Rmax]+(Rmin-R)*1000 HeavisideTheta[Rmin-R]==0,
D[EtotalEM[R,\[CapitalDelta],t,p,nl,PsiDi[R,\[CapitalDelta],t,p,nl,Di,Ms],A,Ku,Di,Ms,Bz],\[CapitalDelta]]==0
},{{R,R0},{\[CapitalDelta],\[CapitalDelta]0}},DampingFactor-> 1/2];
(* Check if the result is reasonable, i.e., a real valued radius larger than 0. If it's not return 0. *)
If[Im[(Rs)]!=0||Re[(Rs)]<0.01,
debugPrintVerbose["not real valued"];
Return[0];
];
Return[Rs];
];

FindCloseByExtremum[Rmin_,Rmax_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_,steps_:100]:=Block[{Rs=Rmin,tab},
tab=Table[{R1,IsExtremum[R1,t,p,nl,A,Ku,Di,Ms,Bz]},{R1,Subdivide[Rmin,Rmax,steps]}];
Print[tab];
If[Total[Boole[tab[[All,2]]]]>0,
Rs=Total[tab[[All,1]]*Boole[tab[[All,2]]]]/Total[Boole[tab[[All,2]]]];
];
If[Not[IsExtremum[Rs,t,p,nl,A,Ku,Di,Ms,Bz]],
debugPrintVerbose["FindCloseByExtremum: no extremum found"];
Return[0];
];
Return[Rs];
];

FindMinimumRadiusInInterval[R0_,Rmin_,Rmax_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=Block[{R,Rs},
If[R0>10^5,debugPrint["RDeltaPsiGivenR0Delta0NoCheck: Warning: R0>1e5. Searching equilibrium radius might take a very long time."];];
(* FindMinimum is slow. First try it differently: *)
Rs=FindExtremumRadiusInIntervalByFindRoot[R0,Rmin,Rmax,t,p,nl,A,Ku,Di,Ms,Bz];
(*Print[{Rs,EofR[Rs,t,p,nl,A,Ku,Di,Ms,Bz],IsMinimum[Rs,t,p,nl,A,Ku,Di,Ms,Bz]}];*)
(* Only if that didn't work, use FindMinimum *)
If[Not[IsMinimum[Rs,t,p,nl,A,Ku,Di,Ms,Bz]],
Rs=R/.Last[FindMinimum[EofR[R,t,p,nl,A,Ku,Di,Ms,Bz,False]+1000 HeavisideTheta[R-Rmax]+1000 HeavisideTheta[Rmin-R],{R,R0}]]
];
(* Check if the result is reasonable, i.e., a real valued radius larger than 0. If it's not return 0. *)
If[Im[(Rs)]!=0||Re[(Rs)]<0.01,
debugPrintVerbose["not a minimum: R = ",Rs];
Return[{"R"->0,"\[CapitalDelta]"->0,"\[Psi]"->0}];
];
If[Not[IsMinimum[Rs,t,p,nl,A,Ku,Di,Ms,Bz]],
Rs=FindCloseByExtremum[Rs-.5,Rs+.5,t,p,nl,A,Ku,Di,Ms,Bz];
Print[Rs];
];
If[Not[IsMinimum[Rs,t,p,nl,A,Ku,Di,Ms,Bz]],
debugPrintVerbose["not a minimum: R = ",Rs];
Return[{"R"->0,"\[CapitalDelta]"->0,"\[Psi]"->0}];
];
Return[Prepend[DeltaPsi[Rs,t,p,nl,A,Ku,Di,Ms,Bz],"R"->Rs]];
];

FindMaximumRadiusInInterval[R0_,Rmin_,Rmax_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=Block[{R,Rs},
If[R0>10^5,debugPrint["RDeltaPsiGivenR0Delta0NoCheck: Warning: R0>1e5. Searching equilibrium radius might take a very long time."];];
(* FindMaximum is slow. First try it differently: *)
Rs=FindExtremumRadiusInIntervalByFindRoot[R0,Rmin,Rmax,t,p,nl,A,Ku,Di,Ms,Bz];
(*Print[{Rs,EofR[Rs,t,p,nl,A,Ku,Di,Ms,Bz],IsMaximum[Rs,t,p,nl,A,Ku,Di,Ms,Bz]}];*)
(* Only if that didn't work, use FindMaximum *)
If[Not[IsMaximum[Rs,t,p,nl,A,Ku,Di,Ms,Bz]],
Rs=R/.Last[FindMaximum[EofR[R,t,p,nl,A,Ku,Di,Ms,Bz,False]+1000 HeavisideTheta[R-Rmax]+1000 HeavisideTheta[Rmin-R],{R,R0}]]
];
(* Check if the result is reasonable, i.e., a real valued radius larger than 0. If it's not return 0. *)
If[Im[(Rs)]!=0||Re[(Rs)]<0.01,
debugPrintVerbose["not a maximum: R = ",Rs];
Return[{"R"->0,"\[CapitalDelta]"->0,"\[Psi]"->0}];
];
If[Not[IsMaximum[Rs,t,p,nl,A,Ku,Di,Ms,Bz]],
Rs=FindCloseByExtremum[Rs-.5,Rs+.5,t,p,nl,A,Ku,Di,Ms,Bz];
];
If[Not[IsMaximum[Rs,t,p,nl,A,Ku,Di,Ms,Bz]],
debugPrintVerbose["not a maximum: R = ",Rs];
Return[{"R"->0,"\[CapitalDelta]"->0,"\[Psi]"->0}];
];
Return[Prepend[DeltaPsi[Rs,t,p,nl,A,Ku,Di,Ms,Bz],"R"->Rs]];
];

RDeltaPsiGivenR0Delta0RmaxCheckExtremum[R0_,\[CapitalDelta]0_,Rmax_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=(*RDeltaPsiGivenR0Delta0CheckExtremum[R0,\[CapitalDelta]0,t,p,nl,A,Ku,Di,Ms,Bz]=*)Block[{R,R1,Rs,\[CapitalDelta],\[CapitalDelta]s,\[Psi],\[Psi]s,result,tab,stepsize},
result=RDeltaPsiGivenR0Delta0RmaxNoCheck[R0,\[CapitalDelta]0,Rmax,t,p,nl,A,Ku,Di,Ms,Bz];
R="R"/.result;
If[R==0,Return[result];];
If[R<FindRc[t,p,nl,A,Ku,Di,Ms,Bz],
debugPrintVerbose["RDeltaPsiGivenR0Delta0RmaxCheckExtremum: R<Rc"];
Return[{"R"->0,"\[CapitalDelta]"->0,"\[Psi]"->0,"Rs"->R}];
];
If[Not[IsExtremum[R,t,p,nl,A,Ku,Di,Ms,Bz]],
stepsize=Max[0.02,2 10^-3 R];
tab=Table[{R1,IsExtremum[R1,t,p,nl,A,Ku,Di,Ms,Bz]},{R1,R-10 stepsize,R+10 stepsize,stepsize}];
If[Total[Boole[tab[[All,2]]]]>0,
Rs=Total[tab[[All,1]]*Boole[tab[[All,2]]]]/Total[Boole[tab[[All,2]]]];
\[CapitalDelta]s=Delta[Rs,t,p,nl,A,Ku,Di,Ms,Bz];
\[Psi]s=PsiDi[Rs,\[CapitalDelta]s,t,p,nl,Di,Ms];
result={"R"->Rs,"\[CapitalDelta]"->\[CapitalDelta]s,"\[Psi]"->\[Psi]s};
];
];
R="R"/.result;
\[CapitalDelta]="\[CapitalDelta]"/.result;
\[Psi]="\[Psi]"/.result;
(*If[Not[IsExtremum[R,t,p,nl,A,Ku,Di,Ms,Bz]] && ((EtotalEM[R,\[CapitalDelta],t,p,nl,\[Psi],A,Ku,Di,Ms,Bz])>E0),*)
If[Not[IsExtremum[R,t,p,nl,A,Ku,Di,Ms,Bz]],
debugPrintVerbose["RDeltaPsiGivenR0Delta0RmaxCheckExtremum: not extremum, E=",EtotalEM[R,\[CapitalDelta],t,p,nl,\[Psi],A,Ku,Di,Ms,Bz]," ",result];
Return[{"R"->0,"\[CapitalDelta]"->0,"\[Psi]"->0,"Rs"->R}];
];
Return[result];
];


(* Find all extrema using a logarithmic sampling of E(R) in the range [Rc,LargeRThresholdR]. Is is guaranteed that there is always a maximum between two minima. *)
FindAllExtrema[t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_,Rmax_:Infinity]:=Block[{data,start,stop,mins,maxs,largeRmin,largeRmax,addLargeRMinimum=False,addLargeRMaximum=False,thr,sampling},
(* Logarithmic sampling with 10 steps in every multiplication by e is sufficient to guarantee that there are at least two points between two 
   adjacent extrema. Therefore, 'data' captures all minima and maxima. *)
start=Log[FindRc[t,p,nl,A,Ku,Di,Ms,Bz]];
stop=Log[Min[Rmax,LargeRThresholdR[t,p,nl,A,Ku,Di,Ms]]]+0.21; (* add 0.1 to make sure that a minimum at the nominal stop point is recognized as such (is not at the boundary of the search interval) *)
(* Manually sampling the energy landscape. If we encounter any points were we can't find the minimum, use a finer sampling.
   After three iterations, stop the loop and remove all R=0 points from the mins and maxs list. *)
For[sampling=1/10,sampling>1/100,sampling/=3,
(* Make sure that we find minima even if they are extremely close to Rc. Hence, add Rc+1e-8 to the list. *)
data=Table[{Exp[lnR],EofR[Exp[lnR],t,p,nl,A,Ku,Di,Ms,Bz,False]},{lnR,Insert[Range[start,stop,sampling],start+10^-8,2]}];
(* Find the minima and maxima and their immediate (larger) neighbors in data. Generate two lists, mins and maxs, where each element in mins
   is a list of two radii, the nominal minimum and the next larger value (analogously for maxs). *)
Module[{pickMins,pickMinsSmallerNeighbors,pickMinsLargerNeighbors,pickMaxs,pickMaxsSmallerNeighbors,pickMaxsLargerNeighbors},
pickMins=MinDetect[data[[All,2]],Padding->"Fixed"];
pickMinsSmallerNeighbors=RotateLeft[pickMins,1];
pickMinsLargerNeighbors=RotateRight[pickMins,1];
mins=Transpose[{Pick[data,pickMins,1][[All,1]],Pick[data,pickMinsSmallerNeighbors,1][[All,1]],Pick[data,pickMinsLargerNeighbors,1][[All,1]]}];
pickMaxs=MaxDetect[data[[All,2]],Padding->"Fixed"];
pickMaxsSmallerNeighbors=RotateLeft[pickMaxs,1];
pickMaxsLargerNeighbors=RotateRight[pickMaxs,1];
maxs=Transpose[{Pick[data,pickMaxs,1][[All,1]],Pick[data,pickMaxsSmallerNeighbors,1][[All,1]],Pick[data,pickMaxsLargerNeighbors,1][[All,1]]}];
];
debugPrintVerbose["FindAllExtrema: Evaluated table for R in [",Exp[start],",",Exp[stop],"]. Got: ",{"mins"->mins,"maxs"->maxs}];
(* Refine the minima and maxima by searching for the exact positions *)
mins = FindMinimumRadiusInInterval[#[[1]],#[[2]],#[[3]],t,p,nl,A,Ku,Di,Ms,Bz]&/@mins;
maxs = FindMaximumRadiusInInterval[#[[1]],#[[2]],#[[3]],t,p,nl,A,Ku,Di,Ms,Bz]&/@maxs;
(* In case the search failed, we need to get more sampling points around the extremum. *)
If[(Length[mins]==0 || Min["R"/.mins]>0) && (Length[maxs]==0 || Min["R"/.maxs]>0),sampling=0];
];
(* If we still have zeros in the mins or maxs lists, return 0. This will probably cause an error in the calling function
and will indicate that some debugging is required. *)
If[(Length[mins]>0 && Min["R"/.mins]==0) || (Length[maxs]>0 && Min["R"/.maxs]==0),Return[0]];
debugPrintVerbose["FindAllExtrema: Refined mins and maxs to ",{"mins"->mins,"maxs"->maxs}];
(* Add the energy at the found minima and maxima to the result *)
mins = Append[#,"energy"->EofR["R"/.#,t,p,nl,A,Ku,Di,Ms,Bz]]&/@mins;
maxs = Append[#,"energy"->EofR["R"/.#,t,p,nl,A,Ku,Di,Ms,Bz]]&/@maxs;
(* Also add the field values to have complete results set *)
mins = Map[Join[{"Bz"->Bz},#]&,mins,{1}];
maxs = Map[Join[{"Bz"->Bz},#]&,maxs,{1}];
(* Finally, append the largeR minima and maxima, if they exist and if they are not already found. To make sure that we don't add
   some minima twice, we distinguish the following situations: 
   1. no mins, no maxs
   2. >0 min, no maxs
   3. no mins, >0 maxs
   4. >0 mins & maxs, Max[mins] > Max[maxs]
   5. >0 mins & maxs, Max[mins] < Max[maxs]
   
   These cases are handled as follows:
   1. if largeRmin > threshold \[Rule] add
      if largeRmax > threshold \[Rule] add both
   2. if largeRmax > Max[threshold,Max[mins]] \[Rule] add both
   3. if largeRmin > Max[threshold,Max[maxs]] \[Rule] add both
   4. same as 2.
   5. same as 3.
   *)
thr=LargeRThresholdR[t,p,nl,A,Ku,Di,Ms];
(* Special case: Bz=0, where no largeR minimum exists *)
If[Bz==0,
largeRmin=Infinity;
largeRmax=LargeRMaximum[Infinity,t,p,nl,A,Ku,Di,Ms,Bz];
If[largeRmax>thr && (Length[maxs]==0 || (Length[mins]>0 && Max["R"/.mins] > Max["R"/.maxs])),
addLargeRMaximum=True];
,
(* else: Bz < 0 *)
largeRmin=LargeRMinimum[t,p,nl,A,Ku,Di,Ms,Bz];
debugPrintVerbose["FindAllExtrema: ",{"threshold"->thr,"largeRmin"->largeRmin}];
If[largeRmin > thr,
largeRmax=LargeRMaximum[largeRmin,t,p,nl,A,Ku,Di,Ms,Bz];
debugPrintVerbose["FindAllExtrema: largeRmax = ",largeRmax];
(* case 1 *)
If[Length[maxs]==0 && Length[mins]==0,
debugPrintVerbose["FindAllExtrema: case 1"];
addLargeRMinimum=True;
If[largeRmax>thr,addLargeRMaximum=True]];
(* case 2 or 4 *)
If[(Length[mins]>0 && Length[maxs]==0) || (Length[mins]>0 && Length[maxs]>0 && Max["R"/.mins] > Max["R"/.maxs]),
debugPrintVerbose["FindAllExtrema: case 2/4"];
If[largeRmax > Max[thr,Max["R"/.mins]],addLargeRMinimum=True;addLargeRMaximum=True]];
(* case 3 or 5 *)
If[(Length[mins]==0 && Length[maxs]>0) || (Length[mins]>0 && Length[maxs]>0 && Max["R"/.mins] < Max["R"/.maxs]),
debugPrintVerbose["FindAllExtrema: case 3/5"];
If[largeRmin > Max[thr,Max["R"/.maxs]],addLargeRMinimum=True]];
]; (* end if largeRmin > thr *)
]; (* end if Bz\[Equal]0 *)
If[addLargeRMinimum,
mins = Append[mins,Join[{"Bz"->Bz,"R"->largeRmin},DeltaPsiInf[t,p,nl,A,Ku,Di,Ms],{"energy"->LargeREnergy[largeRmin,t,p,nl,A,Ku,Di,Ms,Bz]}]]];
If[addLargeRMaximum,
maxs = Append[maxs,Join[{"Bz"->Bz,"R"->largeRmax},DeltaPsiInf[t,p,nl,A,Ku,Di,Ms],{"energy"->LargeREnergy[largeRmax,t,p,nl,A,Ku,Di,Ms,Bz]}]]];
If[Not[addLargeRMinimum],debugPrintVerbose["FindAllExtrema: Determined largeR minimum = ",largeRmin," but not adding it."]];
If[addLargeRMinimum&&Not[addLargeRMaximum],debugPrintVerbose["FindAllExtrema: Determined and added largeR minimum = ",largeRmin," but not adding largeR maximum = ",largeRmax]];
If[addLargeRMinimum&&addLargeRMaximum,debugPrintVerbose["FindAllExtrema: Determined and added largeR minimum = ",largeRmin," and largeR maximum = ",largeRmax]];
debugPrintVerbose["FindAllExtrema: final result: ",{"mins"->mins,"maxs"->maxs}];
Return[{"mins"->mins,"maxs"->maxs}];
];
(* This function determines the forward and reverse energy barriers for all minima in extrema *)
DetermineEnergyBarriers[extrema_]:=Block[{mins=("mins"/.extrema),maxs=("maxs"/.extrema),Bz,result,Eb,Ebreverse,Ebannihilation},
(* Extract the field value *)
Bz=Min["Bz"/.mins];
(* If the smallest R extremum is a minimum then the maximum for that minimum is (0,E0). Add that information. *)
If[Length[maxs]==0,maxs={{"Bz"->Bz,"R"->0,"\[CapitalDelta]"->0,"\[Psi]"->0,"energy"->E0}}];
If[Min["R"/.maxs]>Min["R"/.mins],maxs=Join[{{"Bz"->Bz,"R"->0,"\[CapitalDelta]"->0,"\[Psi]"->0,"energy"->E0}},maxs]];
(* Add [Infinity,Infinity] to the list of maxima *)
maxs=Append[maxs,{"Bz"->Bz,"R"->Infinity,"\[CapitalDelta]"->0,"\[Psi]"->0,"energy"->Infinity}];
(* Determine the energy difference of each minimum to its smaller and larger R adjacent maximum *)
result=Table[
Eb=("energy"/.maxs)[[i]]-("energy"/.mins)[[i]];
Ebreverse=("energy"/.maxs)[[i+1]]-("energy"/.mins)[[i]];
(* The annihilation barrier is the maximum energy barrier between a given minimum and the state at R=0 *)
Ebannihilation=Max[("energy"/.maxs)[[1;;i]]]-("energy"/.mins)[[i]];
Join[mins[[i]],{"Eb"->Eb,"Ebreverse"->Ebreverse,"Ebannihilation"->Ebannihilation}],
{i,1,Length[mins]}];
Return[result];
];

(* A (meta-) stable minimum is defined as a minimum that has an energy that is at most kT larger than the energy
   of all other minima that are accessible without passing an energy barrier of more than Ebmin. *)
IsStableOrMetastableMinimum[minimumOrminimumIndex_,allMinima_,Ebmin_,kT_]:=Block[{minimumIndex,min1,min2,energy,localIndex,localAllMinima,continue},
If[Head[minimumOrminimumIndex]===Integer,minimumIndex=allMinima[[minimumOrminimumIndex]],minimumIndex=minimumOrminimumIndex];
(* Make sure the data is sorted ascendingly by radius *)
localAllMinima=Sort[allMinima,("R"/.#2)>("R"/.#1)&];
(* Convert the minimumIndex to an actual index (a number) *)
minimumIndex=First[First[Position[localAllMinima,minimumIndex]]];
debugPrintVerbose["IsStableOrMetastableMinimum: minimumIndex = ",minimumIndex," min = ",min1=localAllMinima[[minimumIndex]]];
If[minimumIndex<0 || minimumIndex>Length[localAllMinima],
debugPrint["IsStableOrMetastableMinimum: minimumIndex out of bounds."];
Return[False]];
If[("Ebannihilation"/.localAllMinima[[minimumIndex]])-kT<Ebmin,
debugPrintVerbose["IsStableOrMetastableMinimum: annihilation barrier is < Ebmin. Not stable."];
Return[False]];
(* Forward search *)
continue=True;
localIndex=minimumIndex;
While[localIndex>1 && continue,
min1=localAllMinima[[localIndex]];
min2=localAllMinima[[localIndex-1]];
debugPrintVerbose["IsStableOrMetastableMinimum: forward search: looking at min1 = ",min1," and min2 = ",min2];
(* If the annihilation barrier is < Ebmin then the skyrmion is not stable *)
If[("Ebannihilation"/.min1)-kT<Ebmin,
debugPrintVerbose["IsStableOrMetastableMinimum: forward search: min1 annihilation barrier is < Ebmin. Not stable."];
Return[False]];
(* If the energy barrier is smaller than Ebmin and the energy step is less than kT up, the next minimum can be reached. *)
If[("Eb"/.min1)-kT<Ebmin && ("energy"/.min2)-("energy"/.min1) < kT,
(* If the annihilation barrier of min2 is < Ebmin then min1 is not stable since min2 can be reached *)
If[("Ebannihilation"/.min2)-kT<Ebmin,
debugPrintVerbose["IsStableOrMetastableMinimum: forward search: lower energy minimum min2 can be reached by thermal excitation and that minimum can annihilate. Not stable."];
Return[False]];
(* If the reverse energy barrier is < Ebmin and the reverse energy step is less than kT up, then the process can be reversed.
   Otherwise, the original minimum is unstable because it can transform to a different state but not back. *)
If[Not[("Ebreverse"/.min2)-kT<Ebmin && ("energy"/.min1)-("energy"/.min2) < kT],
debugPrintVerbose["IsStableOrMetastableMinimum: forward search: lower energy minimum min2 can be reached by thermal excitation, but the reverse process is not possible. Not stable."];
Return[False]];
(* If the first if-condition is true, continue with the next smaller minimum index. Otherwise, stop the loop. *)
localIndex-=1,continue=False];
];
debugPrintVerbose["IsStableOrMetastableMinimum: Stable according to forward search."];
(* Backward search *)
continue=True;
localIndex=minimumIndex;
While[localIndex<Length[localAllMinima] && continue,
min1=localAllMinima[[localIndex]];
min2=localAllMinima[[localIndex+1]];
debugPrintVerbose["IsStableOrMetastableMinimum: backward search: looking at min1 = ",min1," and min2 = ",min2];
(* If the annihilation barrier is < Ebmin then the skyrmion is not stable *)
If[("Ebannihilation"/.min1)-kT<Ebmin,
debugPrintVerbose["IsStableOrMetastableMinimum: backward search: min1 annihilation barrier is < Ebmin. Not stable."];
Return[False]];
(* If the reverse energy barrier is smaller than Ebmin and the energy step is less than kT up, the next minimum can be reached. *)
If[("Ebreverse"/.min1)-kT<Ebmin && ("energy"/.min2)-("energy"/.min1) < kT,
(* If the annihilation barrier of min2 is < Ebmin then min1 is not stable since min2 can be reached *)
If[("Ebannihilation"/.min2)-kT<Ebmin,
debugPrintVerbose["IsStableOrMetastableMinimum: backward search: lower energy minimum min2 can be reached by thermal excitation and that minimum can annihilate. Not stable."];
Return[False]];
(* If the (forward) energy barrier is < Ebmin and the energy step is less than kT up, then the process can be reversed.
   Otherwise, the original minimum is unstable because it can transform to a different state but not back. *)
If[Not[("Eb"/.min2)-kT<Ebmin && ("energy"/.min1)-("energy"/.min2) < kT],
debugPrintVerbose["IsStableOrMetastableMinimum: backward search: lower energy minimum min2 can be reached by thermal excitation, but the reverse process is not possible. Not stable."];
Return[False]];
(* If the first if-condition is true, continue with the next larger minimum index. Otherwise, stop the loop. *)
localIndex+=1,continue=False];
];
debugPrintVerbose["IsStableOrMetastableMinimum: Stable according to backward search."];
Return[True];
];

(* A (meta-) stable minimum is defined as a minimum that has an energy that is at most kT larger than the energy
   of all other minima that are accessible without passing an energy barrier of more than Ebmin. *)
SelectStableAndMetastableMinima[minima_,Ebmin_,kT_]:=Select[minima,IsStableOrMetastableMinimum[#,minima,Ebmin,kT]&];

(* This function classifies minima, assuming that the provided minima are sorted by descending field (ascending in magnitude) *)
ClassifyMinima[minimaList_,Ebmin_,kT_]:=Block[{result,minima,i,j,k,count,type,block,cdata,maxcount,fit,candidates,index},
If[Length[minimaList]==0,Return[minimaList]];
(* For classification we want to have the largest R minimum first. Therefore, reverse the existing structure. *)
minima=Sort[minimaList[[1]],("R"/.#2)<("R"/.#1)&];
(* Strip any existing count, type, or block entries *)
minima=DeleteCases[#,("count"->_)|("type"->_)|("block"->_)]&/@minima;
(* Assign counts to each minimum *)
minima=Table[Join[{"count"->k,"type"->0,"block"->0},minima[[k]]],{k,1,Length[minima]}];
(* Determine the block of the minima of the first field step. *)
block=0;
For[j=1,j<=Length[minima],j++,
block++;
minima[[j]]=minima[[j]]/.("block"->0)->("block"->block);
(* If the energy barrier is smaller than Ebmin and the energy step is less than kT up, the next minimum can be reached. *)
While[j<Length[minima] && ("Eb"/.minima[[j]])-kT<Ebmin && ("energy"/.minima[[j+1]])-("energy"/.minima[[j]]) < kT,
j++;
minima[[j]]=minima[[j]]/.("block"->0)->("block"->block);];
];
result={minima};
maxcount=Length[minima];
(* Now proceed with the subsequent field steps. *)
For[i=2,i<=Length[minimaList],i++,
(* For classification we want to have the largest R minimum first. Therefore, reverse the existing structure. *)
minima=Sort[minimaList[[i]],("R"/.#2)<("R"/.#1)&];
(* Strip any existing count, type, or block entries *)
minima=DeleteCases[#,("count"->_)|("type"->_)|("block"->_)]&/@minima;
(* Assign counts\[Rule]0 per default as an indicator for unassigned *)
minima=Table[Join[{"count"->0,"type"->0,"block"->0},minima[[k]]],{k,1,Length[minima]}];
(* For each item of the last step check if any element (minimum) in minima can be of the same count. If there are more than 1 candidates,
   choose the one with the largest R.
 We start with the smallest R of the previous step. *)
For[j=Length[result[[-1]]],j>0,j--,
(* First try to fit the existing data and assign the min to the types that fit best. *)
count="count"/.result[[-1,j]];
(* Find all data for this count and try to get a fit. *)
(* Syntax of this command: For all elements in result select those sub-elements where counter\[Equal]c. Here, element is a list of minima
 corresponding to a given field value. The result will be a list of sub-elements (where a sub-element is a minimum),
   but we know that there is only one sub-element in this list because counter is unique within each element. Therefore, we 
  flatten the result. Now we have a list of minima, but we still might have empty lists where no minimum fullfilled counter\[Equal]c.
 Thus, in a final step, we select only those items with at least one minimum.
*)
cdata=Select[Flatten/@(With[{element=#},Select[element,("count"/.#)==count&]]&/@result),Length[#]>0&];
(* If we have at least 3 minima in cdata we can do a fit. Otherwise, we assign the largest R that is not yet assigned
and that is < all R in cdata. *)
If[Length[cdata]>2,
fit=FitRBzData[cdata];
candidates=Position[minima,_?(("count"/.#)==0&&("R"/.#)<=Min["R"/.cdata]&&("R"/.#)>0.7fit["Bz"/.#]&&("R"/.#)>0.7Min["R"/.cdata]&),{1},Heads->False];,
candidates=Position[minima,_?(("count"/.#)==0&&("R"/.#)<=Min["R"/.cdata]&),{1},Heads->False]];
If[Length[candidates]>0,
index=First[Flatten[Select[candidates,("R"/.Extract[minima,#])==Max["R"/.Extract[minima,candidates]]&]]];
minima[[index]]=minima[[index]]/.("count"->_)->("count"->count);];
];
(* Assign new counts to all remaining (unassigned) minima *)
candidates=Flatten[Position[minima,_?(("count"/.#)==0&),{1},Heads->False]];
For[k=1,k<=Length[candidates],k++,
index=candidates[[k]];
maxcount++;
minima[[index]]=minima[[index]]/.("count"->0)->("count"->maxcount);
];
(* Now determine the block of each minimum. *)
block=0;
For[j=1,j<=Length[minima],j++,
block++;
minima[[j]]=minima[[j]]/.("block"->0)->("block"->block);
(* If the energy barrier is smaller than Ebmin and the energy step is less than kT up, the next minimum can be reached. *)
While[j<Length[minima] && ("Eb"/.minima[[j]])-kT<Ebmin && ("energy"/.minima[[j+1]])-("energy"/.minima[[j]]) < kT,
j++;
minima[[j]]=minima[[j]]/.("block"->0)->("block"->block);];
];
result=Append[result,minima];
];
(* Now we have assigned the count and block properties to each minimum. Let's continue with type. *)
(* type is 1 if the data can be fit with a parameter c>0, 2 if c\[LessEqual]0, and 3 if there is not enough data for a fit. *)
For[i=1,i<=maxcount,i++,
(* Select all minima of count i, syntax as explained before *)
cdata=Select[Flatten/@(With[{element=#},Select[element,("count"/.#)==i&]]&/@result),Length[#]>0&];
(* Fit the data *)
If[Length[cdata]>2,
fit=FitRBzData[cdata];
If[Last[fit["BestFitParameters"]/.(_->x_)->x]>0,type=1,type=2];,
(* If cdata is not long enough, type is 3. *)
type=3];
(* Now change the type value in all selected elements *)
result=result/.({"count"->i,"type"->0,x___}->{"count"->i,"type"->type,x});
];
Return[result];
];

CollapseRadiusMinimumEnergyBarrierVerbose3[t_,p_,nl_,A_,Ku_,Di_,Ms_,Ebmin_,temperature_,Bzmin_:0,kTfactor_:1]:=Block[
{kT,extrema,extremaList,minima,minimaList,stableMinima,stableMinimaList,factor,counter,Bz,Bz0,R0,Rmax,collapseFieldExceeded=False,tstart,result},
(* 
   Start with a radius that is a valid minimum in the large R approximation.
   Minimum: R>LargeRSmallestPossibleEquilibrium[t,p,nl,A,Ku,Di,Ms] (let's say R>1.5LargeRSmallestPossibleEquilibrium[t,p,nl,A,Ku,Di,Ms] to make the minimum easy to find)
   Valid: R>Max[10p nl,100 ("\[CapitalDelta]"/.DeltaPsiInf[t,p,nl,A,Ku,Di,Ms])] \[Rule] otherwise, the large R approximation is not justified
*)
tstart=TimeUsed[];
kT=1.38064852*^-23*temperature; (* thermal energy = kT *)
kT/=A t nl; (* normalize to the same units as all the other energies, i.e., to A d *)
debugPrint["CollapseRadiusMinimumEnergyBarrierVerbose3: Temperature T = ",temperature,"K corresponds to kT = ",kT," Ad"];
kT*=kTfactor;
debugPrint["CollapseRadiusMinimumEnergyBarrierVerbose3: ",kTfactor,"kT = ",kT," Ad"];
If[Bzmin<0,
Bz0=Bzmin,
R0=Max[1.5LargeRSmallestPossibleEquilibrium[t,p,nl,A,Ku,Di,Ms],LargeRThresholdR[t,p,nl,A,Ku,Di,Ms]];
Bz0=LargeRBz[R0,t,p,nl,A,Ku,Di,Ms];
While[Bz0>0,
R0*=2;
Bz0=LargeRBz[R0,t,p,nl,A,Ku,Di,Ms];
];
Bz0/=1.5; (* factor 1.5 ensures that we have at least 3 data points with large 3, i.e., enough to get a fit. *)
];
Bz=Bz0;
extrema=FindAllExtrema[t,p,nl,A,Ku,Di,Ms,Bz];
extremaList={extrema};
minima=DetermineEnergyBarriers[extrema];
minimaList={minima};
stableMinima=SelectStableAndMetastableMinima[minima,Ebmin,kT];
stableMinimaList={stableMinima};
debugPrint["CollapseRadiusMinimumEnergyBarrierVerbose3: stable minima: ",stableMinima];
counter=0;
factor=0.05;
While[counter<300,
counter+=1;
Bz*=(1+factor);
Rmax=Max["R"/.("mins"/.extremaList[[-1]])];
debugPrint["CollapseRadiusMinimumEnergyBarrierVerbose3: Starting iteration ",counter," after a total computation time of ",TimeUsed[]-tstart," with Bz = ",Bz,". factor = ",factor,", Rmax = ",Rmax];
extrema=FindAllExtrema[t,p,nl,A,Ku,Di,Ms,Bz,Rmax];
minima=DetermineEnergyBarriers[extrema];
stableMinima=SelectStableAndMetastableMinima[minima,Ebmin,kT];
debugPrint["CollapseRadiusMinimumEnergyBarrierVerbose3: ",{"stableMinima"->stableMinima}];
If[Length[stableMinima]>0,
(* Do not append duplicates *)
extremaList=Append[extremaList,extrema];
minimaList=Append[minimaList,minima];
stableMinimaList=Append[stableMinimaList,stableMinima];
(* If Req < 2 it is very unlikely that we find another type of minimum. Therefore, we can increase the step size. *)
If[Max["R"/.stableMinimaList[[-1]]]<2 && Max["R"/.stableMinimaList[[-2]]] > 2,factor = 1;];

(* Else, make sure to do one more iteration above the collapse field to make sure that there is no other minimum at smaller R. 
If there is indeed no other minimum then we want to return to the same Bz as now in the following iteration, i.e., in the
iteration following the collapse iteration. The field will Bz*(factor+1) in the next iteration and Bz*(factor/4+1) in the one
following that. If we want Bz*(factor/4+1) to be equal to the current Bz, we have to reduce the current Bz by 1/(factor/4+1) *)
,
(* else: no stable minima found \[Rule] reduce field *)
Bz/=(1+factor);
factor/=4;
collapseFieldExceeded=True;
];
(* Evaluate the result and check if we are done. *)
If[
(* Case 1 *)
(Abs[1-Max["Ebannihilation"/.stableMinima]/(Ebmin+kT)]<=0.01) ||
(* Case 2 *)
(Min["R"/.stableMinimaList[[-1]]]>LargeRThresholdR[t,p,nl,A,Ku,Di,Ms] && 
 Min["Ebannihilation"/"energy"/.stableMinimaList[[-1]]]<10^-8 ) ||
(* Case 3 *)
(Abs[Max["R"/.stableMinimaList[[-1]]]-Max["R"/.stableMinimaList[[-2]]]]<0.01),
If[collapseFieldExceeded,
minimaList=ClassifyMinima[minimaList,Ebmin,kT];
stableMinimaList=Map[SelectStableAndMetastableMinima[#,Ebmin,kT]&,minimaList,{1}];
result={"extrema"->extremaList,"minima"->minimaList,"stableMinima"->stableMinimaList};
Block[{underSampledTransitions},
underSampledTransitions=FindUnderSampledTransitions["count"/.("stableMinima"/.result)];
(* Apply ResampleTransition to result with the indices in underSampledTransitions in reverse order to avoid changing the indices of the yet-to-be
   processed elements / transitions *)
(result=ResampleTransition[result,t,p,nl,A,Ku,Di,Ms,Ebmin,temperature*kTfactor,#];&)/@Reverse[underSampledTransitions];
];
result=ResampleTransition[result,t,p,nl,A,Ku,Di,Ms,Ebmin,temperature*kTfactor,Length["stableMinima"/.result]];
result=addHowStabilized[result,t,p,nl,A,Ku,Di,Ms];
Return[Join[result,{"computationTime"->TimeUsed[]-tstart,"success"->True}]];
]]];
debugPrint["CollapseRadiusMinimumEnergyBarrierVerbose: Could not find solution in 300 iterations. Call was:"];
debugPrint[ToExpression[ToString[StringForm["CollapseRadiusMinimumEnergyBarrierVerbose[``,``,``,``,``,``,``,``,``,``,``]",
ToString[t,InputForm],ToString[p,InputForm],ToString[nl,InputForm],ToString[A,InputForm],ToString[Ku,InputForm],ToString[Di,InputForm],ToString[Ms,InputForm],ToString[Ebmin,InputForm],ToString[temperature,InputForm],ToString[Bzmin,InputForm],ToString[kTfactor,InputForm]]],
StandardForm,Hold]];
Return[{"extrema"->extremaList,"minima"->minimaList,"stableMinima"->stableMinima,"computationTime"->TimeUsed[]-tstart,"success"->False}];
];

ReRunCollapseRadiusMinimumEnergyBarrierVerbose3[oldData_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Ebmin_,temperature_,kTfactor_:1]:=Block[
{kT,extrema,extremaList,minima,minimaList,stableMinima,stableMinimaList,factor,counter,Bz,Bz0,R0,Rmax,collapseFieldExceeded=False,tstart,result,done=False},
(* ************************
   oldData should be the result of a CollapseRadiusMinimumEnergyBarrierVerbose3 function call. 
   This function is intended to re-run the calculation with a different energy barrier or temperature. 
************************* *)
tstart=TimeUsed[];
kT=1.38064852*^-23*temperature; (* thermal energy = kT *)
kT/=A t nl; (* normalize to the same units as all the other energies, i.e., to A d *)
debugPrint["ReRunCollapseRadiusMinimumEnergyBarrierVerbose3: Temperature T = ",temperature,"K corresponds to kT = ",kT];
kT*=kTfactor;
(* ************************
   First, re-evaluate the existing minima and re-select stable minima 
************************* *)
extremaList="extrema"/.oldData;
minimaList=DetermineEnergyBarriers/@extremaList;
stableMinimaList=SelectStableAndMetastableMinima[#,Ebmin,kT]&/@minimaList;
(* ************************
   remove empty elements from stableMinimaList 
************************* *)
stableMinimaList=stableMinimaList//.{}->Sequence[];
debugPrint["ReRunCollapseRadiusMinimumEnergyBarrierVerbose3: Length[stableMinimaList]=",Length[stableMinimaList]];
(* ************************
   If the largest field in stableMinimaList is the same as the largest field in extremaList,
   then the new energy barrier is actually smaller than the old one. That is, starting
   from that largest field value, we need to run the same procedure as in
   CollapseRadiusMinimumEnergyBarrierVerbose3.
   Note that fields are negative, i.e., we actually have to take the minimum.
************************* *)
If[Min["Bz"/.extremaList]==Min["Bz"/.stableMinimaList],
Bz=Min["Bz"/.stableMinimaList];
done=False;,
(* else, there is no need to find the new collapse field *)
done=True;
];
(*
   The following code is copy-pasted from CollapseRadiusMinimumEnergyBarrierVerbose3
*)
counter=0;
factor=0.05;
While[counter<300 && Not[done],
counter+=1;
Bz*=(1+factor);
Rmax=Max["R"/.("mins"/.extremaList[[-1]])];
debugPrint["ReRunCollapseRadiusMinimumEnergyBarrierVerbose3: Starting iteration ",counter," after a total computation time of ",TimeUsed[]-tstart," with Bz = ",Bz,". factor = ",factor,", Rmax = ",Rmax];
extrema=FindAllExtrema[t,p,nl,A,Ku,Di,Ms,Bz,Rmax];
minima=DetermineEnergyBarriers[extrema];
stableMinima=SelectStableAndMetastableMinima[minima,Ebmin,kT];
debugPrint["ReRunCollapseRadiusMinimumEnergyBarrierVerbose3: ",{"stableMinima"->stableMinima}];
If[Length[stableMinima]>0,
(* Do not append duplicates *)
extremaList=Append[extremaList,extrema];
minimaList=Append[minimaList,minima];
stableMinimaList=Append[stableMinimaList,stableMinima];
(* If Req < 2 it is very unlikely that we find another type of minimum. Therefore, we can increase the step size. *)
If[Max["R"/.stableMinimaList[[-1]]]<2 && Max["R"/.stableMinimaList[[-2]]] > 2,factor = 1;];

(* Else, make sure to do one more iteration above the collapse field to make sure that there is no other minimum at smaller R. 
If there is indeed no other minimum then we want to return to the same Bz as now in the following iteration, i.e., in the
iteration following the collapse iteration. The field will Bz*(factor+1) in the next iteration and Bz*(factor/4+1) in the one
following that. If we want Bz*(factor/4+1) to be equal to the current Bz, we have to reduce the current Bz by 1/(factor/4+1) *)
,
(* else: no stable minima found \[Rule] reduce field *)
Bz/=(1+factor);
factor/=4;
collapseFieldExceeded=True;
];
(* Evaluate the result and check if we are done. *)
If[
(* Case 1 *)
(Abs[1-Max["Ebannihilation"/.stableMinima]/(Ebmin+kT)]<=0.01) ||
(* Case 2 *)
(Min["R"/.stableMinimaList[[-1]]]>LargeRThresholdR[t,p,nl,A,Ku,Di,Ms] && 
 Min["Ebannihilation"/"energy"/.stableMinimaList[[-1]]]<10^-8 ) ||
(* Case 3 *)
(Abs[Max["R"/.stableMinimaList[[-1]]]-Max["R"/.stableMinimaList[[-2]]]]<0.01),
If[collapseFieldExceeded,
done=True;
]]];
(*
   Now we found the new collapse field, but the transitions might be different. Hence, we need to
   resample all the transitions.
*)
If[done,
minimaList=ClassifyMinima[minimaList,Ebmin,kT];
stableMinimaList=Map[SelectStableAndMetastableMinima[#,Ebmin,kT]&,minimaList,{1}];
(* ************************
   remove empty elements from stableMinimaList 
************************* *)
stableMinimaList=stableMinimaList//.{}->Sequence[];
result={"extrema"->extremaList,"minima"->minimaList,"stableMinima"->stableMinimaList};
Block[{underSampledTransitions},
underSampledTransitions=FindUnderSampledTransitions["count"/.("stableMinima"/.result)];
debugPrint["ReRunCollapseRadiusMinimumEnergyBarrierVerbose3: under-sampled transition indices: ",underSampledTransitions];
(* Apply ResampleTransition to result with the indices in underSampledTransitions in reverse order to avoid changing the indices of the yet-to-be
   processed elements / transitions *)
(result=ResampleTransition[result,t,p,nl,A,Ku,Di,Ms,Ebmin,temperature*kTfactor,#];&)/@Reverse[underSampledTransitions];
];
result=ResampleTransition[result,t,p,nl,A,Ku,Di,Ms,Ebmin,temperature*kTfactor,Length["stableMinima"/.result]];
result=addHowStabilized[result,t,p,nl,A,Ku,Di,Ms];
Return[Join[result,{"computationTime"->TimeUsed[]-tstart,"success"->True}]];
];
debugPrint["ReRunCollapseRadiusMinimumEnergyBarrierVerbose3: Could not find solution in 300 iterations. Call was:"];
debugPrint[ToExpression[ToString[StringForm["ReRunCollapseRadiusMinimumEnergyBarrierVerbose3[oldData,``,``,``,``,``,``,``,``,``,``]",
ToString[t,InputForm],ToString[p,InputForm],ToString[nl,InputForm],ToString[A,InputForm],ToString[Ku,InputForm],ToString[Di,InputForm],ToString[Ms,InputForm],ToString[Ebmin,InputForm],ToString[temperature,InputForm],ToString[kTfactor,InputForm]]],
StandardForm,Hold]];
Return[{"extrema"->extremaList,"minima"->minimaList,"stableMinima"->stableMinima,"computationTime"->TimeUsed[]-tstart,"success"->False}];
];

FindUnderSampledTransitions[countList_]:=Block[
{candidates,i,cpmt,rcpmt},
(* 
   Find all locations in countList where count c exists in step i but not in step i+1 and where
   not all counts of step i+1 exist in step i. countList should be the counts of stableMinimaList.
*)
candidates={};
For[i=1,i<Length[countList],i++,
(* counts that are in i but not in i+1 *)
cpmt=Complement[countList[[i]],countList[[i+1]]];
(* counts that are i+1 but not in i *)
rcpmt=Complement[countList[[i+1]],countList[[i]]];
If[Length[cpmt]!=0 || Length[rcpmt]!=0,
candidates=Append[candidates,i]]];
Return[candidates];
];

ResampleTransition[previousResult_,t_,p_,nl_,A_,Ku_,Di_,Ms_,Ebmin_,temperature_,transitionIndex_]:=Block[
{kT,extrema,extremaList,minima,minimaList,stableMinima,stableMinimaList,BzList,Bz1,Bz2,Rmax,i},
debugPrint["ResampleTransition: Resampling transition ",transitionIndex];
kT=1.38064852*^-23*temperature; (* thermal energy = kT *)
kT/=A t nl; (* normalize to the same units as all the other energies, i.e., to A d *)
(* Add 18 more data points between transitionIndex and transitionIndex+1 *)
If[transitionIndex==Length["minima"/.previousResult],
Bz1=First[("Bz"/.("minima"/.previousResult))[[transitionIndex]]];
Bz2=Bz1^2/First[("Bz"/.("minima"/.previousResult))[[transitionIndex-1]]];,
Bz1=First[("Bz"/.("minima"/.previousResult))[[transitionIndex]]];
Bz2=First[("Bz"/.("minima"/.previousResult))[[transitionIndex+1]]];
];
BzList=Table[Bz,{Bz,Array[#&,20,{Bz1,Bz2}]}];
(* Remove the already existing data points from BzList *)
BzList=BzList[[2;;-2]];
debugPrint["ResampleTransition: Resampling the following Bz: ",BzList];
Rmax=Max[("R"/.("minima"/.previousResult))[[transitionIndex]]];
extremaList={};
minimaList={};
stableMinimaList={};
For[i=1,i<=Length[BzList],i++,
extrema=FindAllExtrema[t,p,nl,A,Ku,Di,Ms,BzList[[i]],Rmax];
minima=DetermineEnergyBarriers[extrema];
stableMinima=SelectStableAndMetastableMinima[minima,Ebmin,kT];
If[Length[stableMinima]>0,
extremaList=Append[extremaList,extrema];
minimaList=Append[minimaList,minima];
stableMinimaList=Append[stableMinimaList,stableMinima];
]];
(* Insert the result in the previousResult list *)
If[transitionIndex==Length["minima"/.previousResult],
extremaList=FlattenAt[Append["extrema"/.previousResult,extremaList],transitionIndex+1];
minimaList=FlattenAt[Append["minima"/.previousResult,minimaList],transitionIndex+1];,
extremaList=FlattenAt[Insert["extrema"/.previousResult,extremaList,transitionIndex+1],transitionIndex+1];
minimaList=FlattenAt[Insert["minima"/.previousResult,minimaList,transitionIndex+1],transitionIndex+1];
];
minimaList=ClassifyMinima[minimaList,Ebmin,kT];
stableMinimaList=Map[SelectStableAndMetastableMinima[#,Ebmin,kT]&,minimaList,{1}];
(* ************************
   remove empty elements from stableMinimaList 
************************* *)
stableMinimaList=stableMinimaList//.{}->Sequence[];
Return[{"extrema"->extremaList,"minima"->minimaList,"stableMinima"->stableMinimaList}];
];

addHowStabilized[element_,t_,p_,nl_,A_,Ku_,Di_,Ms_]:=Module[{result,stableMinima},
stableMinima=Map[With[{fieldelement=#},Map[Append[#,"howStabilized"->DMIorSFstabilizedFast["R","\[CapitalDelta]","\[Psi]",t,p,nl,A,Ku,Di,Ms,"Bz"]/.#]&,fieldelement]]&,"stableMinima"/.element];
stableMinima=Evaluate[stableMinima];
result=element/.("stableMinima"->_)->("stableMinima"->stableMinima);
Return[result];
];


(*FindRc[t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=(*FindRc[t,p,nl,A,Ku,Di,Ms,Bz]=*)Block[{R,Rc},
Rc=R/.FindRoot[(D[EtotalEM[R,\[CapitalDelta],t,p,nl,PsiDi[R,\[CapitalDelta],t,p,nl,Di,Ms],A,Ku,Di,Ms,Bz],\[CapitalDelta]]/.\[CapitalDelta]->R/ArcSinh[1])==0,{R,1,0.01,100}];
Return[Rc];
];
*)
FindRc[t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=FindRc[t,p,nl,A,Ku,Di,Ms,Bz]=Module[{counter=1,Rc=1,step=5,sign=1,\[CapitalDelta]},
\[CapitalDelta]=Delta[Rc,t,p,nl,A,Ku,Di,Ms,Bz,-1];
While[(\[CapitalDelta]<0||step>0.01)&&counter<200,
If[\[CapitalDelta]<0,
If[sign<0,sign=1;step/=5],
If[sign>0,sign=-1;step/=5]];
If[sign<0&&step>=Rc,step/=2];
Rc+=sign*step;
\[CapitalDelta]=Delta[Rc,t,p,nl,A,Ku,Di,Ms,Bz,-1];
];
Return[N[Rc]];
];

FindRDeltaConst[t_,p_,nl_,A_,Ku_,Di_,Ms_,Bz_]:=FindRDeltaConst[t,p,nl,A,Ku,Di,Ms,Bz]=Block[{R,Rc,RDeltaConst},
Rc=FindRc[t,p,nl,A,Ku,Di,Ms,Bz];
RDeltaConst=R/.FindRoot[Delta[R,t,p,nl,A,Ku,Di,Ms,Bz]==0.999("\[CapitalDelta]"/.DeltaPsiInf[t,p,nl,A,Ku,Di,Ms]),{R,Rc}];
Return[RDeltaConst];
];


End[] (* End Private Context *)

EndPackage[]
