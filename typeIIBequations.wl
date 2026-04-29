(* ::Package:: *)

CurrentDir  = DirectoryName[$InputFileName];
Paillaco = CurrentDir <> "PaillacoDiff.wl";

ClearAll[stringIIBequations];
stringIIBequations[BundleTypeIIB_, assum_:{}, simpIN_:Automatic] :=
	Module[{ds2, H3, expboxexpPhi, dPhidPhi,eqsca,eqscasimp,HStarT,F7,F9,eqH3,eqH3simp,eqF1,eqF1simp,eqF3,eqF5,Rddsimp,d2Phidd,F1sq,
	F1sqdd,F3sq,H3sq,F3sqdd,H3sqdd,aF5sqdd,Edd,F5sqdd,timerSimp,aux,simp},

		ds2ore = BundleTypeIIB["ds2"];
		Phi10 = BundleTypeIIB["Phi"];
		H3orB2 = BundleTypeIIB["B2"];
		F1 = BundleTypeIIB["F1"];
		F3 = BundleTypeIIB["F3"];
		coordint = BundleTypeIIB["coord"];

		If[KeyExistsQ[BundleTypeIIB, "constants"],
			Do[d[constIter]=0, {constIter, BundleTypeIIB["constants"]}]
		];

		If[
		simpIN === Automatic,
			simp = Simplify[#,assum]&,
				simp = simpIN
		];
		If[
		Head[ds2ore]===List,
			ds2=ds2ore[[1]] . ds2ore[[2]] . ds2ore[[1]],
				ds2=ds2ore
		];
		
		If[
		FormDegree[H3orB2]=== 2 , 
			H3 = d[H3orB2],
				H3=H3orB2
		];
		
		Block[{$Output={}},ClearGeometric[]];
		Clear[gdd, gUU, sqrtdetg, FormSquare, FormSquaredd];
	
		gdd = DiffToMatrix[ds2,coordint];
		sqrtdetg = Simplify[Sqrt[-Det[gdd]],assum];
		gUU = Inverse[gdd];
		Dim = Length[coordint];
		coord=coordint;

		HStarT[X_] := (-1)^(FormDegree[X]*(Dim-FormDegree[X]))*Hstar[X, gUU, sqrtdetg, d[coord]];
		
		Block[{$Output={}},ComputeRicciScalar[Identity,{gdd,coordint}]];
		Print["sqrtdetg = ",sqrtdetg];
		Print["metric computed"];
		
		Clear[MyHStar];
		Block[{$Output={}},Get[Paillaco]];
		
		Which[
		KeyExistsQ[BundleTypeIIB, "F7"],
			F7 = BundleTypeIIB["F7"],
		True,
			F7 = -HStarT[F3]
		];

		Which[
		KeyExistsQ[BundleTypeIIB, "F9"],
			F9 = BundleTypeIIB["F9"],
		True,
			F9 = HStarT[F1]
		];

		Which[
		KeyExistsQ[BundleTypeIIB, "F5"],
			F5 = BundleTypeIIB["F5"],
		KeyExistsQ[BundleTypeIIB, "G5"],
			Print["-- Computing F5 from G5"];
			G5 = BundleTypeIIB["G5"];
			F5 = G5 + HStarT[G5],
		True,
			F5 = 0
		];

		Print["** F5 self-duality:"];
		Print[Simplify[HStarT[F5]-F5, assum]];
		
		timerSimp[x_] := 
			Module[{xsimp},
				xsimp = TimeConstrained[simp[x], 10, "TimesUp"];
				If[
				xsimp==="TimesUp",
					Print["Extra simplification needed..."];
					Return[x];
				];
				If[xsimp === xsimp*0,
					Print[xsimp===xsimp*0],
						Print["Not clear, simplify later..."]
				];
				Return[xsimp];
			];
		
		expboxexpPhi=Exp[Phi10]Sum[1/sqrtdetg*D[sqrtdetg*gUU[[inda,indb]]D[Exp[-Phi10],coordint[[indb]]],coordint[[inda]]],{inda,10},{indb,10}];
		
		dPhidPhi=FormSquare[d[Phi10]];
		
		Print["** Eq C2"];
		eqF3 = d[F7]-H3\[Wedge]F5;
		
		eqF3 = timerSimp[eqF3];
		Print["** Eq dilaton"];
		
		eqsca = -8*expboxexpPhi+2*RicciScalar-1/(3!)*FormSquare[H3];
		
		eqsca = timerSimp[eqsca];
		Print["** Eq B2"];
		
		eqH3 = simp[d[Exp[-2 Phi10]*HStarT[H3]]+F5\[Wedge]F3+F1\[Wedge]F7];
		
		eqH3 = timerSimp[eqH3];
		Print["** Eq C4"];
		
		eqF5 = simp[d[F5]-H3\[Wedge]F3];
		
		eqF5 = timerSimp[eqF5];
		Print[Style["** Eq C0",Background->Green]];
		
		eqF1 = simp[d[F9] - H3\[Wedge]F7];
		
		eqF1 = timerSimp[eqF1];
		Print["** Computing quantities Einstein equations..."];
		Print["    -Simplifying Rdd"];
		Rddsimp = simp[Rdd];
		d2Phidd = Table[D[Phi10,coordint[[inda]],coordint[[indb]]]-Sum[ChrisUdd[[indc,inda,indb]]D[Phi10,coordint[[indc]]],{indc,Dim}],{inda,Dim},{indb,Dim}];
		F1sq = FormSquare[F1];
		F1sqdd    = If[F1===0,ConstantArray[0,{Dim,Dim}],FormSquaredd[F1]];
		F3sq      = FormSquare[F3]/(3!);
		H3sq      = FormSquare[H3]/(3!);
		F3sqdd    = If[F3===0,ConstantArray[0,{Dim,Dim}],FormSquaredd[F3]/2];
		H3sqdd    = If[H3===0,ConstantArray[0,{Dim,Dim}],FormSquaredd[H3]/2];
		aF5sqdd = If[F5===0,ConstantArray[0,{Dim,Dim}],FormSquaredd[F5]/(4!)];
		Print["    -Simplifying F5sqdd..."];
		F5sqdd = simp[aF5sqdd];
		
		Edd = Rddsimp+2 d2Phidd-1/2*H3sqdd-Exp[2 Phi10]/2*(F1sqdd+F3sqdd+1/2 F5sqdd-1/2*gdd*(F1sq+F3sq));
		
		Print[Style["** Einstein equations",Background->Green]];
		Edd = timerSimp[Edd];
		
		Clear[gdd,gUU,sqrtdetg];Block[{$Output={}},ClearGeometric[]];
		Return[{"eqsca"->eqsca, "eqH3"->eqH3, "eqF1"->eqF1, "eqF3"->eqF3, "eqF5"->eqF5, "Edd"->Edd}]
		];


GamStar = Apply[CenterDot,Map[Gam,Range[10]]];

auxSimpGamma10[LongGam_] :=
	Module[{listlength},
		listlength = Length[Apply[List,LongGam]];
			If[
			listlength>5,
				Return[simpGamma[LongGam\[CenterDot]GamStar]],
					Return[LongGam]
			]
	];

simpGamma10[X_] := X/.CenterDot[y__]:>auxSimpGamma10[CenterDot[y]];

tp[x__]:=TensorProduct[x];

getspinvariations[conf_Association] := Module[
	{e10, Phi, H3, F1, F3, F5, \[Eta]10, dPhislash,H3slash,F1slash,F3slash,F5slash,\[Delta]\[Lambda]sym,\[Omega]slash, \[CapitalGamma]1form10,H31formslash, W, gdd, gUU, Dim, coord},
		Get[Paillaco];

		coord = conf["coord"];
		Dim = Length[coord];
		e10 = conf["e10"];
		\[Eta]10 = conf["\[Eta]dd"];
		Phi = conf["Phi"];
		F1 = conf["F1"];
		F3 = conf["F3"];

		Clear[dxToe, gdd, gUU, eTodx];
		ComputeSpinConnection[e10, \[Eta]10];

		Which[
		KeyExistsQ[conf, "H3"],
			H3 = conf["H3"],
		KeyExistsQ[conf, "B2"],
			H3 = d[conf["B2"]],
		True,
			0
		];
		
		Which[
		KeyExistsQ[conf, "F5"],
			F5 = conf["F5"],
		KeyExistsQ[conf, "G5"],
			Print["--- Computing F5 from G5"];
			gdd = DiffToMatrix[e10.\[Eta]10.e10, coordint];
			sqrtdetg = Simplify[Sqrt[-Det[gdd]],assum];
			gUU = Inverse[gdd];
			Dim = Length[coordint];
			coord=coordint;
			HStarT[X_] := (-1)^(FormDegree[X]*(Dim-FormDegree[X]))*Hstar[X, gUU, sqrtdetg, d[coord]];
			G5 = conf["G5"];
			F5 = G5 + HStarT[G5],
		True,
			F5 = 0
		];

		dPhislash = CliffordMap[d[Phi]];
		H3slash = CliffordMap[H3];
		F1slash = CliffordMap[F1];
		F3slash = CliffordMap[F3];
		F5slash = CliffordMap[F5];
		
		\[Delta]\[Lambda]sym = TensorProduct[dPhislash,Id2]-1/2 TensorProduct[H3slash,\[Sigma][3]]-Exp[Phi]*(TensorProduct[F1slash,I \[Sigma][2]]+1/2*TensorProduct[F3slash,\[Sigma][1]]);
		
		\[Omega]slash = 1/4*Sum[\[Omega]dd[[a,b]]*Gam[a]\[CenterDot]Gam[b],{a,Dim},{b,Dim}]//simpGamma;
		\[CapitalGamma]1form10 = Array[Gam,{Dim}] . \[Eta]10 . Array[e,{Dim}];
		H31formslash = CliffordMap[Contractione[H3]] . Array[e,{Dim}];
		
		W = (tp[\[Omega]slash, Id2] - 1/4*tp[H31formslash, \[Sigma][3]] + Exp[Phi]/8*(tp[F1slash\[CenterDot]\[CapitalGamma]1form10, I*\[Sigma][2]] 
				+ tp[F3slash\[CenterDot]\[CapitalGamma]1form10, \[Sigma][1]] + 1/2*tp[F5slash\[CenterDot]\[CapitalGamma]1form10, I*\[Sigma][2]]));
		Return[<|"1/2" -> \[Delta]\[Lambda]sym, "W" -> W|>];
	];
