(* ::Package:: *)

BeginPackage["HeterogeneousTemplate`"];

(*****************START******************)

	GetProbabilityTensor[gpo_,EnergyMatrix_,KineticMatrix_,copysize_,templatesize_] := Module [{ForwardTensor,BackwardTensor,ProbabilityTens,ForwardProbTensor},
				(* General order is copy(before),template(before),copy(next),template(next) *)
		ForwardTensor =  ConstantArray[0,{copysize,templatesize+1,copysize,templatesize+1}];
		BackwardTensor = ConstantArray[0,{copysize,templatesize+1,copysize,templatesize+1}];
			(* Rate of binding of the first monomer is ForwardTensor[[1]][[3]][[x]][[y]] *)
			(* Rate of unbinding of the first monomer is BackwardTensor[[1]][[3]][[x]][[y]] *)
			(* Rate of unbinding of the last monomer is ForwardTensor[[x]][[y]][[1]][[3]] *)
	
		ProbabilityTens =  ConstantArray[0,{copysize,templatesize+1,copysize,templatesize+1, templatesize+1,copysize+1}];
		ForwardProbTensor =  ConstantArray[0,{copysize,templatesize+1, templatesize+1,copysize}];
	
		For [ i = 1, i <= copysize,  i++,
			For [ j = 1, j <= templatesize, j++, 
				For [ l = 1, l <= copysize,  l++,
					For [ m = 1, m <= templatesize, m++, 
						ForwardTensor[[i]][[j]][[l]][[m]] = E^( KineticMatrix[[l]][[m]] );
						BackwardTensor[[i]][[j]][[l]][[m]] = ForwardTensor[[i]][[j]][[l]][[m]]*E^(-gpo)*E^(  EnergyMatrix[[i]][[j]]- EnergyMatrix[[l]][[m]] );
					]
				]
			]
		];
		
		For [ i = 1, i <= copysize,  i++,
			For [ j = 1, j <= templatesize, j++,
				ForwardTensor[[1]][[templatesize+1]][[i]][[j]] =  E^( KineticMatrix[[i]][[j]] );
				BackwardTensor[[1]][[templatesize+1]][[i]][[j]] = ForwardTensor[[1]][[templatesize+1]][[i]][[j]]*E^(-EnergyMatrix[[i]][[j]]);
				ForwardTensor[[i]][[j]][[1]][[templatesize+1]] =  E^(-EnergyMatrix[[i]][[j]]);
			]
		];
		
		For [ i = 1, i <= copysize,  i++,
			For [ j = 1, j <= templatesize+1, j++, 
				For [ l = 1, l <= copysize,  l++,
					For [ m = 1, m <= templatesize+1, m++, 
						For [r = 1, r<= templatesize + 1, r++,
							forwardratesum = Total[ForwardTensor,{3}][[l]][[m]][[r]];
							ratesum = forwardratesum + BackwardTensor[[i]][[j]][[l]][[m]];
							For [s = 1, s<= copysize, s++,
								ProbabilityTens[[i]][[j]][[l]][[m]][[r]][[s]] = If [ratesum > 0, ForwardTensor[[l]][[m]][[s]][[r]]/ratesum ,0];
								ForwardProbTensor[[l]][[m]][[r]][[s]]  = If [forwardratesum > 0, ForwardTensor[[l]][[m]][[s]][[r]]/forwardratesum ,0];
							];
							ProbabilityTens[[i]][[j]][[l]][[m]][[r]][[copysize+1]]=  If [ratesum > 0, BackwardTensor[[i]][[j]][[l]][[m]]/ratesum ,0];
						]
					]
				]
			]
		];
		
		Return[{ProbabilityTens,ForwardProbTensor}];
		
	]
	
	GetTransferMatrixListOld[gpo_,EnergyMatrix_,KineticMatrix_,template_]:=Module[{polylen, copysize, templatesize, PerSiteError,ProbVector, tempoutput, 
																		ProbabilityTensor, ForwardProbTensor,ForwardAbsorb, NewBackwardAbsorb, BackwardAbsorb,
																		FullForwardAbsorb, Normalization,FirstForwardAbsorb, TransferMatrixList },
		
		polylen =Length[template];
		copysize = Dimensions[EnergyMatrix][[1]];
		templatesize = Dimensions[EnergyMatrix][[2]];
		(*Generate the constant static tensor of probabilities*)
		tempoutput = GetProbabilityTensor[gpo,EnergyMatrix,KineticMatrix, copysize,templatesize];
		
		TransferMatrixList = Range[polylen];
		
		ProbabilityTensor = tempoutput[[1]];
		ForwardProbTensor = tempoutput[[2]];
		
		ForwardAbsorb = ConstantArray[0,{copysize,copysize}];
		NewBackwardAbsorb =  ConstantArray[0,{copysize,copysize}];
		BackwardAbsorb = ProbabilityTensor[[All,template[[polylen-1]],All,template[[polylen]],templatesize+1,copysize+1]];
		FullForwardAbsorb= ProbabilityTensor[[All,template[[polylen-1]],All,template[[polylen]],templatesize+1,1]];
		
		For[polyidx=polylen,polyidx>2,polyidx--,
			(*Get the Forward Absorbances: These will become our probability vector*)
			For[ i = 1,i <=copysize, i++,
				Normalization = 1 - ForwardProbTensor[[i,template[[polyidx-1]],template[[polyidx]],All]] . BackwardAbsorb[[i,All]];
				For[ j = 1,j <=copysize, j++,
					ForwardAbsorb[[i,j]] = ForwardProbTensor[[i,template[[polyidx-1]],template[[polyidx]],j]]*FullForwardAbsorb[[i,j]]/Normalization;
				]
			];
			TransferMatrixList[[polyidx]]=ForwardAbsorb;
			(* Get the backward absorbances for the next step*)
			For[ i = 1,i <=copysize, i++,
				For[ j = 1,j <=copysize, j++,
					Normalization = 1 - ProbabilityTensor[[i,template[[polyidx-2]],j,template[[polyidx-1]],template[[polyidx]],Range[copysize]]] . BackwardAbsorb[[j,All]];
					NewBackwardAbsorb[[i,j]] = ProbabilityTensor[[i,template[[polyidx-2]],j,template[[polyidx-1]],template[[polyidx]],copysize+1]]/Normalization;
				]
			];
			BackwardAbsorb = NewBackwardAbsorb;
			FullForwardAbsorb = 1-BackwardAbsorb;
		]
		
		(*Get the transfer matrix for the second monomer*)
		For[ i = 1,i <=copysize, i++,
				Normalization = 1 - ForwardProbTensor[[i,template[[1]],template[[2]],All]] . BackwardAbsorb[[i,All]];
				For[ j = 1,j <=copysize, j++,
					ForwardAbsorb[[i,j]] = ForwardProbTensor[[i,template[[1]],template[[2]],j]]*FullForwardAbsorb[[i,j]]/Normalization;
				]
		];
		TransferMatrixList[[2]]=ForwardAbsorb;
		
		For[ j = 1,j <=copysize, j++,
			Normalization = 1 - ProbabilityTensor[[1,templatesize+1,j,template[[1]],template[[2]],Range[copysize]]] . BackwardAbsorb[[j,All]];
			NewBackwardAbsorb[[1,j]] = ProbabilityTensor[[1,templatesize+1,j,template[[1]],template[[2]],copysize+1]]/Normalization;
		];
		
		BackwardAbsorb = NewBackwardAbsorb;
		FullForwardAbsorb = 1-BackwardAbsorb;

		FirstForwardAbsorb = ConstantArray[0,copysize];

		Normalization = 1 - ForwardProbTensor[[1,templatesize+1,template[[1]],All]] . BackwardAbsorb[[1,All]];

		For[ j = 1,j <=copysize, j++,
			FirstForwardAbsorb[[j]] = ForwardProbTensor[[1,templatesize+1,template[[1]],j]]*FullForwardAbsorb[[1,j]]/Normalization;
		];
		
		TransferMatrixList[[1]]=FirstForwardAbsorb;
		Return[TransferMatrixList];
	
	];
	
	GetTransferMatrixList[gpo_,EnergyMatrix_,KineticMatrix_,template_]:=Module[{polylen, copysize, templatesize, PerSiteError,ProbVector, tempoutput, 
																		ProbabilityTensor, ForwardProbTensor,ForwardAbsorb, NewFullForwardAbsorb, ForwardTerm,
																		FullForwardAbsorb, Normalization,FirstForwardAbsorb, TransferMatrixList },
		
		polylen = Length[template];
		copysize = Dimensions[EnergyMatrix][[1]];
		templatesize = Dimensions[EnergyMatrix][[2]];
		(*Generate the constant static tensor of probabilities*)
		tempoutput = GetProbabilityTensor[gpo,EnergyMatrix,KineticMatrix, copysize,templatesize];
		
		TransferMatrixList = Range[polylen];
		
		ProbabilityTensor = tempoutput[[1]];
		ForwardProbTensor = tempoutput[[2]];
		
		ForwardAbsorb = ConstantArray[0,{copysize,copysize}];
		FullForwardAbsorb = ProbabilityTensor[[All,template[[polylen-1]],All,template[[polylen]],templatesize+1,1]];
		NewFullForwardAbsorb = ConstantArray[0,{copysize,copysize}];
		
		For[polyidx=polylen,polyidx>2,polyidx--,
			(*Get the Forward Absorbances: These will become our probability vector*)
			For[ i = 1,i <=copysize, i++,
				Normalization = ForwardProbTensor[[i,template[[polyidx-1]],template[[polyidx]],All]] . FullForwardAbsorb[[i,All]];
				For[ j = 1,j <=copysize, j++,
					ForwardAbsorb[[i,j]] = ForwardProbTensor[[i,template[[polyidx-1]],template[[polyidx]],j]]*FullForwardAbsorb[[i,j]]/Normalization;
				]
			];
			TransferMatrixList[[polyidx]] = ForwardAbsorb;
			(* Get the backward absorbances for the next step*)
			For[ i = 1,i <=copysize, i++,
				For[ j = 1,j <=copysize, j++,
					ForwardTerm = ProbabilityTensor[[i,template[[polyidx-2]],j,template[[polyidx-1]],template[[polyidx]],Range[copysize]]] . FullForwardAbsorb[[j,All]];
					Normalization = ProbabilityTensor[[i,template[[polyidx-2]],j,template[[polyidx-1]],template[[polyidx]],copysize+1]] + ForwardTerm;
					NewFullForwardAbsorb[[i,j]] = ForwardTerm/Normalization;
				]
			];
			FullForwardAbsorb = NewFullForwardAbsorb;
		]
		
		(*Get the transfer matrix for the second monomer*)
		For[ i = 1,i <=copysize, i++,
				Normalization = ForwardProbTensor[[i,template[[polyidx-1]],template[[polyidx]],All]] . FullForwardAbsorb[[i,All]];
				For[ j = 1,j <=copysize, j++,
					ForwardAbsorb[[i,j]] = ForwardProbTensor[[i,template[[1]],template[[2]],j]]*FullForwardAbsorb[[i,j]]/Normalization;
				]
		];
		TransferMatrixList[[2]]=ForwardAbsorb;
		
		For[ j = 1,j <=copysize, j++,
			ForwardTerm = ProbabilityTensor[[1,templatesize+1,j,template[[1]],template[[2]],Range[copysize]]] . FullForwardAbsorb[[j,All]];
			Normalization = ProbabilityTensor[[1,templatesize+1,j,template[[1]],template[[2]],copysize+1]] + ForwardTerm;
			NewFullForwardAbsorb[[1,j]] = ForwardTerm/Normalization;
		];
		
		FullForwardAbsorb = NewFullForwardAbsorb;
		FirstForwardAbsorb = ConstantArray[0,copysize];
		
		Normalization = ForwardProbTensor[[1,templatesize+1,template[[1]],All]] . FullForwardAbsorb[[1,All]];
		For[ j = 1,j <=copysize, j++,
			FirstForwardAbsorb[[j]] = ForwardProbTensor[[1,templatesize+1,template[[1]],j]]*FullForwardAbsorb[[1,j]]/Normalization;
		];
		
		TransferMatrixList[[1]]=FirstForwardAbsorb;
		Return[TransferMatrixList];
	
	];
	
	GetPerSiteError[TransferMatrixList_, Template_] := Module[{polylen,PerSiteError, ProbVector},
		
		polylen = Length[TransferMatrixList];
		PerSiteError = Range[polylen];
	
		PerSiteError[[1]]=1-TransferMatrixList[[1]][[Template[[1]]]] ;
		ProbVector = TransferMatrixList[[1]];
		
		For [i = 2, i <=polylen,i++,
			ProbVector=ProbVector . TransferMatrixList[[i]];
			PerSiteError[[i]] = 1-ProbVector[[Template[[i]]]];
		];
		
		Return[PerSiteError]; 
	];
	
	GetErrorProb[TransferMatrixList_,Template_] := Mean[GetPerSiteError[TransferMatrixList,Template]];
	
	GetEntropyRate[TransferMatrixList_] := Module[{polylen, ProbVector, EntropyRate},
		polylen = Length[TransferMatrixList];
		EntropyRate = Range[polylen];
	
		ProbVector = TransferMatrixList[[1]];
		EntropyRate[[1]] = -ProbVector . Log[ProbVector];
	
		For [i = 2, i <=polylen,i++,
			EntropyRate[[i]] = Total[ProbVector . (-TransferMatrixList[[i]]*Log[TransferMatrixList[[i]]])];
			ProbVector=ProbVector . TransferMatrixList[[i]];
		];
		
		Return[EntropyRate]; 
	];
	
	GetAverageEntropyRate[TransferMatrixList_] := Mean[GetEntropyRate[TransferMatrixList][[Round[Length[TransferMatrixList]/10];;Round[9*Length[TransferMatrixList]/10]]]];
	
	GetAverageEfficiency[TransferMatrixList_,gpo_,copysize_] := (-GetAverageEntropyRate[TransferMatrixList]+Log[copysize])/(gpo+Log[copysize]);
	
	OrderNEntropy[TransitionList_,N_] := 
		Module[ {len,MeanTrans,ProbVector,idx,jdx,kdx,mdx,NewProbVector,LowerOrder,NextDigit,
			PastStates,NewLast,OldLast1,OldLast2,AvgProb,EntropY},
		len = Length[TransitionList];
		MeanTrans = ConstantArray[0,{2,2^N}];
		ProbVector = TransitionList[[1]];
	
		For [jdx = 2, jdx<=N, jdx++,
			NewProbVector = ConstantArray[0,2^jdx];
			For [kdx = 1, kdx<=2^jdx,kdx++,
				LowerOrder=GetLowerOrderState[ kdx,jdx ];
				NextDigit = If[kdx<=(2^(jdx-1)),1,2];
				NewProbVector[[kdx]] = ProbVector[[LowerOrder]]*TransitionList[[jdx, LastDigitUnMap[LowerOrder,jdx-1],NextDigit ]];
			];
			ProbVector = NewProbVector;
		];
		AvgProb = ConstantArray[0,Length[ProbVector]];
		For [idx = N+1, idx <= len, idx++,
			NewProbVector = ConstantArray[0,2^N];
			For [mdx = 1, mdx <=2^N,mdx++,
				If [idx >= Round[len/10] && idx <= Round[len*9/10],
						MeanTrans[[1]][[mdx]] = MeanTrans[[1]][[mdx]]+ProbVector[[mdx]]*TransitionList[[idx,LastDigitUnMap[mdx,N],1]];
						MeanTrans[[2]][[mdx]] = MeanTrans[[2]][[mdx]]+ProbVector[[mdx]]*TransitionList[[idx,LastDigitUnMap[mdx,N],2]],0
					];
				PastStates = GetPastStates[mdx,N];
				NewLast =LastDigitUnMap[ mdx,N];
				OldLast1 = LastDigitUnMap[ PastStates[[1]],N];
				OldLast2 = LastDigitUnMap[ PastStates[[2]],N];
				NewProbVector[[mdx]]= ProbVector[[PastStates[[1]]]]*TransitionList[[idx,OldLast1,NewLast]]+ 
					ProbVector[[PastStates[[2]]]]*TransitionList[[idx,OldLast2,NewLast]];
			];
			ProbVector = NewProbVector;
			If [ idx >= Round[len/10] && idx <= Round[len*9/10],
				AvgProb = AvgProb + ProbVector,0
			];
		];
		
		AvgProb = AvgProb/Total[AvgProb];
		MeanTrans = {MeanTrans[[1]]*1.0/Total[MeanTrans],MeanTrans[[2]]*1.0/Total[MeanTrans]};
		
		EntropY  = 0;
		For [idx = 1, idx <=2^N, idx++,
			EntropY = EntropY + AvgProb[[idx]]*(-MeanTrans[[1,idx]]*Log[ MeanTrans[[1,idx]]] - MeanTrans[[2,idx]]*Log[ MeanTrans[[2,idx]]]);
		];
	
		Return[{EntropY,ProbVector,MeanTrans}];
	]
	
	LastDigitUnMap[digit_,N_] := Boole[digit > 2^(N-1)]+1
	GetPastStates[digit_,N_] := Module[{modDigit},
		modDigit = If[Mod[digit,2^(N-1)]>0,Mod[digit,2^(N-1)],2^(N-1)];
		Return[{2*modDigit-1,2*modDigit}];
	]
	
	GetLowerOrderState[digit_,N_] := Module[{modDigit},
		modDigit = If[Mod[digit,2^(N-1)]>0,Mod[digit,2^(N-1)],2^(N-1)];
		Return[modDigit];
	]
	
	MutualInformation[TransitionList_,N_]:= OrderNEntropy[TransitionList, N] -  GetAverageEntropyRate[TransitionList]
(*****************END******************)

Begin["`Private`"];
End[];
EndPackage[];
