(* ::Package:: *)

BeginPackage["HeterogeneousTemplate`"];
SetDirectory[NotebookDirectory[]];
<<"GraphMarkovFunctions.wl";
(*****************START******************)
	EquilibriumTransferMat[G_,s1_,s2_,Template_] := Module[{seqlist, Frac, start,len,
			CorrectFractionList,zback,z,TransferProbList,zbacklast},
		len = Length[Template];	
		TransferProbList = ConstantArray[0,len];
	
		If[ Template[[1]] == 1, start = s1,start=s2];
		zbacklast = {1,1};
		zback =  G[[;;,Template[[len-1]],;;,Template[[len]]]] . zbacklast;
		TransferProbList[[len]] = G[[;;,Template[[len-1]],;;,Template[[len]]]]*
			Join[{zbacklast,zbacklast},2]/ zback;
	
		Join[{{2,3},{2,3}},2]
		For [i=len-1,i >= 2,i--,
			zbacklast = zback;
			zback =G[[;;,Template[[i-1]],;;,Template[[i]]]] . zbacklast;
			
			TransferProbList[[i]] = G[[;;,Template[[i-1]],;;,Template[[i]]]]*
				Join[{zbacklast,zbacklast},2]/ zback;
		];
		
		zbacklast = zback;
		zback = start . zbacklast;
		TransferProbList[[1]]= start*zbacklast/zback;
		
		Return[TransferProbList];
	]
	
	PartitionFunc[G_,s1_,s2_,Template_] := Module[{seqlist, Frac, start,len, z},
		(*Get The partition function value*)
		len = Length[Template];	
	
		If[ Template[[1]] == 1, start = s1,start=s2];
		z = start;
		For [i=1,i <= len-1,i++,
			z = z . G[[;;,Template[[i]],;;,Template[[i+1]]]];
		];
		z = z . {1,1};
		
		Return[z];
	]
	
	GetProbabilityTensor[gpo_,EnergyMatrix_,KineticMatrix_,copysize_,templatesize_,kbind_,M_] := Module [{ForwardTensor,BackwardTensor,ProbabilityTens,ForwardProbTensor,i,j,l,m},
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
						BackwardTensor[[i]][[j]][[l]][[m]] = ForwardTensor[[i]][[j]][[l]][[m]]*E^(-gpo)*E^( -EnergyMatrix[[i]][[j]][[l]][[m]] );
					]
				]
			]
		];
		
		For [ i = 1, i <= copysize,  i++,
			For [ j = 1, j <= templatesize, j++,
				ForwardTensor[[1]][[templatesize+1]][[i]][[j]] =  E^( KineticMatrix[[i]][[j]] );
				BackwardTensor[[1]][[templatesize+1]][[i]][[j]] = E^( KineticMatrix[[i]][[j]] )*E^(-EnergyMatrix[[1]][[2]][[i]][[j]]);
				ForwardTensor[[i]][[j]][[1]][[templatesize+1]] =  E^(20);
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
		
		Return[{ProbabilityTens,ForwardProbTensor,ForwardTensor,BackwardTensor}];
		
	]
	
GetTransferMatrixList[gpo_,EnergyMatrix_,KineticMatrix_,template_, kbind_,M_]:=Module[{polylen, copysize, templatesize, PerSiteError,ProbVector, tempoutput, 
																		ProbabilityTensor, ForwardProbTensor,ForwardAbsorb, ForwardTerm,NewFullForwardAbsorb,
																		FullForwardAbsorb, Normalization,FirstForwardAbsorb, TransferMatrixList,AbsorbanceProbList,
																		VisitationList,VisitationMatrix,TransientTransferMatrix, FullBranchVisitation,
																		TransientList, ForwardTensor, BackwardTensor, VelocityList, velvec, vzero, bend, before,
																		pfor,pnext,pabs,i,j,l,m },
		polylen =Length[template];
		copysize = Dimensions[EnergyMatrix][[1]];
		templatesize = Dimensions[EnergyMatrix][[2]];
		(*Generate the constant static tensor of probabilities*)
		tempoutput = GetProbabilityTensor[gpo,EnergyMatrix,KineticMatrix, copysize,templatesize,kbind,M];
		
		TransferMatrixList = Range[polylen];
		AbsorbanceProbList = Range[polylen];
		TransientList = Range[polylen];
		VelocityList = Range[polylen];
		
		
		ProbabilityTensor = tempoutput[[1]];
		ForwardProbTensor = tempoutput[[2]];
		ForwardTensor = tempoutput[[3]];
		BackwardTensor = tempoutput[[4]];
		
		ForwardAbsorb = ConstantArray[0,{copysize,copysize}];
		FullForwardAbsorb = ProbabilityTensor[[All,template[[polylen-1]],All,template[[polylen]],templatesize+1,1]];
		AbsorbanceProbList[[polylen]] = FullForwardAbsorb;
		
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
			AbsorbanceProbList[[polyidx-1]] = FullForwardAbsorb;
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
		AbsorbanceProbList[[1]] = FullForwardAbsorb[[1,All]];

		Normalization = ForwardProbTensor[[1,templatesize+1,template[[1]],All]] . FullForwardAbsorb[[1,All]];
		For[ j = 1,j <=copysize, j++,
			FirstForwardAbsorb[[j]] = ForwardProbTensor[[1,templatesize+1,template[[1]],j]]*FullForwardAbsorb[[1,j]]/Normalization;
		];
		
		TransferMatrixList[[1]]=FirstForwardAbsorb;
		
		
		(*Forward recurrences to obtain the average number of visits*)
		VisitationList = ConstantArray[0,polylen+1];
		
		VisitationMatrix = ConstantArray[0,{copysize,copysize}];
		(*StateNum = 1+copysize+copysize^2;
		TransientTransferMatrix = ConstantArray[0,{StateNum,StateNum}];
		(*Probabilities from State 1*)
		For [ k = 2, k <= copysize+1, k++,
				TransientTransferMatrix[[k]][[1]] = ForwardProbTensor[[1,templatesize+1,template[[1]],k-1]];	 
		];
	
		(*Probabilities from first layer*)
		For [ j = 2, j<= copysize+1, j++,
				TransientTransferMatrix[[1]][[j]] = ProbabilityTensor[[1,templatesize+1,j-1,template[[1]],template[[2]],copysize+1]];
			For [ k = 1 , k <= copysize, k++,
				TransientTransferMatrix[[copysize*(j-1)+k+1]][[j]] = ProbabilityTensor[[1,templatesize+1,j-1,template[[1]],template[[2]],k]]
			]
		]
		(*Probabilities from second layer*)
		For [ j = copysize+2, j <= StateNum, j++,
			TransientTransferMatrix[[Quotient[j-2,copysize]+1]][[j]] = 1-AbsorbanceProbList[[2]][[Quotient[j-2,copysize],Mod[j-2,copysize]+1]];
		];
		
		FullBranchVisitation = Inverse[IdentityMatrix[StateNum] - TransientTransferMatrix];
		
		For [ k = 2, k <= copysize+1, k++,
			VisitationMatrix[[1]][[k-1]] = FullBranchVisitation[[k,1]];	 
		];*)
		
		pfor = 1;
		pnext = ForwardProbTensor[[1,templatesize+1,template[[1]],All]];
		pabs = AbsorbanceProbList[[1]];
		
		VisitationList[[1]] = pfor/(pnext . pabs);
		
		pfor = ForwardProbTensor[[1,templatesize+1,template[[1]],All]];
		pnext = ProbabilityTensor[[1,templatesize+1, 1;;copysize, template[[1]],template[[2]], 1;;copysize]];
		pabs = 1-AbsorbanceProbList[[2]];
		For [ k = 1, k <= copysize, k++,
			VisitationMatrix[[1,k]] = VisitationList[[1]]*pfor[[k]]/(1-pnext[[k,All]] . pabs[[k,All]]);	 
		];
				
		VisitationList[[2]] = VisitationMatrix[[1,;;]];

		For [ polyidx = 2, polyidx <= polylen-1, polyidx++,
			(*First, set up the Transient Transfer Matrix *)
			VisitationMatrix = ConstantArray[0,{copysize,copysize,copysize}];
			If[ polyidx == 2,
				bend = 1; before = templatesize+1,
				bend = copysize; before = template[[polyidx-2]]];
				
			For [b = 1, b <= bend, b++,
				For [n = 1, n <= copysize, n++,
					pfor = ProbabilityTensor[[b,before,n,template[[polyidx-1]],template[[polyidx]], 1;;copysize]];
					pnext = ProbabilityTensor[[n,template[[polyidx-1]], 1;;copysize, template[[polyidx]],template[[polyidx+1]], 1;;copysize]];
					pabs = 1-AbsorbanceProbList[[polyidx+1]];
					For [ k = 1, k <= copysize, k++,
						VisitationMatrix[[b]][[n]][[k]] = pfor[[k]]/(1-pnext[[k,All]] . pabs[[k,All]]);	 
					];
				];
			];
			VisitationList[[polyidx+1]] = VisitationMatrix;
		];
		
		VisitationMatrix = ConstantArray[0,{copysize,copysize,copysize}];
		If[ polylen == 2, bend = 1; before = templatesize+1, bend = copysize; before = template[[polylen-2]]];
		For [b = 1, b <= bend, b++,
				For [n = 1, n <= copysize, n++,
					For [ k = 1, k <= copysize, k++,
						VisitationMatrix[[b]][[n]][[k]] = ProbabilityTensor[[b,before,n,template[[polylen-1]],template[[polylen]],k]];	 
					];
				];
			];
		VisitationList[[polylen+1]] = VisitationMatrix;
		Return[{TransferMatrixList,VisitationList}];
	
	];
	
(*GetTransferMatrixList[gpo_,EnergyMatrix_,KineticMatrix_,template_,kbind_,M_]:=Module[{polylen, copysize, templatesize, PerSiteError,ProbVector, tempoutput, 
																		ProbabilityTensor, ForwardProbTensor,ForwardAbsorb, NewFullForwardAbsorb,
																		FullForwardAbsorb, Normalization,FirstForwardAbsorb, TransferMatrixList, ForwardTerm },
		
		polylen =Length[template];
		copysize = Dimensions[KineticMatrix][[1]];
		templatesize = Dimensions[KineticMatrix][[2]];
		(*Generate the constant static tensor of probabilities*)
		tempoutput = GetProbabilityTensor[gpo,EnergyMatrix,KineticMatrix, copysize,templatesize,kbind,M];
		
		TransferMatrixList = Range[polylen];
		
		ProbabilityTensor = tempoutput[[1]];
		ForwardProbTensor = tempoutput[[2]];
		
		ForwardAbsorb = ConstantArray[0,{copysize,copysize}];
		FullForwardAbsorb= ProbabilityTensor[[All,template[[polylen-1]],All,template[[polylen]],templatesize+1,1]];
		NewFullForwardAbsorb= ConstantArray[0,{copysize,copysize}];
		
		For[polyidx=polylen,polyidx>2,polyidx--,
			(*Get the Forward Absorbances: These will become our probability vector*)
			For[ i = 1,i <=copysize, i++,
				Normalization = ForwardProbTensor[[i,template[[polyidx-1]],template[[polyidx]],All]] . FullForwardAbsorb[[i,All]];
				For[ j = 1,j <=copysize, j++,
					ForwardAbsorb[[i,j]] = ForwardProbTensor[[i,template[[polyidx-1]],template[[polyidx]],j]]*FullForwardAbsorb[[i,j]]/Normalization;
				]
			];
			TransferMatrixList[[polyidx]]=ForwardAbsorb;
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

		Normalization = ForwardProbTensor[[1,template[[polyidx-1]],template[[polyidx]],All]] . FullForwardAbsorb[[1,All]];
		For[ j = 1,j <=copysize, j++,
			FirstForwardAbsorb[[j]] = ForwardProbTensor[[1,templatesize+1,template[[1]],j]]*FullForwardAbsorb[[1,j]]/Normalization;
		];
		
		TransferMatrixList[[1]]=FirstForwardAbsorb;
		Return[TransferMatrixList];
	
	];
*)	
	GetPerSiteError[TransferMatrixList_, Template_] := Module[{polylen,PerSiteError, ProbVector,i},
		
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
	
	GetBulkProb[TransferMatrixList_] := Module[{polylen,PerSiteError, ProbVector,i},
		
		polylen = Length[TransferMatrixList];
		PerSiteError = Range[polylen];
	
		PerSiteError[[1]] = TransferMatrixList[[1]] ;
		ProbVector = TransferMatrixList[[1]];
		
		For [i = 2, i <=polylen,i++,
			ProbVector=ProbVector . TransferMatrixList[[i]];
			PerSiteError[[i]] = ProbVector;
		];
		
		Return[PerSiteError]; 
	];
	
	GetErrorProb[TransferMatrixList_,Template_] := Mean[GetPerSiteError[TransferMatrixList,Template]];
	
	GetEntropyRate[TransferMatrixList_] := Module[{polylen, ProbVector, EntropyRate,i},
		polylen = Length[TransferMatrixList];
		EntropyRate = Range[polylen];
	
		ProbVector = TransferMatrixList[[1]];
		EntropyRate[[1]] = -ProbVector . Log[ProbVector];
	
		For [i = 2, i <=polylen,i++,
			ProbVector=ProbVector . TransferMatrixList[[i]];
			EntropyRate[[i]] = Total[ProbVector . (-TransferMatrixList[[i]]*Log[TransferMatrixList[[i]]])];
		];
		
		Return[EntropyRate]; 
	];
	
	GetAverageEntropyRate[TransferMatrixList_] := Mean[GetEntropyRate[TransferMatrixList]];
	
	GetAverageEfficiency[TransferMatrixList_,gpo_,copysize_] := (-GetAverageEntropyRate[TransferMatrixList]+Log[copysize])/(gpo+Log[copysize]);

	(*Functions to do with the fine-grained model*)
	
	(*Functions for setting up parameters for the fine grained model*)
	
	GetKineticTensors[ gbb_,EnergyMatrix_,kbind_,kpol_,M_,copysize_,templatesize_] := Module[{kineticPrePolymerize,
				ForwardTensor,BackwardTensor,forwardratesum,ratesum,i,j,l,m},
		
		kineticPrePolymerize = ConstantArray[0,{copysize,templatesize,copysize,templatesize,2}]; (*The probability tensor prior to polymerization*)
		(*Specifically for the definition of main*)
		ForwardTensor =  ConstantArray[0,{copysize,templatesize+1,copysize,templatesize+1}];
		BackwardTensor = ConstantArray[0,{copysize,templatesize+1,copysize,templatesize+1}];
			(* Rate of binding of the first monomer is ForwardTensor[[1]][[3]][[x]][[y]] *)
			(* Rate of unbinding of the first monomer is BackwardTensor[[1]][[3]][[x]][[y]] *)
			(* Rate of unbinding of the last monomer is ForwardTensor[[x]][[y]][[1]][[3]] *)
		For [ i = 1, i <= copysize,  i++,
			For [ j = 1, j <= templatesize, j++, 
				For [ l = 1, l <= copysize,  l++,
					For [ m = 1, m <= templatesize, m++, 
							(*binding*)
							ForwardTensor[[i]][[j]][[l]][[m]] = kbind[[l,m]]*M[[l]];
							(*polymerization*)
							BackwardTensor[[i]][[j]][[l]][[m]] = kpol[[i,j,l,m]]*Exp[-gbb];
	
							(*unbinding*)
							kineticPrePolymerize[[i]][[j]][[l]][[m]][[1]] = kbind[[l,m]]*Exp[-EnergyMatrix[[i,j,l,m]]];
							(*polymerization*)
							kineticPrePolymerize[[i]][[j]][[l]][[m]][[2]] = kpol[[i,j,l,m]];
	
						]
					]
				]
			];
			
			For [ i = 1, i <= copysize,  i++,
				For [ j = 1, j <= templatesize, j++,
					ForwardTensor[[1]][[templatesize+1]][[i]][[j]] =  kbind[[i,j]]*M[[i]];
					BackwardTensor[[1]][[templatesize+1]][[i]][[j]] = kbind[[i,j]]*E^(-EnergyMatrix[[1]][[2]][[i]][[j]]);
					ForwardTensor[[i]][[j]][[1]][[templatesize+1]] =  kbind[[i,j]]*E^(20);
				]
			];
			
			Return[{ForwardTensor,BackwardTensor,kineticPrePolymerize}]
	]
	
	GetProbabilityTensorFine[gbb_,EnergyMatrix_,kbind_,kpol_,M_,copysize_,templatesize_] := 
			Module[{ProbabilityTensorMain,ProbabilityPrePolymerize,
				ForwardTensor,BackwardTensor,forwardratesum,ratesum,i,j,l,m},
		(*stage (stg) mapping
		1 -> The state before (so this would be after the last polymer has polymerized)
			(*WARNING: NEVER take probabilities from states 1 and 5. they are abstractions so 2 and 4 have somewhere to go, 
				but is otherwise going to be 0*)
		2 -> The MAIN coarse grained state
		3 -> First binding
		4 -> Polymerization
		5 -> The NEXT coarse grained state*)
	
		ProbabilityTensorMain = ConstantArray[0,{copysize,templatesize+1,copysize,templatesize+1,
			 templatesize+1,copysize+1}]; (*The default probability tensor *)
		ProbabilityPrePolymerize = ConstantArray[0,{copysize,templatesize,copysize,templatesize,2}]; (*The probability tensor prior to polymerization*)
	
		(*Specifically for the definition of main*)
		ForwardTensor =  ConstantArray[0,{copysize,templatesize+1,copysize,templatesize+1}];
		BackwardTensor = ConstantArray[0,{copysize,templatesize+1,copysize,templatesize+1}];
			(* Rate of binding of the first monomer is ForwardTensor[[1]][[3]][[x]][[y]] *)
			(* Rate of unbinding of the first monomer is BackwardTensor[[1]][[3]][[x]][[y]] *)
			(* Rate of unbinding of the last monomer is ForwardTensor[[x]][[y]][[1]][[3]] *)
		
	
		For [ i = 1, i <= copysize,  i++,
			For [ j = 1, j <= templatesize, j++, 
				For [ l = 1, l <= copysize,  l++,
					For [ m = 1, m <= templatesize, m++, 
							ForwardTensor[[i]][[j]][[l]][[m]] = kbind[[l,m]]*M[[l]];
							BackwardTensor[[i]][[j]][[l]][[m]] = kpol[[i,j,l,m]]*Exp[-gbb];
	
							(*unbinding*)
							ProbabilityPrePolymerize[[i]][[j]][[l]][[m]][[1]] = kbind[[l,m]]*Exp[-EnergyMatrix[[i,j,l,m]]];
							(*polymerization*)
							ProbabilityPrePolymerize[[i]][[j]][[l]][[m]][[2]] = kpol[[i,j,l,m]];
							ProbabilityPrePolymerize[[i]][[j]][[l]][[m]] = ProbabilityPrePolymerize[[i]][[j]][[l]][[m]]/
								Total[ProbabilityPrePolymerize[[i]][[j]][[l]][[m]]];
						]
					]
				]
			];
			
			For [ i = 1, i <= copysize,  i++,
				For [ j = 1, j <= templatesize, j++,
					ForwardTensor[[1]][[templatesize+1]][[i]][[j]] =  kbind[[i,j]]*M[[i]];
					BackwardTensor[[1]][[templatesize+1]][[i]][[j]] = kbind[[i,j]]*E^(-EnergyMatrix[[1,2,i,j]]);
					ForwardTensor[[i]][[j]][[1]][[templatesize+1]] =  kbind[[i,j]]*E^(20);
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
									ProbabilityTensorMain[[i]][[j]][[l]][[m]][[r]][[s]] = 
										If [ratesum > 0, ForwardTensor[[l]][[m]][[s]][[r]]/ratesum ,0];
								];
								ProbabilityTensorMain[[i]][[j]][[l]][[m]][[r]][[copysize+1]]=  
										If [ratesum > 0, BackwardTensor[[i]][[j]][[l]][[m]]/ratesum ,0];
							]
						]
					]
				]
			];
			
		
		Return[{ProbabilityTensorMain,ProbabilityPrePolymerize}]
	
	]

	
	GetUnnormedProbabilityTensor[gbb_,EnergyMatrix_,kbind_,kpol_,M_,copysize_,templatesize_] := 
		Module[{ProbabilityTensorMain,ProbabilityPrePolymerize,
			ForwardTensor,BackwardTensor,forwardratesum,ratesum,i,j,l,m},
	(*stage (stg) mapping
	1 -> The state before (so this would be after the last polymer has polymerized)
		(*WARNING: NEVER take probabilities from states 1 and 5. they are abstractions so 2 and 4 have somewhere to go, 
			but is otherwise going to be 0*)
	2 -> The MAIN coarse grained state
	3 -> First binding
	4 -> Polymerization
	5 -> The NEXT coarse grained state*)

	ProbabilityTensorMain = ConstantArray[0,{copysize,templatesize+1,copysize,templatesize+1,
		 templatesize+1,copysize+1}]; (*The default probability tensor *)
	ProbabilityPrePolymerize = ConstantArray[0,{copysize,templatesize,copysize,templatesize,2}]; (*The probability tensor prior to polymerization*)

	(*Specifically for the definition of main*)
	ForwardTensor =  ConstantArray[0,{copysize,templatesize+1,copysize,templatesize+1}];
	BackwardTensor = ConstantArray[0,{copysize,templatesize+1,copysize,templatesize+1}];
		(* Rate of binding of the first monomer is ForwardTensor[[1]][[3]][[x]][[y]] *)
		(* Rate of unbinding of the first monomer is BackwardTensor[[1]][[3]][[x]][[y]] *)
		(* Rate of unbinding of the last monomer is ForwardTensor[[x]][[y]][[1]][[3]] *)
	

	For [ i = 1, i <= copysize,  i++,
		For [ j = 1, j <= templatesize, j++, 
			For [ l = 1, l <= copysize,  l++,
				For [ m = 1, m <= templatesize, m++, 
						ForwardTensor[[i]][[j]][[l]][[m]] = kbind[[l,m]]*M[[l]];
						BackwardTensor[[i]][[j]][[l]][[m]] = kpol[[i,j,l,m]]*Exp[-gbb];

						(*unbinding*)
						ProbabilityPrePolymerize[[i]][[j]][[l]][[m]][[1]] = kbind[[l,m]]*Exp[-EnergyMatrix[[i,j,l,m]]];
						(*polymerization*)
						ProbabilityPrePolymerize[[i]][[j]][[l]][[m]][[2]] = kpol[[i,j,l,m]];
					]
				]
			]
		];
		
		For [ i = 1, i <= copysize,  i++,
			For [ j = 1, j <= templatesize, j++,
				ForwardTensor[[1]][[templatesize+1]][[i]][[j]] =  kbind[[i,j]]*M[[i]];
				BackwardTensor[[1]][[templatesize+1]][[i]][[j]] = kbind[[i,j]]*E^(-EnergyMatrix[[1,2,i,j]]);
				ForwardTensor[[i]][[j]][[1]][[templatesize+1]] =  kbind[[i,j]]*E^(20);
			]
		];
		
		For [ i = 1, i <= copysize,  i++,
			For [ j = 1, j <= templatesize+1, j++, 
				For [ l = 1, l <= copysize,  l++,
					For [ m = 1, m <= templatesize+1, m++, 
						For [r = 1, r<= templatesize + 1, r++,
							For [s = 1, s<= copysize, s++,
								ProbabilityTensorMain[[i]][[j]][[l]][[m]][[r]][[s]] =  ForwardTensor[[l]][[m]][[s]][[r]];
							];
							ProbabilityTensorMain[[i]][[j]][[l]][[m]][[r]][[copysize+1]]=  BackwardTensor[[i]][[j]][[l]][[m]];
						]
					]
				]
			]
		];
		
	
	Return[{ProbabilityTensorMain,ProbabilityPrePolymerize}]

	]
	
	(*Functions for *)

	JTot[ForwardTensor_,BackwardTensor_,kineticPrePolymerize_,copysize_ ,templatesize_,
				copylast_,templatelast_,copynow_,templatenow_,templatenext_] := Module[{
				Normalization, JTotPart,w,k,J,Factor21},

		Normalization = 1;
		JTotPart = 0;
		
		(*Assume a petal goes as 1 <-> 2 <-> 3 <-> 1, where 1 is the central state and 3 is one of the 'exit' states*)
			(*For each petal, we label the kinetic constants as follows*)
			(*w: 1 -> 2 *)
			(*k: 2 -> 1*)
			(*s: 2 -> 3*)
			(*p: 3 -> 2*)
			(*J: 3 -> 1*)
		(*Factor31 is p(3)/p(1)*)
		(*Factor23 is p(2)/p(3)*)
		
		(*So, p(1) = 1/(1 + SUM(Factor31*(1+Factor21)) -  we call the denominator here "Normalization"*)
		(*JTotPart = SUM(Factor31*J), so that JTot = JTotPart*p(1) = JTotPart/Normalization*)
		
		If [ templatelast < templatesize+1 && templatenow < templatesize+1,
			(*Physical Descriptors in this case*)	
				(*w: 1 -> 2 Depolymerization*)
				(*k: 2 -> 1 Polymerization*)
				(*J: 2 -> 1 Unbinding*)
			w = BackwardTensor[[copylast,templatelast,copynow,templatenow]];
			k = kineticPrePolymerize[[copylast,templatelast,copynow,templatenow,2]];
			J = kineticPrePolymerize[[copylast,templatelast,copynow,templatenow,1]];
			
			Factor21 = w/(k+J);
			JTotPart = JTotPart + Factor21*J;
			Normalization = Normalization + Factor21,
			(*Entering conditional statement: Where we are either before the first template site or at the first template site*)
			If[ templatenow == templatesize+1,
				(*We are before template site 1*)
				Return[ Total[ForwardTensor[[copynow,templatenow,;;,templatenext]]]  ],
				(*We are at template site 1*)
				JTotPart = JTotPart + BackwardTensor[[copylast,templatelast,copynow,templatenow]];
			]
		];
		
		If[ templatenext < templatesize+1,
			For [ cp = 1, cp<= copysize, cp++,
				(*Reminder*)
					(*w: 1 -> 2 Binding*)
					(*k: 2 -> 1 Unbinding*)
					(*s: 2 -> 3 Polymerization*)

				w = ForwardTensor[[copynow,templatenow,cp,templatenext]];
				k = kineticPrePolymerize[[copynow,templatenow,cp,templatenext,1]];
				J = kineticPrePolymerize[[copynow,templatenow,cp,templatenext,2]];
				
				Factor21 = w/(k+J);
				JTotPart = JTotPart + Factor21*J;
				Normalization = Normalization + Factor21
			],
			(*If at the end of the polymer, make sure to include state 1 as a pre-finishing state*)
			If[templatenext==templatesize+1,
				JTotPart = JTotPart + ForwardTensor[[copynow,templatenow,1,templatenext]],0];
		];
		Return[JTotPart/Normalization]
	];
	
	JTotMatrix[temp_,copysize_ ,templatesize_,templatelast_,templatenow_,templatenext_] := If[  templatelast < templatesize+1,
			f[A_] :=JTot[temp[[1]],temp[[2]],temp[[3]],copysize,templatesize,A[[1]],templatelast,A[[2]],templatenow,templatenext];
			Return[Map[f,CoordinateBoundingBoxArray[{{1,1},{copysize,copysize}},1],{2}]] ,
			f[A_] :=JTot[temp[[1]],temp[[2]],temp[[3]],copysize,templatesize,1,templatelast,A,templatenow,templatenext];
			Return[Map[f,Range[copysize]]] 
	]
	
	GetVisitationList[ conditionalvisitation_ ] := Module[ {polylen, visitation,lengthvisit},
		polylen = Length[conditionalvisitation];
		visitation = ConstantArray[0,polylen];
		lengthvisit = ConstantArray[0,polylen];
		
		visitation[[1]] = conditionalvisitation[[1]];
		lengthvisit[[1]] = Total[visitation[[1]]];
		visitation[[2]] = conditionalvisitation[[2]];
		lengthvisit[[2]] = Total[visitation[[2]]];
		visitation[[3]] = MapThread[Times,{visitation[[2]],conditionalvisitation[[3]][[1]]}];
		lengthvisit[[3]] = Total[visitation[[3]],{1,2}];
		
		For [idx = 4, idx<= polylen, idx++,
			visitation[[idx]] = Total[MapThread [Times,{ visitation[[idx-1]],conditionalvisitation[[idx]] }]];
			lengthvisit[[idx]] = Total[visitation[[idx]],{1,2}]
		];
		
		Return[{visitation, lengthvisit}];
	]
	
	CoarseGrainedJTot[ForwardTensor_,BackwardTensor_,
			copysize_ ,templatesize_,copylast_,templatelast_,copynow_,templatenow_,templatenext_] := Module[{forwardratesum,
				ratesum},
		forwardratesum = Total[ForwardTensor,{3}][[copynow]][[templatenow]][[templatenext]];
		ratesum = forwardratesum + BackwardTensor[[copylast]][[templatelast]][[copynow]][[templatenow]];
		Return[ratesum];					
	]
	
	CoarseGrainedSpeedMatrix[ForwardTensor_,BackwardTensor_,copysize_ ,templatesize_,templatelast_,templatenow_,templatenext_] := If[  templatelast < templatesize+1,
			f[A_] := CoarseGrainedJTot[ForwardTensor,BackwardTensor,copysize,templatesize,A[[1]],templatelast,A[[2]],templatenow,templatenext];
			Return[Map[f,CoordinateBoundingBoxArray[{{1,1},{copysize,copysize}},1],{2}]] ,
			f[A_] := CoarseGrainedJTot[ForwardTensor,BackwardTensor,copysize,templatesize,1,templatelast,A,templatenow,templatenext];
			Return[Map[f,Range[copysize]]]; 
	]
	
	GetTimes[ visitationMatrixls_, gpo_,temp_,copysize_,templatesize_,template_] := 
			Module[ {polylen, visitationTime,LengthTime,JTotTable, TypicalComb, VisitationSum},
		
		ForwardTensor = temp[[1]];
		BackwardTensor = temp[[2]];
		kineticPrePolymerize = temp[[3]];
		
		(*Table of JTotMatrices for a 'typical' index, that is, not near either end of the polymer*)
			(*Calculating these in advance saves computation time*)
		JTotTable = ConstantArray[0,{templatesize,templatesize,templatesize}];
		TypicalComb = Tuples[Range[templatesize],3];
		Do[JTotTable[[templateTriple[[1]],templateTriple[[2]],templateTriple[[3]]]]
			= JTotMatrix[temp,copysize,templatesize,templateTriple[[1]],templateTriple[[2]],
			templateTriple[[3]]], {templateTriple, TypicalComb}];
	
		polylen = Length[visitationMatrixls]-1;
		
		visitationTime = ConstantArray[0,polylen+1];
		LengthTime = ConstantArray[0,polylen+1];
		VisitationSum = ConstantArray[0,polylen+1];
		
		visitationTime[[1]] = visitationMatrixls[[1]]*
			1/JTot[temp[[1]],temp[[2]],temp[[3]],copysize,templatesize,1,3,1,3,template[[1]]];
		LengthTime[[1]] = visitationTime[[1]];
		VisitationSum[[1]] = visitationMatrixls[[1]];
		
		visitationTime[[2]] = visitationMatrixls[[2]]*1/JTotMatrix[temp,copysize,templatesize,
			templatesize+1,template[[1]],template[[2]]] ;
		LengthTime[[2]] = Total[visitationTime[[2]]];
		VisitationSum[[2]] = Total[visitationMatrixls[[2]]];
		
		For [idx = 2, idx<= polylen-1, idx++,
			visitationTime[[idx+1]] = visitationMatrixls[[idx+1]]*1/JTotTable[[template[[idx-1]],
				template[[idx]],template[[idx+1]]]];
			LengthTime[[idx+1]] = Total[visitationTime[[idx+1]],{1,2}];
			VisitationSum[[idx+1]] = Total[visitationMatrixls[[idx+1]],{1,2}];
		];
		
		visitationTime[[polylen+1]] = visitationMatrixls[[polylen+1]]*1/JTotMatrix[temp,copysize,templatesize,
			template[[polylen-1]],template[[polylen]],templatesize+1];
		LengthTime[[polylen+1]] = Total[visitationTime[[polylen+1]],{1,2}];
		VisitationSum[[polylen+1]] = Total[visitationMatrixls[[polylen+1]],{1,2}];
		
		Return[{visitationTime, LengthTime, VisitationSum}];
	]
	
	GetCoarseGrainedTimes[ visitationMatrixls_, gpo_,ForwardTensor_,BackwardTensor_,copysize_,templatesize_,template_] := 
			Module[ {polylen, visitationTime,LengthTime,JTotTable, TypicalComb},
		
		(*Table of JTotMatrices for a 'typical' index, that is, not near either end of the polymer*)
			(*Calculating these in advance saves computation time*)
		JTotTable = ConstantArray[0,{templatesize,templatesize,templatesize}];
		TypicalComb = Tuples[Range[templatesize],3];
		Do[JTotTable[[templateTriple[[1]],templateTriple[[2]],templateTriple[[3]]]]
			= CoarseGrainedSpeedMatrix[ForwardTensor,BackwardTensor,copysize,templatesize,templateTriple[[1]],templateTriple[[2]],
			templateTriple[[3]]], {templateTriple, TypicalComb}];
	
		polylen = Length[visitationMatrixls]-1;
		
		visitationTime = ConstantArray[0,polylen+1];
		LengthTime = ConstantArray[0,polylen+1];
		
		visitationTime[[1]] = visitationMatrixls[[1]]*
			1/CoarseGrainedJTot[ForwardTensor,BackwardTensor,copysize,templatesize,1,3,1,3,template[[1]]];
		LengthTime[[1]] = visitationTime[[1]];
	
		visitationTime[[2]] = visitationMatrixls[[2]]*1/CoarseGrainedSpeedMatrix[ForwardTensor,BackwardTensor,copysize,templatesize,
			templatesize+1,template[[1]],template[[2]]] ;
		LengthTime[[2]] = Total[visitationTime[[2]]];
		
		For [idx = 2, idx<= polylen-1, idx++,
			visitationTime[[idx+1]] = visitationMatrixls[[idx+1]]*1/JTotTable[[template[[idx-1]],
				template[[idx]],template[[idx+1]]]];
			LengthTime[[idx+1]] = Total[visitationTime[[idx+1]],{1,2}];
			
		];
		
		visitationTime[[polylen+1]] = visitationMatrixls[[polylen+1]]*1/CoarseGrainedSpeedMatrix[ForwardTensor,BackwardTensor,copysize,templatesize,
			template[[polylen-1]],template[[polylen]],templatesize+1];
		LengthTime[[polylen+1]] = Total[visitationTime[[polylen+1]],{1,2}];
		
		Return[{visitationTime, LengthTime}];
	]
	
	GetExactVisitation[ExactTransMat_,NonAbsorbingNum_,AbsorbingNum_,copysize_,polylen_] := Module[{TimeMat,TimeVec,out,mat,prev},
		TimeMat = Inverse[IdentityMatrix[NonAbsorbingNum]- TransMat[[1;;NonAbsorbingNum,1;;NonAbsorbingNum]]];
		TimeVec = TimeMat[[All,1]];
		out = ConstantArray[0,polylen];
		For [tier = 1, tier<= polylen, tier++,
			mat = ConstantArray[0,{copysize,copysize}];
			For [ curr = 1, curr<=2, curr++,
				For[ prtally = 1, prtally <= copysize^(tier-1), prtally++,
					prev = Mod[prtally+1,2]+1;	
					mat[[prev,curr]] = mat[[prev,curr]] + 
						TimeVec[[GetState[{tier,curr,prev,prtally},copysize]]]; 
				]
			];
			out[[tier]] = mat;
		];
		Return[out];
	]
	
	IterativeAbsorbingProbabilities[TransferMatrixLs_,len_] := Module[{seqlist,Problist,prob,i},
		seqlist = Flatten[Outer[List,##]&@@Table[{1,2},{len}],len-1];
		Print[seqlist];
		Problist = ConstantArray[0,Length[seqlist]];
		For[idx=1, idx<= Length[seqlist], idx++,
			prob = TransferMatrixLs[[1]][[seqlist[[idx,1]]]];
			For [ i = 1, i<= Length[TransferMatrixLs]-1,i++,
				prob = prob*TransferMatrixLs[[i+1]][[seqlist[[idx,i]],seqlist[[idx,i+1]]]];
			];
			Problist[[idx]] = prob;
		] ;
		Return[Problist];
	]

(*****************END******************)

Begin["`Private`"];
End[];
EndPackage[];
