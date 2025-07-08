(* ::Package:: *)

BeginPackage["GraphMarkovFunctions`"];

ToModel::usage="Converts a list of edges as unordered vertex pairs to a model. i.e. {{1,2},...,{a,b}}";
Begin["`Private`"]
ToModel[g_]:=Module[{y},
y={};
For[i=1,i<=Length[g],i++,
AppendTo[y,{Min[g[[i,1;;2]]]\[DirectedEdge]Max[g[[i,1;;2]]],ToExpression["R"<>"p"<>ToString[Min[g[[i,1;;2]]]]<>"o"<>ToString[Max[g[[i,1;;2]]]]]}];
AppendTo[y,{Max[g[[i,1;;2]]]\[DirectedEdge]Min[g[[i,1;;2]]],ToExpression["R"<>"m"<>ToString[Min[g[[i,1;;2]]]]<>"o"<>ToString[Max[g[[i,1;;2]]]]]}]];
y=DeleteDuplicates[y]];
End[]

ToDirectedModel::usage="Converts a list of edges as unordered vertex pairs to a directed graph. i.e. {{1,2},...,{a,b}}";
Begin["`Private`"]
ToDirectedModel[Model_]:=Module[{y},
y={};
g=Model[[;;,1;;2]];
For[i=1,i<=Length[g],i++,
AppendTo[y,g[[i,1]]\[DirectedEdge]g[[i,2]]]];
y=DeleteDuplicates[y]];
End[]

SpanningTrees::usage="Takes in an undirected graph g and returns a list of spanning trees";
Begin["`Private`"]
SpanningTrees[g_]:=Module[{y},
y={};
n=VertexCount[g];
SubGs=Subsets[EdgeList[g],{n-1}];
For[i=1,i<=Length[SubGs],i++, If[AcyclicGraphQ[Graph[SubGs[[i]]]],AppendTo[y,SubGs[[i]]]]];
y]
End[]

Leaves::usage="Takes in a Tree g and returns the list of leaves";
Begin["`Private`"]
Leaves[g_]:=Module[{y},
y={};
For[i=1,i<=VertexCount[g],i++,If[VertexDegree[g][[i]]==1,AppendTo[y,VertexList[g][[i]]]]];
y]
End[]

ForwardPaths::usage="Takes in a spanning tree g and a target node (a root) and gives the edges directed to the root";
Begin["`Private`"]
ForwardPaths[g_,S_]:=Module[{y},
y={};
Leafs=Complement[Leaves[g],{S}];
LeafNumber=Length[Leafs];
For[i=1,i<=LeafNumber,i++, path=FindShortestPath[g,Leafs[[i]],S];
For[j=2,j<=  Length[path],j++,If[SubsetQ[y,{path[[j-1]]\[DirectedEdge]path[[j]]}]==False,AppendTo[y,path[[j-1]]\[DirectedEdge]path[[j]]]]]];
y]
End[]

Rates::usage="Takes in a model g and a rooted spanning tree FP and returns the product over the edges in the rooted spanning tree";
Begin["`Private`"]
Rates[g_,FP_]:=Product[g[[Position[g[[;;,1]],FP[[i]]][[1,1]],2]],{i,1,Length[FP]}]; 
End[]

STFunction::usage="Takes in a model in the form g = {{1\[DirectedEdge]2,Rate},...,{x\[DirectedEdge]y,Rate},...} and a target node S and returns the sum over spanning trees";

STFunction[M_,S_]:=Module[{y},
g=M//ToModel;
If[ConnectedGraphQ[Graph[g[[;;,1]]]]==False,y=0,
STs=SpanningTrees[UndirectedGraph[g[[;;,1]]]];
y=Total[Table[Rates[g,ForwardPaths[STs[[i]],S]],{i,1,Length[STs]}]]]];

ToAssignments::usage="Converts a set of the form S={{a,b,rate1},{b,a,rate2},...} to a set of assignments to set the rate a \[Rule] b to be rate1, b \[Rule] a to be rate2 etc";
ToAssignments[S_]:=Module[{y},
y={};
For[i=1,i<=Length[S],i++,
If[Length[S[[i,;;]]]==3,
If[S[[i,1]]>S[[i,2]],AppendTo[y,ToExpression["Rm"<>ToString[S[[i,2]]]<>"o"<>ToString[S[[i,1]]]]-> S[[i,3]]],AppendTo[y,ToExpression["Rp"<>ToString[S[[i,1]]]<>"o"<>ToString[S[[i,2]]]]-> S[[i,3]]]]];];
y]

STSum::usage="Takes a model {{a,b,Rab},...} and gives the sum over spanning trees rooted at Root setting the rates to be as assigned";
Begin["`Private`"]
STSum[Model_,Root_]:=GraphMarkovFunctions`Private`STFunction[Model,Root]/.GraphMarkovFunctions`Private`ToAssignments[Model];
End[]

ToAssAdd::usage="Converts a set of the form S={{a,b,rate1},{b,a,rate2},...} to a set of assignments to set the rate a \[Rule] b to be rate1, b \[Rule] a to be rate2 etc aslso adds together repeated entries";
Begin["`Private`"]
ToAssAdd[S_]:=Module[{y},
y={};
For[i=1,i<=Length[S],i++,
If[Length[S[[i,;;]]]==3,If[S[[i,1]]>S[[i,2]],If[MemberQ[y,ToExpression["Rm"<>ToString[S[[i,2]]]<>"o"<>ToString[S[[i,1]]]]->_],y[[Position[y,ToExpression["Rm"<>ToString[S[[i,2]]]<>"o"<>ToString[S[[i,1]]]]->_][[1]]]]=Val->(ToExpression["Rm"<>ToString[S[[i,2]]]<>"o"<>ToString[S[[i,1]]]]/.y)+S[[i,3]]/.{Val-> ToExpression["Rm"<>ToString[S[[i,2]]]<>"o"<>ToString[S[[i,1]]]]},
AppendTo[y,ToExpression["Rm"<>ToString[S[[i,2]]]<>"o"<>ToString[S[[i,1]]]]-> S[[i,3]]]],
If[MemberQ[y,ToExpression["Rp"<>ToString[S[[i,1]]]<>"o"<>ToString[S[[i,2]]]]->_],y[[Position[y,ToExpression["Rp"<>ToString[S[[i,1]]]<>"o"<>ToString[S[[i,2]]]]->_][[1]]]]=(Val->(ToExpression["Rp"<>ToString[S[[i,1]]]<>"o"<>ToString[S[[i,2]]]]/.y)+S[[i,3]])/.{Val-> ToExpression["Rp"<>ToString[S[[i,1]]]<>"o"<>ToString[S[[i,2]]]]},
AppendTo[y,ToExpression["Rp"<>ToString[S[[i,1]]]<>"o"<>ToString[S[[i,2]]]]-> S[[i,3]]]]]];];y]
End[]

TreeNumber::usage="Calculates the number of spanning trees for a graph g of the form {{a,b},...}";
Begin["`Private`"]
TreeNumber[g_]:=Module[{y},
A=AdjacencyMatrix[UndirectedGraph[ToModel[g][[;;,1]]]];
Diag=VertexDegree[UndirectedGraph[ToModel[g][[;;,1]]]];
L=DiagonalMatrix[Diag]-A;
y=Det[L[[;;-2,;;-2]]]];
End[]

PlotModel::usage="Plots Model {{a,b},...} highlighting the start in red and end in blue";
Begin["`Private`"]
PlotModel[g_,S_,F_]:=Graph[UndirectedGraph[ToModel[g][[;;,1]]], VertexStyle->{S->Red,F-> Blue}];
End[]

Q::usage="Takes in a Model, start node and end node and returns the Q term";
Begin["`Private`"]
Q[g_,S_,F_]:=If[MemberQ[ArrayReshape[Complement[g[[;;,1;;2]],{{S,F},{F,S}}],{1,2*Length[Complement[g[[;;,1;;2]],{{S,F},{F,S}}]]}][[1,;;]],S]&&MemberQ[ArrayReshape[Complement[g[[;;,1;;2]],{{S,F},{F,S}}],{1,2*Length[Complement[g[[;;,1;;2]],{{S,F},{F,S}}]]}][[1,;;]],F],
(GraphMarkovFunctions`Private`STFunction[Union[g[[;;,1;;2]],{{S,F}}],S]-GraphMarkovFunctions`Private`STFunction[Complement[g[[;;,1;;2]],{{S,F},{F,S}}],S])/ToExpression["Rm"<>ToString[Min[S,F]]<>"o"<>ToString[Max[S,F]]]//Simplify,
GraphMarkovFunctions`Private`STFunction[Union[g[[;;,1;;2]],{{S,F}}],S]/ToExpression["Rm"<>ToString[Min[S,F]]<>"o"<>ToString[Max[S,F]]]//Simplify];
End[]

ToSpecialModel::usage="Takes in a list of pairs of nodes and returns a reversble model list e.g. {{1, 2}} -> {{1, 2, Rp1o2}, {2, 1, Rm1o2}}";
Begin["`Private`"]
ToSpecialModel[g_]:=Module[{y},
y={};
For[i=1,i<=Length[g],i++,
AppendTo[y,{Min[g[[i,1;;2]]],Max[g[[i,1;;2]]],ToExpression["R"<>"p"<>ToString[Min[g[[i,1;;2]]]]<>"o"<>ToString[Max[g[[i,1;;2]]]]]}];
AppendTo[y,{Max[g[[i,1;;2]]],Min[g[[i,1;;2]]],ToExpression["R"<>"m"<>ToString[Min[g[[i,1;;2]]]]<>"o"<>ToString[Max[g[[i,1;;2]]]]]}]];
y=DeleteDuplicates[y]];
End[]

Ass::usage="";
Begin["`Private`"]
Ass[g_,s_]:=Module[{y},
y={};
m=g//ToModel;
For[i=1,i<= Length[m],i++,AppendTo[y,m[[i,-1]]-> ToExpression[ToString[m[[i,-1]]]<>ToString[s]]]];
y];
End[]

ToTransMatrix::usage="Takes in a Model and final point and returns the transition matrix for the stepwise process";
Begin["`Private`"]
ToTransMatrix[g_,F_]:=Module[{y},
M=ToSpecialModel[g[[;;,1;;2]]];
n=VertexCount[Graph[g[[;;,1;;2]]]];
y=ConstantArray[0,{3n+1,3n+1}];
For[i=1,i<= Length[M],i++,y[[M[[i,1]],M[[i,2]]]]=M[[i,3]]];
For[i=1,i<=n,i++, y[[1,i]]=0];
y=y/.Ass[g,"y"];
y[[F,n+1]]=Polpx;
y[[F+1,n]]=Polmx;
For[i=1,i<= Length[M],i++,y[[M[[i,1]]+n,M[[i,2]]+n]]=M[[i,3]]];
y=y/.Ass[g,"r"];

For[i=1,i<= Length[M],i++,If[M[[i,1]]==1,y[[n+1,M[[i,2]]+2n-1]]=M[[i,3]],
If[M[[i,2]]==1,y[[M[[i,1]]+2n-1,n+1]]=M[[i,3]],
y[[M[[i,1]]+2n-1,M[[i,2]]+2n-1]]=M[[i,3]]]]];
y=y/.Ass[g,"w"];
y[[F+n,3n]]=Polpyr;
y[[F+2n-1,3n+1]]=Polpyw;
y[[1,1]]=1;
y[[3n,3n]]=1;
y[[3n+1,3n+1]]=1;
For[i=1,i<=3n-1,i++,y[[i,;;]]=y[[i,;;]]/Total[y[[i,;;]]]];
y
];
End[]

ToRateMatrix::usage="Takes a set of edges and turns it to a rate matrix";

ToRateMatrix[Model_]:=Module[{y},
Nodes=Sort[DeleteDuplicates[Flatten[Model[[;;,1;;2]]]]];
NodeCount=Length[Nodes];
Entries=ToSpecialModel[Model];
Entries[[;;,1;;2]]=ArrayReshape[Map[(Position[Nodes,#])&,Entries[[;;,1;;2]],{2}],{Length[Entries],2}];
y=ConstantArray[0,{NodeCount,NodeCount}];
For[i=1,i<= Length[Entries],i++,y[[Entries[[i,2]],Entries[[i,1]]]]=Entries[[i,3]]];
y=y+DiagonalMatrix[Table[-Total[y[[;;,i]]],{i,1,NodeCount}]];
y];

ToRateMatrixpoly::usage="";
Begin["`Private`"]
ToRateMatrixpoly[g_,F_]:=Module[{y},
M=ToSpecialModel[g[[;;,1;;2]]];
n=VertexCount[Graph[g[[;;,1;;2]]]];
y=ConstantArray[0,{3n+1,3n+1}];
For[i=1,i<= Length[M],i++,y[[M[[i,1]],M[[i,2]]]]=M[[i,3]]];
For[i=1,i<=n,i++, y[[1,i]]=0];
y=y/.Ass[g,"y"];
y[[F,n+1]]=Polpx;
y[[F+1,n]]=Polmx;
For[i=1,i<= Length[M],i++,y[[M[[i,1]]+n,M[[i,2]]+n]]=M[[i,3]]];
y=y/.Ass[g,"r"];

For[i=1,i<= Length[M],i++,If[M[[i,1]]==1,y[[n+1,M[[i,2]]+2n-1]]=M[[i,3]],
If[M[[i,2]]==1,y[[M[[i,1]]+2n-1,n+1]]=M[[i,3]],
y[[M[[i,1]]+2n-1,M[[i,2]]+2n-1]]=M[[i,3]]]]];
y=y/.Ass[g,"w"];
y[[F+n,3n]]=Polpyr;
y[[F+2n-1,3n+1]]=Polpyw;
For[i=1,i<= 3n+1,i++,
y[[i,i]]=-Total[y[[i,;;]]]];
y
];
End[]

NumericalProbs::usage="";
Begin["`Private`"]
NumericalProbs[g_,F_]:=Module[{y},
P=ToMatrix[g,F];
n=VertexCount[Graph[G]];
Fund=IdentityMatrix[3 n+1]-P;
Mat=Fund[[2;;3n-1,2;;3n-1]];
V1=-Fund[[2;;3n-1,3n]];
V2=-Fund[[2;;3n-1,3n+1]];
V3=-Fund[[2;;3n-1,1]];
pr=Dot[Inverse[Mat],V1][[n]]//FullSimplify;
pw=Dot[Inverse[Mat],V2][[n]]//FullSimplify;
q=Dot[Inverse[Mat],V3][[n]]//FullSimplify;
y={pr,pw,q}];
End[]


ToMatLab::usage="Converts an expression into something to paste into MATLAB";
Begin["`Private`"]
ToMatLab[expr_]:=StringDelete[StringReplace[StringReplace[StringReplace[ToString[expr,InputForm],"*"-> " *"],")"-> " )"],Shortest["E^"<>x__<>{Whitespace|EndOfString}]->"exp("<>x<>")"],Whitespace]; 
End[]

Reroute::usage="Takes a model and rerouts all edges going from From to To";
Begin["`Private`"]
Reroute[Model_,From_,To_]:=Module[{y},
Edges=Model[[;;,1;;2]];
ReroutedEdges={};
y={};
For[i=1,i<= Length[Edges],i++,If[MemberQ[Edges[[i]],From],AppendTo[ReroutedEdges,Edges[[i]]],AppendTo[y,Edges[[i]]]]];
ReroutedEdges=DeleteCases[ReroutedEdges,{From,To}];
ReroutedEdges=DeleteCases[ReroutedEdges,{To,From}];
y=ToSpecialModel[y];
ReroutedModel=ToSpecialModel[ReroutedEdges];
For[i=1,i<= Length[ReroutedModel],i++,
If[ReroutedModel[[i,1]]==From,ReroutedModel[[i,1]]=To,
If[ReroutedModel[[i,2]]==From,ReroutedModel[[i,2]]=To]]];
y=Union[y,ReroutedModel];
y=ToSpecialModel[y[[;;,1;;2]]//DeleteDuplicates]/.ToAssAdd[y];
y=y/.GraphMarkovFunctions`ToAssignments[Model]] 
End[]

EndPackage[]
