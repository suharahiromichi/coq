(**
使い方；

M-x run-wolfram
<<ge.wls

B={{0}}
ge[B]
 *)

(**
最初の非零の要素を取り出す。
 *)
pick[A_] := Module[{r},
                  r = ArrayRules[A];
                  If[r[[1]][[2]] == 0,      (* 非零の要素がないか？ *)
                     None,
                     {r[[1]][[1]][[1]], r[[1]][[1]][[2]]}
                  ]
            ];

(**
I行めと1行めを入れ替える。
 *)
xrow[I_, A_] := Module[{B},
                       B = A;
                       B[[1]] = A[[I]];
                       B[[I]] = A[[1]];
                       B]

(**
J列めと1列めを入れ替える。
 *)
xcol[J_, A_] := Module[{B},
                       B = A;
                       B[[All, 1]] = A[[All, J]];
                       B[[All, J]] = A[[All, 1]];
                       B]

(**
上左
 *)
ulsubmx[A_] := A[[1;;1, 1;;1]]

(**
上右
 *)
ursubmx[A_] := A[[1;;1, 2;;Dimensions[A][[2]]]]

(**
下左
 *)
dlsubmx[A_] := A[[2;;Dimensions[A][[1]], 1;;1]]

(**
下右
 *)
drsubmx[A_] := A[[2;;Dimensions[A][[1]], 2;;Dimensions[A][[2]]]]

(**
連結
 *)
blockmx[UL_, UR_, DL_, DR_] := Join[Join[UL, DL],
                                    Join[UR, DR],
                                    2]

gerV[A_] := Module[{n, ij, id},
                   n = Dimensions[A][[2]];
                   id = IdentityMatrix[n];
                   ij = pick[A];
                   If[ij === None,  (* 非零要素が無いか？ *)
                      {{{1}}, id, 0},
                      Module[{i, j, a, B},
                             i = ij[[1]];
                             j = ij[[2]];
                             a = A[[i]][[j]];
                             B = id;
                             B[[1]][[1]] = a;
                             {{{a}}, B, 1}
                      ]
                   ]
            ]

gecV[A_] := Module[{m, ij, id},
                   m = Dimensions[A][[1]];
                   id = IdentityMatrix[m];
                   ij = pick[A];
                   If[ij === None,  (* 非零要素が無いか？ *)
                      {id, {{1}}, 0},
                      Module[{i, j, a, B},
                             i = ij[[1]];
                             j = ij[[2]];
                             a = A[[i]][[j]];
                             B = id;
                             B[[1]][[1]] = a;
                             {B, {{a}}, 1}
                      ]
                   ]
            ]

ge[A_] := Module[{m, n},
                 m = Dimensions[A][[1]];
                 n = Dimensions[A][[2]];
                 Which[m == 0, {{{1}}, {{1}}, 0},
                       n == 0, {{{1}}, {{1}}, 0},
                       m == 1, gerV[A],
                       n == 1, gecV[A],
                       True,
                       Module[{ij},
                              ij = pick[A];
                              If[ij === None,  (* 非零要素が無いか？ *)
                                 {{{1}}, {{1}}, 0},
                                 Module[{i, j, A1, a, u, v, a2, a3, aa, r, ll, uu, lll, uuu},
                                        i = ij[[1]];
                                        j = ij[[2]];
                                        A1 = xrow[i, xcol[j, A]];
                                        a = A[[i]][[j]];
                                        u = ursubmx[A1];     (* 上右 'M_(1,n-1) *)
                                        v = dlsubmx[A1] / a; (* 下左 'M_(m-1,1) *)
                                        a2 = drsubmx[A1];    (* 下右 'M_(m-1,n-1) *)
                                        a3 = v . u;
                                        aa = a2 - a3;
                                        
                                        r = ge[aa];
                                        
                                        ll = blockmx[{{1}},
                                                     ConstantArray[0, {1, m - 1}], (* 'M_(1, m-1) *)
                                                     v,                            (* 'M_(m-1, 1) *)
                                                     r[[1]]]; (* L *)              (* 'M_m-1 *)
                                        uu = blockmx[{{a}},
                                                     u,                            (* 'M_(1, n-1) *)
                                                     ConstantArray[0, {n - 1, 1}], (* 'M_(n-1, 1) *)
                                                     r[[2]]]; (* U *)              (* 'M_n-1 *)
                                        
                                        lll = xrow[i, ll]; (* 'M_m *)
                                        uuu = xcol[j, uu]; (* 'M_n *)
                                        
                                        Print["m,n"];
                                        Print[{m, n}];

                                        Print["A1"];
                                        Print[A1//MatrixForm]; (* 'M_(m,n) *)
                                        Print[];

                                        Print["ll"];
                                        Print[ll//MatrixForm]; (* 'M_m *)
                                        Print[];
                                        Print["v"];
                                        Print[v//MatrixForm]; (* 'M_m *)
                                        Print[];
                                        Print["r[[1]]"];
                                        Print[r[[1]]//MatrixForm]; (* 'M_m *)
                                        Print[];
                                        
                                        Print["uu"];
                                        Print[uu//MatrixForm]; (* 'M_n *)
                                        Print[];
                                        Print["u"];
                                        Print[u//MatrixForm]; (* 'M_n *);
                                        Print[];
                                        Print["r[[2]]"];
                                        Print[r[[2]]//MatrixForm]; (* 'M_n *)
                                        Print[];
                                        
                                        Print[r[[3]] + 1];
                                        
                                        Print["DIMS"];
                                        Print[Dimensions[ll]];
                                        Print[Dimensions[uu]];
                                        Print[Dimensions[lll]];
                                        Print[Dimensions[uuu]];
                                        Print["DIMS----"];
                                        
                                        {lll, uuu, r[[3]] + 1}
(*
                                     Print[v//MatrixForm];
                                     Print[];
                                     Print[a2//MatrixForm];
                                     Print[];
                                     Print[a3//MatrixForm];
                                     Print[];
                                     Print[aa//MatrixForm];
 *)
                                 ]
                              ]
                       ]
                 ]
          ];

(**
Print[xrow[2, A]//MatrixForm]
Print[]
Print[xcol[2, A]//MatrixForm]

Print[ge[{{}}]]
Print[ge[{{0}}]]
Print[ge[{{1}}]]
Print[ge[A]]

Print[ursubmx[A]//MatrixForm]
Print[]
Print[]

Print[dlsubmx[A]//MatrixForm]
Print[]
Print[]

Print[drsubmx[A]//MatrixForm]
Print[]
Print[]

Print[blockmx[ulsubmx[A], ursubmx[A], dlsubmx[A], drsubmx[A]]//MatrixForm]
 *)

A := {{2, 2, 3, 4}, {5, 6, 7, 8}, {9, 10, 11, 12}}

X := {{2, 3, 4}, {6, 7, 8}}

Y := {{3, 4}}

J := {{1, 0}, {0, 1}}

J3 := {{1, 0, 0}, {0, 1, 0}, {0, 0, 1}}

J4 := {{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}

Print[A//MatrixForm]
Print[]
R = ge[A]
Print[R[[1]]//MatrixForm]
Print[]
Print[R[[2]]//MatrixForm]
Print[]
Print[R[[3]]//MatrixForm]

(* END *)
