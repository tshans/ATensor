ATensor := module()

description "A package containing commands relating to the fifth order symmetric (2,0) tensor density that is not divergence-free.";
	option package;
	export Init, Div, DP, DQ, A, divA, B1, B2, B3, B4, B5, B6, B7, B8, divB1, divB2, divB3, divB4, divB5, divB6, divB7, divB8, divA1, divA2, divA3, divA4, divA5, divA6, divA7, divA8, PartialSum2, PartialSum3, PartialSum4, PartialSum5, PartialSum6, PartialSum7;

# Throughout this module lowercase letters after the initial name (g for the metric, R for the Ricci scalar/covariant derviatives) indicate lower indices and uppercase letters denote upper indices, with summation notation in effect. As an example, RAaD = gAB_Rabc_gCD denotes the trace of the first two indices and the raised third index of the symmetrized third covariant derivative of the Ricci scalar.

# Command list
##################################################
Init := proc(g)
local C, R, Ra, Rab, R3, Rabc;
description "Computes and returns the Ricci scalar and first three symmetrized covariant derivatives computed from a given metric tensor.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Compute the Levi-Civita connection of the metric.
C := Christoffel(g);

# Compute the Ricci scalar.
R := RicciScalar(g);

# Compute the first covariant derivative of the Ricci scalar.
Ra := CovariantDerivative(R,C);

# Compute the second covariant derivative of the Ricci scalar.
Rab := CovariantDerivative(Ra,C);

# Compute the (unsymmetrized) third covariant derivative of the Ricci scalar.
R3 := CovariantDerivative(Rab,C);

# Symmetrize the third covariant derivative of the Ricci scalar.
Rabc := SymmetrizeIndices(R3,[1,2,3], "Symmetric");

# Return the metric and 4 computed tensors.
[g, R, Ra, Rab, Rabc]

end proc:

##################################################

Div := proc(T,g)
local C, delta_T;
description "Computes the divergence of a rank 2 symmetric contravariant tensor using the Levi-Civita connection of the given metric.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor, DifferentialGeometry:-Tools;

# Compute the Levi-Civita connection of the metric.
C := Christoffel(g);

# Take the covariant derivative of the given tensor.
delta_T := CovariantDerivative(T,C);

# Return zero if delta_T is zero. If delta_T is nonzero, contract one index of the given tensor with the covariant derivative index.
if evalb(DGinfo(delta_T,"TensorType") = [["con_bas", "con_bas", "cov_bas"], [["bas", 1]]]) = 'false'
	then return 0
	else ContractIndices(delta_T, [[2,3]])
end if

end proc:

##################################################

DP := proc(g,P,vars)
local r, s, dP, gij, R, Ra, Rab, Rabc, gIJ, RA, S;
description "Computes a variety of derivatives for a given scalar dependent on the Ricci scalar, R, and contracted first covariant derivatives of the Ricci scalar, S = RaRA, derived from the given metric.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Label the two variables in P.
r, s := vars[1], vars[2];

# Compute the various derivatives in a list.
dP := [P, seq(diff(P,r$i),i=1..3), seq(diff(P,s$i),i=1..3), diff(P, r, s), diff(P, r, r, s), diff(P, r, s, s)];

# Extract the various covariant derivatives of the Ricci scalar from the given metric using the Init command.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the inverse metric.
gIJ := InverseMetric(gij);

# Compute the raised first covariant derivative of the Ricci scalar.
RA := RaiseLowerIndices(gIJ, Ra, [1]);

# Compute the S scalar.
S := ContractIndices(evalDG(Ra &t RA),[[1,2]]);

# Substitute the explicit forms of R and S into the derivative list.
subs([r = R, s = S],dP)

end proc:

##################################################

DQ := proc(g,Q,vars)
local r, dQ, gij, R, Ra, Rab, Rabc;
description "Computes a variety of derivatives for a given scalar dependent on the Ricci scalar, R, derived from the given metric.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Label the variable corresponding to R.
r := vars[1];

# Compute the various derivatives in a list.
dQ := [Q, seq(diff(Q,r$i),i=1..3)];

# Extract the various covariant derivatives of the Ricci scalar from the given metric using the Init command.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Substitute the explicit form of R into the derivative list.
subs([r = R],dQ)

end proc:

##################################################

A := proc(g,PQ,vars)
local dP, dQ, A1, A2, A3, A4, A5, A6, A7, A8, a;
description "Computes the symmetric divergence-free (2,0) tensor density A from the given metric and scalar functions P and Q in the variables R and S.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Identify the variables for the scalar functions P and Q.
dP := DP(g, PQ[1], vars);
dQ := DP(g, PQ[2], vars);

# Multiply each tensorial part by its corresponding scalar derivative.
A1 := evalDG(B1(g)*dP[5]);
A2 := evalDG(B2(g)*dP[5]);
A3 := evalDG(B3(g)*dP[6]);
A4 := evalDG(B4(g)*dP[8]);
A5 := evalDG(B5(g)*(dP[2] + dQ[1]));
A6 := evalDG(B6(g)*dP[5]);
A7 := evalDG(B7(g)*(dP[3] + dQ[2]));
A8 := evalDG(B8(g)*dP[1]);

# Sum all 8 terms together.
a := [A1,A2,A3,A4,A5,A6,A7,A8];

evalDG(add(a[i],i=1..8))

end proc:

##################################################

divA := proc(g,PQ,vars)
local gij, R, Ra, Rab, Rabc, C, rootg, gIJ, RA, S, dP, dQ;
description "Computes the divergence of A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the Christoffel symbols of the metric.
C := Christoffel(gij);

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
S := ContractIndices(Ra &t RA, [[1,2]]);

# Compute the various derivatives of P and Q.
dP := DP(g, PQ[1], vars);
dQ := DQ(g, PQ[2], vars);

# divA contains a single term with a first derivative. The coefficient is 1/2 * rootg * (P - R*Q).
evalDG(1/2 * rootg &t RA * (dP[1] - R * dQ[1]));

end proc:

##################################################

B1 := proc(g)
local gij, R, Ra, Rab, Rabc, rootg, gIJ, RA, RAbc, RAac, gIJ_RAac, gIJ_RAac_RD, gIJ_RAac_RC, RIJc, RIJc_RD, RIJc_RC;
description "Computes the term linear in third order derivatives in the tensor A from the given metric.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# There are two terms in B1: both terms involve the product of two metrics, with the first term tracing two indices of the third covariant derivative of the metric and the second term raising the first two indices of the metric. Computing the first term, raise the first index of the third covariant derivative and contract over the first and second indices.
RAbc := RaiseLowerIndices(gIJ,Rabc,[1]);
RAac := ContractIndices(RAbc,[[1,2]]);

# Multiply the traced third covariant derivative by an inverse metric and a raised index first covariant derivative.
gIJ_RAac := evalDG(gIJ &t RAac);
gIJ_RAac_RD := evalDG(gIJ_RAac &t RA);

# Contract the third index of the third covariant derivative with the first covariant derivative.
gIJ_RAac_RC := ContractIndices(gIJ_RAac_RD, [[3,4]]);

# Computing the second term, raise both the first and second indices of the third covariant derivative.
RIJc := RaiseLowerIndices(gIJ, RAbc, [2]);

# Contract the remaining lower index of the third covariant derivative with a raised index first covariant derivative
RIJc_RD := evalDG(RIJc &t RA);
RIJc_RC := ContractIndices(RIJc_RD, [[3,4]]);

# Take the difference between the two terms and multiply the result by a factor of 2*rootg
evalDG(2*rootg &t (gIJ_RAac_RC - RIJc_RC))

end proc:

##################################################

B2 := proc(g)
local gij, R, Ra, Rab, Rabc, rootg, gIJ, Rab_Rcd, Rab_RcD, Rab_RcB, Rab_RCB, Rab_RAB, gIJ_Rab_RAB, RIb_RcB, RIb_RJB;
description "Computes the term quadratic in second order derivatives only in the tensor A from the given metric.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# There are two terms in B2: both terms involve the product of two metrics, with the first term contracting the two second covariant derivatives and the second term raising single indices. In both terms, we compute the product of two second covariant derivatives and contract a pair of indices between the two.
Rab_Rcd := evalDG(Rab &t Rab);
Rab_RcD := RaiseLowerIndices(gIJ, Rab_Rcd, [4]);
Rab_RcB := ContractIndices(Rab_RcD, [[2,4]]);

# Starting with the first term, contract across the remaining indices and multiply by the inverse metric.
Rab_RCB := RaiseLowerIndices(gIJ,Rab_RcB, [2]);
Rab_RAB := ContractIndices(Rab_RCB, [[1,2]]);
gIJ_Rab_RAB := evalDG(gIJ &t Rab_RAB);

# For the second term, raise both remaining lower indices.
RIb_RcB := RaiseLowerIndices(gIJ, Rab_RcB, [1]);
RIb_RJB := RaiseLowerIndices(gIJ, RIb_RcB, [2]);

# Take the difference between the two terms and multiply the result by a factor of 2*rootg
evalDG(2*rootg &t (gIJ_Rab_RAB - RIb_RJB))

end proc:

##################################################

B3 := proc(g)
local gij, R, Ra, Rab, Rabc, rootg, gIJ, RA, Rab_Rcd, Rab_Rcd_RE_RF, Rab_Rcd_RB_RD, Rab_RCd_RB_RD, Rab_RAd_RB_RD, gIJ_Rab_RAd_RB_RD, RIb_Rcd_RB_RD, RIb_RJd_RB_RD;
description "Computes the term quadratic in second order and first order derivatives in the tensor A from the given metric.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# There are two terms in B3: both terms involve the product of two metrics, with the first term contracting the two second covariant derivatives and the second term raising single indices. In both terms, we compute the product of two second covariant derivatives and contract each with a raised first covariant derivative.
Rab_Rcd := evalDG(Rab &t Rab);
Rab_Rcd_RE_RF := evalDG(Rab_Rcd &t RA &t RA);
Rab_Rcd_RB_RD := ContractIndices(Rab_Rcd_RE_RF,[[2,5],[3,6]]); 

# Starting with the first term, contract across the remaining indices and multiply by the inverse metric.
Rab_RCd_RB_RD := RaiseLowerIndices(gIJ, Rab_Rcd_RB_RD, [2]);
Rab_RAd_RB_RD := ContractIndices(Rab_RCd_RB_RD, [[1,2]]);
gIJ_Rab_RAd_RB_RD := evalDG(gIJ &t Rab_RAd_RB_RD);

# For the second term, raise both remaining lower indices.
RIb_Rcd_RB_RD := RaiseLowerIndices(gIJ, Rab_Rcd_RB_RD, [1]);
RIb_RJd_RB_RD := RaiseLowerIndices(gIJ, RIb_Rcd_RB_RD, [2]);

# Take the difference between the two terms and multiply the result by a factor of 4*rootg
evalDG(4*rootg &t (gIJ_Rab_RAd_RB_RD - RIb_RJd_RB_RD))

end proc:

##################################################

B4 := proc(g)
local gij, R, Ra, Rab, Rabc, rootg, gIJ, RA, Rab_Rc_RD, Rab_Rc_RB, Rab_RC_RB, Rab_RA_RB, gIJ_Rab_RA_RB, RIb_Rc_RB, RIb_RJ_RB, sym_RIb_RJ_RB;
description "Computes the term quadratic in first order and linear in second order derivatives in the tensor A from the given metric.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# There are two terms in B4: both terms involve the product of two metrics, with the first term contracting between a first and second derivative and the second term raising the two free indices. In both terms, we compute the product of a second covariant derivative and two first covariant derivatives (one up, one down), contracting across the second covariant derviative and the upper first covariant derivative.
Rab_Rc_RD := evalDG(Rab &t Ra &t RA);
Rab_Rc_RB := ContractIndices(Rab_Rc_RD, [[2,4]]); 

# For the first term, contract across the remaining indices and multiply by the inverse metric.
Rab_RC_RB := RaiseLowerIndices(gIJ, Rab_Rc_RB, [2]);
Rab_RA_RB := ContractIndices(Rab_RC_RB, [[1,2]]);
gIJ_Rab_RA_RB := evalDG(gIJ &t Rab_RA_RB);

# For the second term, raise both remaining lower indices then symmetrize.
RIb_Rc_RB := RaiseLowerIndices(gIJ, Rab_Rc_RB, [1]);
RIb_RJ_RB := RaiseLowerIndices(gIJ, RIb_Rc_RB, [2]);
sym_RIb_RJ_RB := SymmetrizeIndices(RIb_RJ_RB, [1,2], "Symmetric");

# Take the difference between the two terms and multiply the result by a factor of 4*rootg
evalDG(4*rootg &t (gIJ_Rab_RA_RB - sym_RIb_RJ_RB))

end proc:

##################################################

B5 := proc(g)
local gij, R, Ra, Rab, Rabc, rootg, gIJ, RAb, RAa, gIJ_RAa, RIb, RIJ;
description "Computes the term linear in second order derivatives in the tensor A from the given metric.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# There are two terms in B5: both terms involve the product of two metrics, with the first term tracing the second derivative and the second term raising both indices of the second derivative.

# For the first term, compute the trace of the second derivative and multiply by an inverse metric.
RAb := RaiseLowerIndices(gIJ, Rab, [1]);
RAa := ContractIndices(RAb, [[1,2]]);
gIJ_RAa := evalDG(gIJ &t RAa);

# For the second term, raise both remaining lower indices then symmetrize.
RIb := RaiseLowerIndices(gIJ, Rab, [1]);
RIJ := RaiseLowerIndices(gIJ, RIb, [2]);

# Take the difference between the two terms and multiply the result by a factor of rootg
evalDG(rootg &t (gIJ_RAa - RIJ))

end proc:

##################################################

B6 := proc(g)
local gij, R, Ra, Rab, Rabc, rootg, gIJ, RA, R_RI_RJ;
description "Computes the term quadratic in first order derivatives and linear in the Ricci scalar in the tensor A from the given metric.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# There is one term in B6, comprised of a Ricci scalar and two raised first covariant derivatives, with a coefficicent of 1/3*rootg.
R_RI_RJ := evalDG(R * RA &t RA);
evalDG(1/3*rootg &t R_RI_RJ)

end proc:

##################################################

B7 := proc(g)
local gij, R, Ra, Rab, Rabc, rootg, gIJ, RA, Ra_RB, Ra_RA, gIJ_S, RI_RJ;
description "Computes the term quadratic in first order derivatives in the tensor A from the given metric.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# There are two terms in B7: both terms involve the product of two metrics, with the first term contracting the two first derivatives and the second raising the indices of both.

# For the first term, contract the two first derivatives and multiply by an inverse metric.
Ra_RB := evalDG(Ra &t RA);
Ra_RA := ContractIndices(Ra_RB, [[1,2]]);
gIJ_S := evalDG(gIJ*Ra_RA);

# For the second term, raise both first derivatives.
RI_RJ := evalDG(RA &t RA);

# Take the difference between the two terms and multiply the result by a factor of rootg
evalDG(rootg &t (gIJ_S - RI_RJ))

end proc:

##################################################

B8 := proc(g)
local gij, R, Ra, Rab, Rabc, rootg, gIJ;
description "Computes the term linear in the Ricci scalar in the tensor A from the given metric.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# There is one term in B8, consisting of the Ricci tensor and an inverse metric multiplied by a factor of 1/2*rootg.
evalDG(1/2*R*rootg &t gIJ)

end proc:

##################################################

divB1 := proc(g) 
local gij, R, Ra, Rab, Rabc, gIJ, rootg, RA, Ra_RB, S, R_Rab_RC, R_RIb_RC, R_RIb_RB, R_RAa_RI, S_RI, Rabc_Rde, RAbc_RDI, RAac_RCI, RIBC_Rde, RIBC_Rbc;
description "Computes the divergence of the B1 term in the tensor A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the inverse metric.
gIJ := InverseMetric(gij);

# Compute the square root of the metric determinant.
rootg := MetricDensity(gij,1);

# Compute the raised first covariant derivative of R.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
Ra_RB := evalDG(Ra &t RA);
S := ContractIndices(Ra_RB, [[1,2]]);

# Compute all 5 terms of divB1. 

# The first term consists of R, as well as a second and first derivative, with the second derivative contracted against the first derivative and with its free index raised.
R_Rab_RC := evalDG(R * Rab &t RA);
R_RIb_RC := RaiseLowerIndices(gIJ, R_Rab_RC,[1]);
R_RIb_RB := ContractIndices(R_RIb_RC, [[2,3]]);

# The second term is similar to the first term but with the second derivative traced and the first derivative raised.
R_RAa_RI := ContractIndices(R_RIb_RC, [[1,2]]);

# The third index is the product of S and a raised first derivative.
S_RI := evalDG(S*RA);

# The fourth term is the product of one second and one third derivative. with two indices traced on the third derivative and the remaining index contracted against a second derivative. The free index on the second derivative is raised.
Rabc_Rde := evalDG(Rabc &t Rab);
RAbc_RDI := RaiseLowerIndices(gIJ, Rabc_Rde, [1,4,5]);
RAac_RCI := ContractIndices(RAbc_RDI, [[1,2],[3,4]]);

# The fifth term is similar to the fourth but the second derivative is contracted against two of the third derivative's indices and the remaining index is raised.
RIBC_Rde := RaiseLowerIndices(gIJ, Rabc_Rde, [1,2,3]);
RIBC_Rbc := ContractIndices(RIBC_Rde, [[2,4],[3,5]]);

# The coefficients of each term are -8/3 for term one, +4/3 for term two, -1/3 for term three, +2 for term four, and -2 for term five. Sum all five and multiply by rootg.
evalDG(rootg &t (-8/3*R_RIb_RB + 4/3*R_RAa_RI - 1/3*S_RI + 2*RAac_RCI - 2*RIBC_Rbc))

end proc:

##################################################

divB2 := proc(g) 
local gij, R, Ra, Rab, Rabc, gIJ, rootg, RA, Rabc_Rde, RIBC_Rde, RIBC_Rbc, RAbc_RDI, RAac_RCI, R_Rab_RI, R_RAb_RI, R_RAa_RI, R_RIa_RA;
description "Computes the divergence of the B2 term in the tensor A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the inverse metric.
gIJ := InverseMetric(gij);

# Compute the square root of the metric determinant.
rootg := MetricDensity(gij,1);

# Compute the raised first covariant derivative of R.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute all 4 terms of divB2. The first term is the product of one second and one third derivative. The second derivative is contracted against two of the third derivative's indices, with the remaining index raised.
Rabc_Rde := evalDG(Rabc &t Rab);
RIBC_Rde := RaiseLowerIndices(gIJ, Rabc_Rde, [1,2,3]);
RIBC_Rbc := ContractIndices(RIBC_Rde, [[2,4],[3,5]]);

# The second term is similar to the first but with two indices traced on the third derivative and the remaining index contracted against a second derivative. The free index on the second derivative is raised.
RAbc_RDI := RaiseLowerIndices(gIJ, Rabc_Rde, [1,4,5]);
RAac_RCI := ContractIndices(RAbc_RDI, [[1,2],[3,4]]);

# The third term consists of R, as well as a second and first derivative, with the second derivative traced and the first derivative raised.
R_Rab_RI := evalDG(R * Rab &t RA);
R_RAb_RI := RaiseLowerIndices(gIJ, R_Rab_RI,[1]);
R_RAa_RI := ContractIndices(R_RAb_RI, [[1,2]]);

# The fourth term is similar to the third term but with the second derivative contracted against the first derivative and with its free index raised.
R_RIa_RA := ContractIndices(R_RAb_RI, [[2,3]]);

# The coefficients of each term are +2 for term one, -2 for term two, -5/3 for term three, and +4/3 for term four. Sum all four and multiply by rootg.
evalDG(rootg &t (2*RIBC_Rbc - 2*RAac_RCI - 5/3*R_RAa_RI + 4/3*R_RIa_RA))

end proc:

##################################################

divB3 := proc(g) 
local gij, R, Ra, Rab, Rabc, gIJ, rootg, RA, Rabc_Rde_RF_RG, RIbc_RDe_RF_RG, RIbc_RBe_RC_RE, RBbc_RIe_RC_RE, R_Rab_RC_RD_RE, R_Rab_RA_RB_RI, Rab_Rcd_Ref_RG, RIb_RCd_REf_RG, RIb_RBd_RDf_RF, RAB_Rcd_RIf_RG, RAB_Rab_RIf_RF;
description "Computes the divergence of the B3 term in the tensor A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the inverse metric.
gIJ := InverseMetric(gij);

# Compute the square root of the metric determinant.
rootg := MetricDensity(gij,1);

# Compute the raised first covariant derivative of R.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute all 5 terms of divB3. The first term is the product of one third, one second, and two first derivatives. The free index is on the third derivative, with the remaining indices contracted against a second and first derivative. The second index of the second derivative is contracted against the final first derivative.
Rabc_Rde_RF_RG := evalDG(Rabc &t Rab &t RA &t RA);
RIbc_RDe_RF_RG := RaiseLowerIndices(gIJ,Rabc_Rde_RF_RG, [1,4]);
RIbc_RBe_RC_RE := ContractIndices(RIbc_RDe_RF_RG, [[2,4],[3,6],[5,7]]);

# The second term is the same product as the first, with the third derivative traced over two indices and contracted with a first derivative on the remaining index, as well as a first derivative contracted against the second derivative. The free index on the second derivative is raised.
RBbc_RIe_RC_RE := ContractIndices(RIbc_RDe_RF_RG, [[1,2],[3,6],[5,7]]);

# The third term consists of R, three first derivatives, and one second derivative. The second derivative is contracted against two of the first derivatives.
R_Rab_RC_RD_RE := evalDG(R * Rab &t RA &t RA &t RA);
R_Rab_RA_RB_RI := ContractIndices(R_Rab_RC_RD_RE, [[1,3],[2,4]]);

# The fourth term contains one first derivative and three second derivatives. One of the second derivatives is contracted over a single index with each of the other two second derivatives, with one free index raised and the other contracted with the first derivative.
Rab_Rcd_Ref_RG := evalDG(Rab &t Rab &t Rab &t RA);
RIb_RCd_REf_RG := RaiseLowerIndices(gIJ, Rab_Rcd_Ref_RG, [1,3,5]);
RIb_RBd_RDf_RF := ContractIndices(RIb_RCd_REf_RG, [[2,3],[4,5],[6,7]]);

# The fifth term contains the same product as the fourth, with two of the second derivatives contracted against each other and the remaining second derivative contracted against the first derivative. The free index on this last second derivative is raised.
RAB_Rcd_RIf_RG := RaiseLowerIndices(gIJ, Rab_Rcd_Ref_RG, [1,2,5]);
RAB_Rab_RIf_RF := ContractIndices(RAB_Rcd_RIf_RG, [[1,3],[2,4],[6,7]]);

# The coefficients of each term are +4 for terms one and four, -4 for terms two and five, and -2/3 for term three. Sum all five and multiply by rootg.
evalDG(rootg &t (4*RIbc_RBe_RC_RE - 4*RBbc_RIe_RC_RE - 2/3*R_Rab_RA_RB_RI + 4*RIb_RBd_RDf_RF - 4*RAB_Rab_RIf_RF))

end proc:

##################################################

divB4 := proc(g) 
local gij, R, Ra, Rab, Rabc, gIJ, rootg, RA, Ra_RB, S, RIbc, RIbc_RD_RE, RIbc_RB_RC, RAab, RAab_RC_RI, RAab_RB_RI, R_S_RI, Rab_Rcd_RE, RIB_Rcd_RE, RIB_Rbe_RE, RAB_Rcd_RI, RAB_Rab_RI, RIb_RCd_RE, RIe_RCc_RE;
description "Computes the divergence of the B4 term in the tensor A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the inverse metric.
gIJ := InverseMetric(gij);

# Compute the square root of the metric determinant.
rootg := MetricDensity(gij,1);

# Compute the raised first covariant derivative of R.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
Ra_RB := evalDG(Ra &t RA);
S := ContractIndices(Ra_RB, [[1,2]]);

# Compute all 6 terms of divB4. The first term raises the first index of a third covariant derivative and contracts the remaining indices against two first covariant derivatives.
RIbc := RaiseLowerIndices(gIJ,Rabc,[1]);
RIbc_RD_RE := evalDG(RIbc &t RA &t RA);
RIbc_RB_RC := ContractIndices(RIbc_RD_RE, [[2,4],[3,5]]);

# The second term traces off two indices of a third covariant derivative, contracts the remaining index against a first covariant derivative, and multiplies by another first covariant derivative.
RAab := ContractIndices(RIbc, [[1,2]]);
RAab_RC_RI := evalDG(RAab &t RA &t RA);
RAab_RB_RI := ContractIndices(RAab_RC_RI, [[1,2]]);

# The third term is R*S multiplied by a raised first covariant derivative.
R_S_RI := evalDG(R * S * RA);

# The fourth term is the product of two second and one first derivatives, contracting the two second derivatives against each other, while contracting one free index against a first derivative and raising the remaining first index.
Rab_Rcd_RE := evalDG(Rab &t Rab &t RA);
RIB_Rcd_RE := RaiseLowerIndices(gIJ, Rab_Rcd_RE, [1,2]);
RIB_Rbe_RE := ContractIndices(RIB_Rcd_RE, [[2,3], [4,5]]);

# The fifth term consists of the same product as the fourth term but with the two second derivatives contracted against each other and the first derivative has the free index.
RAB_Rcd_RI := RaiseLowerIndices(gIJ, Rab_Rcd_RE, [1,2]);
RAB_Rab_RI := ContractIndices(RAB_Rcd_RI, [[1,3], [2,4]]);

# The sixth term is simlilar to the fourth and fifth, with the trace of one second derivative multiplied by a second derivative contracted against a first derivative with the free index raised.
RIb_RCd_RE := RaiseLowerIndices(gIJ, Rab_Rcd_RE, [1,3]);
RIe_RCc_RE := ContractIndices(RIb_RCd_RE, [[2,5],[3,4]]);

# The coefficients of each term are +2 for term one, -2 for terms two, five and six, -1/3 for term three, and +4 for term four. Sum all six and multiply by rootg.
evalDG(rootg &t (2*RIbc_RB_RC - 2*RAab_RB_RI - 1/3*R_S_RI + 4*RIB_Rbe_RE - 2*RAB_Rab_RI - 2*RIe_RCc_RE))

end proc:

##################################################

divB5 := proc(g) 
local gij, R, Ra, Rab, Rabc, gIJ, rootg, RA;
description "Computes the divergence of the B5 term in the tensor A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the inverse metric.
gIJ := InverseMetric(gij);

# Compute the square root of the metric determinant.
rootg := MetricDensity(gij,1);

# Compute the raised first covariant derivative of R.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute divB5. The only term is -1/2*rootg*R multiplied by a raised first covariant derivative.
evalDG(-1/2*R*rootg &t RA)

end proc:

##################################################

divB6 := proc(g) 
local gij, R, Ra, Rab, Rabc, gIJ, rootg, RA, Ra_RB, S, S_RI, Rab_RC, Rab_RB, RIb_RB, R_RIb_RB, RaB, RaA, RaA_RI, R_RaA_RI;
description "Computes the divergence of the B6 term in the tensor A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the inverse metric.
gIJ := InverseMetric(gij);

# Compute the square root of the metric determinant.
rootg := MetricDensity(gij,1);

# Compute the raised first covariant derivative of R.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
Ra_RB := evalDG(Ra &t RA);
S := ContractIndices(Ra_RB, [[1,2]]);

# Compute the three terms of divB6. The first term is S multiplied by a raised first covariant derivative.
S_RI := evalDG(S * RA);

# The second term contracts one raised first covariant derivative of R with a second covariant derivative and raises the remaining index, while multiplying by R.
Rab_RC := evalDG(Rab &t RA);
Rab_RB := ContractIndices(Rab_RC, [[2,3]]);
RIb_RB := RaiseLowerIndices(gIJ, Rab_RB, [1]);
R_RIb_RB := evalDG(R * RIb_RB);

# The third term contains a raised first derivative and the trace of a second derivative, while multiplying by R.
RaB := RaiseLowerIndices(gIJ, Rab, [2]);
RaA := ContractIndices(RaB,[[1,2]]);
RaA_RI := evalDG(RaA * RA);
R_RaA_RI := evalDG(R * RaA_RI);

# Sum all three terms and multiply by 1/3*rootg.
evalDG(1/3*rootg &t (S_RI + R_RIb_RB + R_RaA_RI))

end proc:

##################################################

divB7 := proc(g) 
local gij, R, Ra, Rab, Rabc, gIJ, rootg, RA, Rab_RC, Rab_RB, RIb_RB, RaB, RaA, RaA_RI;
description "Computes the divergence of the B7 term in the tensor A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the inverse metric.
gIJ := InverseMetric(gij);

# Compute the square root of the metric determinant.
rootg := MetricDensity(gij,1);

# Compute the raised first covariant derivative of R.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute the two terms of divB7. The first term contracts one raised first covariant derivative of R with a second covariant derivative and raises the remaining index.
Rab_RC := evalDG( RA &t Rab);
Rab_RB := ContractIndices(Rab_RC, [[1,2]]);
RIb_RB := RaiseLowerIndices(gIJ, Rab_RB, [1]);

# The second term contains a raised first derivative and the trace of a second derivative.
RaB := RaiseLowerIndices(gIJ, Rab, [2]);
RaA := ContractIndices(RaB,[[1,2]]);
RaA_RI := evalDG(RaA * RA);

# Subtract the second term from the first and multiply by rootg.
evalDG(rootg &t (RIb_RB - RaA_RI))

end proc:

##################################################

divB8 := proc(g) 
local gij, R, Ra, Rab, Rabc, gIJ, rootg, RA;
description "Computes the divergence of the B8 term in the tensor A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the inverse metric.
gIJ := InverseMetric(gij);

# Compute the square root of the metric determinant.
rootg := MetricDensity(gij,1);

# Compute the raised first covariant derivative of R.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute divB8.
evalDG(1/2*rootg &t RA)

end proc:

##################################################

divA1 := proc(g,PQ,vars)
local gij, R, Ra, Rab, Rabc, C, rootg, gIJ, RA, S, dP, R_RA_Rbc, R_RA_RBc, R_RA_RBa, P1, R_RA_RBb, P2, S_RA, P3, Rab_Rcde, RAB_RCde, RAB_RCcb, P4, RAB_RCab, P5, RA_RB_Rcde, RA_RB_RCde, RA_RB_RCcb, P6, RA_RB_RCab, P7, RA_Rb_Rcd_Refg, RA_Rb_RCD_REfg, RA_Rd_RCD_REea, P8, RA_Rd_RCD_REac, P9;
description "Computes the divergence of the full third order term in A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the Christoffel symbols of the metric.
C := Christoffel(gij);

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
S := ContractIndices(Ra &t RA, [[1,2]]);

# Compute the various derivatives of P.
dP := DP(g, PQ[1], vars);

# Construct the nine terms of divA1. The first two terms are the product of R, a first derivative, and a second derivative. The first term raises one index on the second derivative and contracts the remaining index with the first derivative. The coefficient is -8/3 * rootg * dP/dS.
R_RA_Rbc := evalDG(R * RA &t Rab);
R_RA_RBc := RaiseLowerIndices(gIJ, R_RA_Rbc, [2]);
R_RA_RBa := ContractIndices(R_RA_RBc, [[1,3]]);
P1 := evalDG(-8/3 * rootg &t R_RA_RBa * dP[5]);

# The second term traces the second derivative and the raised first derivative has its index free. The coefficient is 4/3 * rootg * dP/dS.
R_RA_RBb := ContractIndices(R_RA_RBc, [[2,3]]);
P2 := evalDG(4/3 * rootg &t R_RA_RBb * dP[5]);

# The third term is the product of S and a raised first derivative. The coefficient is -1/3 * rootg * dP/dS
S_RA := evalDG(S * RA);
P3 := evalDG(-1/3 * rootg &t S_RA * dP[5]);

# The fourth and fifth terms are the product of a second and third derivative of R. The fourth term traces two indices of the third derivative, contracting the remaining index with the second derivative. The free index on the second derivative is raised. The coefficient is 2 * rootg * dP/dS.
Rab_Rcde := evalDG(Rab &t Rabc);
RAB_RCde := RaiseLowerIndices(gIJ, Rab_Rcde, [1,2,3]);
RAB_RCcb := ContractIndices(RAB_RCde, [[2,5],[3,4]]);
P4 := evalDG(2 * rootg &t RAB_RCcb * dP[5]);

# The fifth term contracts the second derivative against the third derivative, with the free index on the third derivative raised. The coefficient is -2 * rootg & dP/dS.
RAB_RCab := ContractIndices(RAB_RCde, [[1,4],[2,5]]);
P5 := evalDG(-2 * rootg &t RAB_RCab * dP[5]);

# The sixth and seventh terms are the product of two first derivatives and a third derivative. The sixth term traces two indices of the third derivative and contracts the remaining index with a first derivative. The remaining first derivative is raised. The coefficient is 2 * rootg * d^2 P/dR dS.
RA_RB_Rcde := evalDG(RA &t RA &t Rabc);
RA_RB_RCde := RaiseLowerIndices(gIJ, RA_RB_Rcde, [3]);
RA_RB_RCcb := ContractIndices(RA_RB_RCde, [[2,5],[3,4]]);
P6 := evalDG(2 * rootg &t RA_RB_RCcb * dP[8]);

# The seventh term contracts the two first derivatives against the third derivative, raising the remaining index. The coefficient is -2 * rootg * d^2 P/dR dS.
RA_RB_RCab := ContractIndices(RA_RB_RCde, [[1,4],[2,5]]);
P7 := evalDG(-2 * rootg &t RA_RB_RCab * dP[8]);

# The eigth and ninth terms are the product of two first derivatives, a second derivative, and a third derivative. The eigth term traces two indices of the third derivative and contracts the remaining index with a first derivative. The second derivative has one raised index and contracts the other index with the last first derivative. The coefficient is 4 * rootg * d^2 P/dS^2.
RA_Rb_Rcd_Refg := evalDG(RA &t Ra &t Rab &t Rabc);
RA_Rb_RCD_REfg := RaiseLowerIndices(gIJ, RA_Rb_Rcd_Refg, [3,4,5]);
RA_Rd_RCD_REea := ContractIndices(RA_Rb_RCD_REfg, [[1,7],[2,4],[5,6]]);
P8 := evalDG(4 * rootg &t RA_Rd_RCD_REea * dP[6]);

# The ninth term contracts a first derivative with both the second and third derivatives, with the remaining index on the second derivative contracted with the third derivative. The final index on the third derivative is raised. The coefficient is -4 * rootg * d^2 P/dS^2.
RA_Rd_RCD_REac := ContractIndices(RA_Rb_RCD_REfg, [[1,6],[2,4],[3,7]]);
P9 := evalDG(-4 * rootg &t RA_Rd_RCD_REac * dP[6]);

evalDG(P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9)

end proc:

##################################################

divA2 := proc(g,PQ,vars)
local gij, R, Ra, Rab, Rabc, C, rootg, gIJ, RA, S, dP, Rab_Rcde, RAB_RCde, RAB_RCab, P1, RAB_RcDe, RAB_RbDd, P2, R_RA_Rbc, R_RA_RBc, R_RA_RBb, P3, R_RA_RBa, P4, RA_Rbc_Rde, RA_RBC_Rde, RA_RBC_Rbc, P5, RA_RbC_RDe, RA_RaC_RDc, P6, RA_Rbc_Rde_Rfg, RA_RBC_Rde_RfG, RA_RBC_Rbc_RaG, P7, RA_RBC_RDe_Rfg, RA_RBC_RDc_Rab, P8;
description "Computes the divergence of the full term quadratic in second order only in A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the Christoffel symbols of the metric.
C := Christoffel(gij);

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
S := ContractIndices(Ra &t RA, [[1,2]]);

# Compute the various derivatives of P.
dP := DP(g, PQ[1], vars);

# Construct the eight terms of divA2. The first two terms are the product of a second and a third derivative of R. The first term contracts the second derivative against the third derivative, raising the free index on the third derivative. The coefficient is 2 * rootg * dP/dS.
Rab_Rcde := evalDG(Rab &t Rabc);
RAB_RCde := RaiseLowerIndices(gIJ, Rab_Rcde, [1,2,3]);
RAB_RCab := ContractIndices(RAB_RCde, [[1,4],[2,5]]);
P1 := evalDG(2 * rootg &t RAB_RCab * dP[5]);

# The second term traces two indices of the third derivative, contracting the remaining index against the second derivative. The free index on the second derivative is raised. The coefficient is -2 * rootg * dP/dS.
RAB_RcDe := RaiseLowerIndices(gIJ, Rab_Rcde, [1,2,4]);
RAB_RbDd := ContractIndices(RAB_RcDe, [[1,3],[4,5]]);
P2 := evalDG(-2 * rootg &t RAB_RbDd * dP[5]);

# The third and fourth terms are the product of R, a first derivative, and a second derivative. The third term traces the second derivative and raises the first derivative. The coefficient is -5/3 * rootg * dP/dS.
R_RA_Rbc := evalDG(R*RA &t Rab);
R_RA_RBc := RaiseLowerIndices(gIJ, R_RA_Rbc, [2]);
R_RA_RBb := ContractIndices(R_RA_RBc, [[2,3]]);
P3 := evalDG(-5/3 * rootg &t R_RA_RBb * dP[5]);

# The fourth term contracts the first derivative against the second derivative and raises the remaining index on the second derivative. The coefficient is 4/3 * rootg * dP/dS.
R_RA_RBa := ContractIndices(R_RA_RBc, [[1,3]]);
P4 := evalDG(4/3 * rootg &t R_RA_RBa * dP[5]);

# The fifth and sixth terms are the product of a first derivative and two second derivatives. The fifth term contracts the second derivatives against each other and raises the index on the first derivative. The coefficient is 2 * rootg * d^2 P/dR dS.
RA_Rbc_Rde := evalDG(RA &t Rab &t Rab);
RA_RBC_Rde := RaiseLowerIndices(gIJ, RA_Rbc_Rde, [2,3]);
RA_RBC_Rbc := ContractIndices(RA_RBC_Rde, [[2,4],[3,5]]);
P5 := evalDG(2 * rootg &t RA_RBC_Rbc * dP[8]);

# The sixth term contracts an index from each second derivative, with one remaining index contracted against the first derivative and the other raised. The coefficient is -2 * rootg * d^2 P/dR dS.
RA_RbC_RDe := RaiseLowerIndices(gIJ, RA_Rbc_Rde, [3,4]);
RA_RaC_RDc := ContractIndices(RA_RbC_RDe, [[1,2],[3,5]]);
P6 := evalDG(-2 * rootg &t RA_RaC_RDc * dP[8]);

# The seventh and eighth terms are the product of a first derivative and three second derivatives. The seventh term contracts two of the second derivatives together, while the remaining second derivative raises one index and contracts the other against the first derivative. The coefficient is 2 * rootg * d^2 P/dS^2.
RA_Rbc_Rde_Rfg := evalDG(RA &t Rab &t Rab &t Rab);
RA_RBC_Rde_RfG := RaiseLowerIndices(gIJ, RA_Rbc_Rde_Rfg, [2,3,7]);
RA_RBC_Rbc_RaG := ContractIndices(RA_RBC_Rde_RfG, [[1,6],[2,4],[3,5]]);
P7 := evalDG(4 * rootg &t RA_RBC_Rbc_RaG * dP[6]);

# The eight term daisy chains the second derivatives together, with the one of the remaining indices contracted against the first derivative and the other is raised. The coefficient is -2 * rootg * d^2 P/dS^2.
RA_RBC_RDe_Rfg := RaiseLowerIndices(gIJ, RA_Rbc_Rde_Rfg, [2,3,4]);
RA_RBC_RDc_Rab := ContractIndices(RA_RBC_RDe_Rfg, [[2,7],[3,5],[1,6]]);
P8 := evalDG(-4 * rootg &t RA_RBC_RDc_Rab * dP[6]);

evalDG(P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8);

end proc:

##################################################

divA3 := proc(g,QP,vars)
local gij, R, Ra, Rab, Rabc, C, rootg, gIJ, RA, S, dP, RA_Rb_Rcd_Refg, RA_Rb_RCD_REfg, RA_Rd_RCD_REac, P1, RA_Rd_RCD_REea, P2, R_RA_RB_RC_Rde, R_RA_RB_RC_Rbc, P3, RA_Rbc_Rde_Rfg, RA_RBC_RDe_Rfg, RA_RBC_RDc_Rab, P4, RA_RBC_Rde_RfG, RA_RBC_Rbc_RaG, P5, RA_RB_RC_Rde_Rfg, RA_RB_RC_RDe_Rfg, RA_RB_RC_RDb_Rdc, P6, RA_RB_RC_Rde_RFg, RA_RB_RC_Rab_RFc, P7;
description "Computes the divergence of the full term quadratic in second order and first order in A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the Christoffel symbols of the metric.
C := Christoffel(gij);

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
S := ContractIndices(Ra &t RA, [[1,2]]);

# Compute the various derivatives of P.
dP := DP(g, PQ[1], vars);

# Construct the seven terms of divA3. The first and second terms are the product of two first derivatives, a second derivative, and a third derivative. The first term contracts a first derivative with both the second and third derivatives, with the remaining index on the second derivative contracted with the third derivative. The final index on the third derivative is raised. The coefficient is 4 * rootg * d^2 P/dS^2.
RA_Rb_Rcd_Refg := evalDG(RA &t Ra &t Rab &t Rabc);
RA_Rb_RCD_REfg := RaiseLowerIndices(gIJ, RA_Rb_Rcd_Refg, [3,4,5]);
RA_Rd_RCD_REac := ContractIndices(RA_Rb_RCD_REfg, [[1,6],[2,4],[3,7]]);
P1 := evalDG(4 * rootg &t RA_Rd_RCD_REac * dP[6]);

# The second term traces two indices of the third derivative and contracts the remaining index with a first derivative. The second derivative has one raised index and contracts the other index with the last first derivative. The coefficient is -4 * rootg * d^2 P/dS^2.
RA_Rd_RCD_REea := ContractIndices(RA_Rb_RCD_REfg, [[1,7],[2,4],[5,6]]);
P2 := evalDG(-4 * rootg &t RA_Rd_RCD_REea * dP[6]);

# The third term is the product of three first derivatives and a second derivatives. The second derivative is contracted against two of the first derivatives, with the remaining first derivative raised. The coefficient is -2/3 * rootg * d^2 P/dS^2
R_RA_RB_RC_Rde := evalDG(R * RA &t RA &t RA &t Rab);
R_RA_RB_RC_Rbc := ContractIndices(R_RA_RB_RC_Rde, [[2,4],[3,5]]);
P3 := evalDG(-2/3 * rootg &t R_RA_RB_RC_Rbc * dP[6]);

# The fourth and fifth terms are the product of a first derivative and three second derivatives. The fourth term daisy chains the second derivatives together, with one of the remaining indices contracted against the first derivative and the other raised. The coefficient is 4 * rootg * d^2 P/dS^2.
RA_Rbc_Rde_Rfg := evalDG(RA &t Rab &t Rab &t Rab);
RA_RBC_RDe_Rfg := RaiseLowerIndices(gIJ, RA_Rbc_Rde_Rfg, [2,3,4]);
RA_RBC_RDc_Rab := ContractIndices(RA_RBC_RDe_Rfg, [[2,7],[3,5],[1,6]]);
P4 := evalDG(4 * rootg &t RA_RBC_RDc_Rab * dP[6]);

# The fifth term contracts two of the second derivatives together, while the remaining second derivative raises one index and contracts the other against the first derivative. The coefficient is 4 * rootg * d^2 P/dS^2.
RA_RBC_Rde_RfG := RaiseLowerIndices(gIJ, RA_Rbc_Rde_Rfg, [2,3,7]);
RA_RBC_Rbc_RaG := ContractIndices(RA_RBC_Rde_RfG, [[1,6],[2,4],[3,5]]);
P5 := evalDG(-4 * rootg &t RA_RBC_Rbc_RaG * dP[6]);

# The sixth and seventh terms are the product of three first derivatives and two second derivatives. The sixth term contracts one index from each second derivative, with the remaining index on each second derivative contracted with a first derivative. The remaining first derivative is raised. The coefficient is 4 * rootg * d^3 P/dR dS^2.
RA_RB_RC_Rde_Rfg := evalDG(RA &t RA &t RA &t Rab &t Rab);
RA_RB_RC_RDe_Rfg := RaiseLowerIndices(gIJ, RA_RB_RC_Rde_Rfg, [4]);
RA_RB_RC_RDb_Rdc := ContractIndices(RA_RB_RC_RDe_Rfg, [[2,5],[3,7],[4,6]]);
P6 := evalDG(4 * rootg &t RA_RB_RC_RDb_Rdc * dP[10]);

# The seventh term contracts two first derivatives against a second derivative and the remaining first derivative against the remaining second derivative, raising the free index on this last second derivative. The coefficient is -4 * rootg * d^3 P/dR dS^2.
RA_RB_RC_Rde_RFg := RaiseLowerIndices(gIJ, RA_RB_RC_Rde_Rfg, [6]);
RA_RB_RC_Rab_RFc := ContractIndices(RA_RB_RC_Rde_RFg, [[1,4],[2,5],[3,7]]);
P7 := evalDG(-4 * rootg &t RA_RB_RC_Rab_RFc * dP[10]);

evalDG(P1 + P2 + P3 + P4 + P5 + P6 + P7)

end proc:

##################################################

divA4 := proc(g,PQ,vars)
local gij, R, Ra, Rab, Rabc, C, rootg, gIJ, RA, S, dP, RA_RB_Rcde, RA_RB_RCde, RA_RB_RCab, P1, RA_RB_RcDe, RA_RB_RbDd, P2, R_S_RA, P3, RA_Rbc_Rde, RA_RBC_Rde, RA_RBC_Rca, P4, RA_RBC_Rbc, P5, RA_RBc_RDe, RA_RBa_RDd, P6, RA_RB_RC_Rde, RA_RB_RC_Rbc, P7, S_RA_Rbc, S_RA_RbC, S_RA_RaC, P8, RA_RB_RC_Rde_Rfg, RA_RB_RC_Rde_RfG, RA_RB_RC_Rab_RcG, P9, RA_RB_RC_Rgb_RcG, P10;
description "Computes the divergence of the full term linear in second order and quadratic in first order in A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the Christoffel symbols of the metric.
C := Christoffel(gij);

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
S := ContractIndices(Ra &t RA, [[1,2]]);

# Compute the various derivatives of P.
dP := DP(g, PQ[1], vars);

# Construct the ten terms of divA4. The first two terms contain the product of two first derivatives and a third derivative. The first term contracts the two first derivatives with the third derivative and raises the free index of the third derivative. The coefficient is 2 * rootg * d^2 P/dR dS.
RA_RB_Rcde := evalDG(RA &t RA &t Rabc);
RA_RB_RCde := RaiseLowerIndices(gIJ, RA_RB_Rcde, [3]);
RA_RB_RCab := ContractIndices(RA_RB_RCde, [[1,4],[2,5]]);
P1 := evalDG(2 * rootg &t RA_RB_RCab * dP[8]);

# The second term traces two indices of the third derivative and contracts the remaining index against a first derivative. The remaining first derivative is raised. The coefficient is -2 * rootg * d^2 P/dR dS.
RA_RB_RcDe := RaiseLowerIndices(gIJ, RA_RB_Rcde, [4]);
RA_RB_RbDd := ContractIndices(RA_RB_RcDe, [[2,3],[4,5]]);
P2 := evalDG(-2 * rootg &t RA_RB_RbDd * dP[8]);

# The third term is the product of R, S, and a first derivative. The coefficient is -1/3 * rootg * d^2 P/dR dS.
R_S_RA := evalDG(R*S*RA);
P3 := evalDG(-1/3 * rootg &t R_S_RA * dP[8]);

# The fourth, fifth, and sixth terms are the product of a first derivative and two second derivatives. The fourth term contracts one index from each of the second derivatives, with one of the remaining indices contracted against the first derivative and the other raised. The coefficient is 4 * rootg * d^2 P/dR dS.
RA_Rbc_Rde := evalDG(RA &t Rab &t Rab);
RA_RBC_Rde := RaiseLowerIndices(gIJ, RA_Rbc_Rde, [2,3]);
RA_RBC_Rca := ContractIndices(RA_RBC_Rde, [[1,5],[3,4]]);
P4 := evalDG(4 * rootg &t RA_RBC_Rca * dP[8]);

# The fifth term contracts the second derivatives against each other and raises the first derivative. The coefficient is -2 * rootg * d^2 P/dR dS.
RA_RBC_Rbc := ContractIndices(RA_RBC_Rde, [[2,4],[3,5]]);
P5 := evalDG(-2 * rootg &t RA_RBC_Rbc * dP[8]);

# The sixth term traces one of the second derivatives and contracts the other with the first derivative. The free index on this second derivative is raised. The coefficient is -2 * rootg * d^2 P/dR dS.
RA_RBc_RDe := RaiseLowerIndices(gIJ, RA_Rbc_Rde, [2,4]);
RA_RBa_RDd := ContractIndices(RA_RBc_RDe, [[1,3],[4,5]]);
P6 := evalDG(-2 * rootg &t RA_RBa_RDd * dP[8]);

# The seventh term is the product of three first derivatives and a second derivative. Two of the first derivatives are contracted with the second derivative and the remaining first derivative is raised. The coefficient is 2 * rootg * d^3 P/dR^2 dS.
RA_RB_RC_Rde := evalDG(RA &t RA &t RA &t Rab);
RA_RB_RC_Rbc := ContractIndices(RA_RB_RC_Rde, [[2,4],[3,5]]);
P7 := evalDG(2 * rootg &t RA_RB_RC_Rbc * dP[9]);

# The eigth term is the product of S, a first derivative, and a second derivative. The second derivative is contracted with the first derivative and the free index is raised. The coefficient is -2 * rootg * d^3 P/dR^2 dS.
S_RA_Rbc := evalDG(S * RA &t Rab);
S_RA_RbC := RaiseLowerIndices(gIJ, S_RA_Rbc, [3]);
S_RA_RaC := ContractIndices(S_RA_RbC, [[1,2]]);
P8 := evalDG(-2 * rootg &t S_RA_RaC * dP[9]);

# The ninth and tenth terms are the product of three first derivatives and two second derivatives. The ninth term contracts all three first derivatives with the two second derivatives; the remaining free index is raised. The coefficient is 4 * rootg * d^3 P/dR dS^2.
RA_RB_RC_Rde_Rfg := evalDG(RA &t RA &t RA &t Rab &t Rab);
RA_RB_RC_Rde_RfG := RaiseLowerIndices(gIJ, RA_RB_RC_Rde_Rfg, [7]);
RA_RB_RC_Rab_RcG := ContractIndices(RA_RB_RC_Rde_RfG, [[1,4],[2,5],[3,6]]);
P9 := evalDG(4 * rootg &t RA_RB_RC_Rab_RcG * dP[10]);

# The tenth term contracts an index from each of the second derivatives and contracts the remaining free index on each with a first derivative. The remaining first derivative is raised. The coefficient is -4 * rootg * d^3 P/dR^2 dS.
RA_RB_RC_Rgb_RcG := ContractIndices(RA_RB_RC_Rde_RfG, [[2,5], [3,6],[4,7]]);
P10 := evalDG(-4 * rootg &t RA_RB_RC_Rgb_RcG * dP[10]);

evalDG(P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9 + P10)

end proc:

##################################################

divA5 := proc(g,PQ,vars)
local gij, R, Ra, Rab, Rabc, C, rootg, gIJ, RA, S, dP, dQ, R_RA, P1, RA_Rbc, RA_RBc, RA_RBb, P2, RA_RbC, RA_RaC, P3, RA_Rbc_Rde, RA_RBc_RdE, RA_RBb_RaE, P4, RA_RBC_Rde, RA_RBC_Rab, P5;
description "Computes the divergence of the full term linear in second order in A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the Christoffel symbols of the metric.
C := Christoffel(gij);

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
S := ContractIndices(Ra &t RA, [[1,2]]);

# Compute the various derivatives of P and Q.
dP := DP(g, PQ[1], vars);
dQ := DQ(g, PQ[2], vars);

# Construct the five terms of divA5. The first term is the product of R and a first derivative. The coefficient is -1/2 * rootg * (dP/dR + Q).
R_RA := evalDG(R * RA);
P1 := evalDG(-1/2 * rootg &t R_RA * (dP[2] + dQ[1]));

# The second and third terms are the product of a first and second derivative. The second term traces the second derivative and raises the first. The coefficient is rootg * (d^2 P/dR^2 + dQ/dR).
RA_Rbc := evalDG(RA &t Rab);
RA_RBc := RaiseLowerIndices(gIJ, RA_Rbc, [2]);
RA_RBb := ContractIndices(RA_RBc, [[2,3]]);
P2 := evalDG(rootg &t RA_RBb * (dP[3] + dQ[2]));

# The third term contracts the first and second derivatives, with the free index on the second derivative raised. The coefficient is -rootg * (d^2 P/dR^2 + dQ/dR).
RA_RbC := RaiseLowerIndices(gIJ, RA_Rbc, [3]);
RA_RaC := ContractIndices(RA_RbC, [[1,2]]);
P3 := evalDG(-rootg &t RA_RaC * (dP[3] + dQ[2]));

# The fourth and fifth terms are a product of a first derivative and two second derivatives. The fourth term traces one second derivative and contracts the other with the first derivative. The remaining index is raised. The coefficient is 2 * rootg * d^2 P/dR dS.
RA_Rbc_Rde := evalDG(RA &t Rab &t Rab);
RA_RBc_RdE := RaiseLowerIndices(gIJ, RA_Rbc_Rde, [2,5]);
RA_RBb_RaE := ContractIndices(RA_RBc_RdE, [[1,4],[2,3]]);
P4 := evalDG(2 * rootg &t RA_RBb_RaE * dP[8]);

# The fifth term contracts one index from each second derivative, with one free index contracted against a first derivative and the other raised. The coefficient is -2 * rootg * d^2 P/dR dS.
RA_RBC_Rde := RaiseLowerIndices(gIJ, RA_Rbc_Rde, [2,3]);
RA_RBC_Rab := ContractIndices(RA_RBC_Rde, [[1,4],[2,5]]);
P5 := evalDG(-2 * rootg &t RA_RBC_Rab * dP[8]);

evalDG(P1 + P2 + P3 + P4 + P5)

end proc:

##################################################

divA6 := proc(g,PQ,vars)
local gij, R, Ra, Rab, Rabc, C, rootg, gIJ, RA, S, dP, S_RA, P1, R_RA_Rbc, R_RA_RBc, R_RA_RBa, P2, R_RA_RBb, P3, R_S_RA, P4, R_RA_RB_RC_Rde, R_RA_RB_RC_Rbc, P5;
description "Computes the divergence of the full term quadratic in first order and linear in R in A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the Christoffel symbols of the metric.
C := Christoffel(gij);

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
S := ContractIndices(Ra &t RA, [[1,2]]);

# Compute the various derivatives of P.
dP := DP(g, PQ[1], vars);

# Construct the five terms of divA6. The first term is the product of S and a first derivative. The coefficient is 1/3 * rootg * dP/dS.
S_RA := evalDG(S * RA);
P1 := evalDG(1/3 * rootg &t S_RA * dP[5]);

# The second and third terms consists of R, a first covariant derivative of R, and a second covariant derivative. The second term contracts the first and second derivatives and raises the remaining index on the second derivative. The coefficient is 1/3 * rootg * dP/dS.
R_RA_Rbc := evalDG(R * RA &t Rab);
R_RA_RBc := RaiseLowerIndices(gIJ, R_RA_Rbc, [2]);
R_RA_RBa := ContractIndices(R_RA_RBc, [[1,3]]);
P2 := evalDG(1/3 * rootg &t R_RA_RBa * dP[5]);

# The third term traces the second derivative and raises the first index. The coefficient is 1/3 * rootg * dP/dS.
R_RA_RBb := ContractIndices(R_RA_RBc, [[2,3]]);
P3 := evalDG(1/3 * rootg &t R_RA_RBb * dP[5]);

# The fourth term is the product of R, S, and a first derivative. The coefficient is 1/3 * rootg * d^2 P/dR dS.
R_S_RA := evalDG(R * S * RA);
P4 := evalDG(1/3 * rootg &t R_S_RA * dP[8]);

# The fifth term is the product of R, three first derivatives, and one second derivative. The second derivative is contracted against two of the first derivatives and the remaining first derivative is raised. The coefficient is 2/3 * rootg * d^2 P/dS^2.
R_RA_RB_RC_Rde := evalDG(R * RA &t RA &t RA &t Rab);
R_RA_RB_RC_Rbc := ContractIndices(R_RA_RB_RC_Rde, [[2,4],[3,5]]);
P5 := evalDG(2/3 * rootg &t R_RA_RB_RC_Rbc * dP[6]);

evalDG(P1 + P2 + P3 + P4 + P5)

end proc:

##################################################

divA7 := proc(g,PQ,vars)
local gij, R, Ra, Rab, Rabc, C, rootg, gIJ, RA, S, dP, dQ, RA_Rbc, RA_RbC, RA_RaC, P1, RA_RBc, RA_RBb, P2, S_RA_Rbc, S_RA_RBc, S_RA_RBa, P3, RA_RB_RC_Rde, RA_RB_RC_Rbc, P4;
description "Computes the divergence of the full term quadratic in first order in A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the Christoffel symbols of the metric.
C := Christoffel(gij);

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
S := ContractIndices(Ra &t RA, [[1,2]]);

# Compute the various derivatives of P and Q.
dP := DP(g, PQ[1], vars);
dQ := DQ(g, PQ[2], vars);

# Construct the four terms of divA7. The first and second terms are the product of a first and second derivative. The first term contracts the first and second derivatives, with the free index on the second derivative raised. The coefficient is rootg * (d^2 P/dR^2 + dQ/dR).
RA_Rbc := evalDG(RA &t Rab);
RA_RbC := RaiseLowerIndices(gIJ, RA_Rbc, [3]);
RA_RaC := ContractIndices(RA_RbC, [[1,2]]);
P1 := evalDG(rootg &t RA_RaC * (dP[3] + dQ[2]));

# The second term traces the second derivative and raises the first. The coefficient is -rootg * (d^2 P/dR^2 + dQ/dR).
RA_RBc := RaiseLowerIndices(gIJ, RA_Rbc, [2]);
RA_RBb := ContractIndices(RA_RBc, [[2,3]]);
P2 := evalDG(-rootg &t RA_RBb * (dP[3] + dQ[2]));

# The third term is the product of S, a first derivative, and a second derivative. The second derivative is contracted against the first derivative, with the free index raised. The coefficient is 2 * rootg * d^3 P/dR^2 dS.
S_RA_Rbc := evalDG(S * RA &t Rab);
S_RA_RBc := RaiseLowerIndices(gIJ, S_RA_Rbc, [3]);
S_RA_RBa := ContractIndices(S_RA_RBc, [[1,2]]);
P3 := evalDG(2 * rootg &t S_RA_RBa * dP[9]);

# The fourth term is the product of three first derivatives and a seoncd derivative. The second derivative is contracted against two first derivatives and the remaining first derivative is raised. The coefficient is -2 * rootg * d^3 P/dR^2 dS.
RA_RB_RC_Rde := evalDG(RA &t RA &t RA &t Rab);
RA_RB_RC_Rbc := ContractIndices(RA_RB_RC_Rde, [[2,4],[3,5]]);
P4 := evalDG(-2 * rootg &t RA_RB_RC_Rbc * dP[9]);

evalDG(P1 + P2 + P3 + P4)

end proc:

##################################################

divA8 := proc(g,PQ,vars)
local gij, R, Ra, Rab, Rabc, C, rootg, gIJ, RA, S, dP, P1, R_RA, P2, R_RA_Rbc, R_RA_RBc, R_RA_RBa, P3;
description "Computes the divergence of the full term linear in R in A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the Christoffel symbols of the metric.
C := Christoffel(gij);

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
S := ContractIndices(Ra &t RA, [[1,2]]);

# Compute the various derivatives of P.
dP := DP(g, PQ[1], vars);

# Construct the three terms of divA8. The first term is a first derivative with coefficient 1/2 * rootg * P.
P1 := evalDG(1/2 * rootg &t RA * dP[1]);

# The second term is the product of R and a first derivative. The coefficient is 1/2 * rootg * dP/dR.
R_RA := evalDG(R * RA);
P2 := evalDG(1/2 * rootg &t R_RA * dP[2]);

# The third term consists of R, a first covariant derivative of R, and a second covariant derivative. Contract the first and second derivatives while raising the remaining index on the second derivative. The coefficient is rootg * dP/dS.
R_RA_Rbc := evalDG(R * RA &t Rab);
R_RA_RBc := RaiseLowerIndices(gIJ, R_RA_Rbc, [2]);
R_RA_RBa := ContractIndices(R_RA_RBc, [[1,3]]);
P3 := evalDG(rootg &t R_RA_RBa * dP[5]);

evalDG(P1 + P2 + P3)

end proc:

##################################################

PartialSum2 := proc(g,PQ,vars)
local gij, R, Ra, Rab, Rabc, C, rootg, gIJ, RA, S, dP, R_RA_Rbc, R_RA_RbC, R_RA_RaC, P1, R_RA_RBc, R_RA_RBb, P2, S_RA, P3, RA_RB_Rcde, RA_RB_RCde, RA_RB_RCcb, P4, RA_RB_RCab, P5, RA_Rb_Rcd_Refg, RA_Rb_RCD_REfg, RA_Rd_RCD_REea, P6, RA_Rd_RCD_REac, P7, RA_Rbc_Rde, RA_RBC_Rde, RA_RBC_Rbc, P8, RA_RbC_RDe, RA_RaC_RDc, P9, RA_Rbc_Rde_Rfg, RA_RBC_Rde_RfG, RA_RBC_Rbc_RaG, P10, RA_RBC_RDe_Rfg, RA_RBC_RDc_Rab, P11;
description "Computes the divergence of the sum of the first two terms in A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the Christoffel symbols of the metric.
C := Christoffel(gij);

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
S := ContractIndices(Ra &t RA, [[1,2]]);

# Compute the various derivatives of P.
dP := DP(g, PQ[1], vars);

# Construct the eleven terms of PartialSum2. The first two terms are the product of R, a first derivative, and a second derivative. The first term contracts the second derivative with the first derivative, raising the free index. The coefficicent is -4/3 * rootg * dP/dS.
R_RA_Rbc := evalDG(R * RA &t Rab);
R_RA_RbC := RaiseLowerIndices(gIJ, R_RA_Rbc, [3]);
R_RA_RaC := ContractIndices(R_RA_RbC, [[1,2]]);
P1 := evalDG(-4/3 * rootg &t R_RA_RaC * dP[5]);

# The second term traces the second derivative and raises the first derivative. The coefficient is -1/3 * rootg * dP/dS.
R_RA_RBc := RaiseLowerIndices(gIJ, R_RA_Rbc, [2]);
R_RA_RBb := ContractIndices(R_RA_RBc, [[2,3]]);
P2 := evalDG(-1/3 * rootg &t R_RA_RBb * dP[5]);

# The third term is the product of S and a first derivative, with a coefficient of -1/3 * rootg * dP/dS.
S_RA := evalDG(S * RA);
P3 := evalDG(-1/3 * rootg &t S_RA * dP[5]);

# The fourth and fifth terms are the product of two first derivatives and a third derivative. The fourth term traces two indices of the third derivative and contracts the remaining index with a first derivative. The remaining first derivative is raised. The coefficient is 2 * rootg * d^2 P/dR dS.
RA_RB_Rcde := evalDG(RA &t RA &t Rabc);
RA_RB_RCde := RaiseLowerIndices(gIJ, RA_RB_Rcde, [3]);
RA_RB_RCcb := ContractIndices(RA_RB_RCde, [[2,5],[3,4]]);
P4 := evalDG(2 * rootg &t RA_RB_RCcb * dP[8]);

# The fifth term contracts the two first derivatives against the third derivative, raising the remaining index. The coefficient is -2 * rootg * d^2 P/dR dS.
RA_RB_RCab := ContractIndices(RA_RB_RCde, [[1,4],[2,5]]);
P5 := evalDG(-2 * rootg &t RA_RB_RCab * dP[8]);

# The sixth and seventh terms are the product of two first derivatives, a second derivative, and a third derivative. The sixth term traces two indices of the third derivative and contracts the remaining index with a first derivative. The second derivative has one raised index and contracts the other index with the last first derivative. The coefficient is 4 * rootg * d^2 P/dS^2.
RA_Rb_Rcd_Refg := evalDG(RA &t Ra &t Rab &t Rabc);
RA_Rb_RCD_REfg := RaiseLowerIndices(gIJ, RA_Rb_Rcd_Refg, [3,4,5]);
RA_Rd_RCD_REea := ContractIndices(RA_Rb_RCD_REfg, [[1,7],[2,4],[5,6]]);
P6 := evalDG(4 * rootg &t RA_Rd_RCD_REea * dP[6]);

# The seventh term contracts a first derivative with both the second and third derivatives, with the remaining index on the second derivative contracted with the third derivative. The final index on the third derivative is raised. The coefficient is -4 * rootg * d^2 P/dS^2.
RA_Rd_RCD_REac := ContractIndices(RA_Rb_RCD_REfg, [[1,6],[2,4],[3,7]]);
P7 := evalDG(-4 * rootg &t RA_Rd_RCD_REac * dP[6]);

# The eigth and ninth terms are the product of a first derivative and two second derivatives. The eigth term contracts the second derivatives against each other and raises the index on the first derivative. The coefficient is 2 * rootg * d^2 P/dR dS.
RA_Rbc_Rde := evalDG(RA &t Rab &t Rab);
RA_RBC_Rde := RaiseLowerIndices(gIJ, RA_Rbc_Rde, [2,3]);
RA_RBC_Rbc := ContractIndices(RA_RBC_Rde, [[2,4],[3,5]]);
P8 := evalDG(2 * rootg &t RA_RBC_Rbc * dP[8]);

# The ninth term contracts an index from each second derivative, with one remaining index contracted against the first derivative and the other raised. The coefficient is -2 * rootg * d^2 P/dR dS.
RA_RbC_RDe := RaiseLowerIndices(gIJ, RA_Rbc_Rde, [3,4]);
RA_RaC_RDc := ContractIndices(RA_RbC_RDe, [[1,2],[3,5]]);
P9 := evalDG(-2 * rootg &t RA_RaC_RDc * dP[8]);

# The tenth and eleventh terms are the product of a first derivative and three second derivatives. The tenth term contracts two of the second derivatives together, while the remaining second derivative raises one index and contracts the other against the first derivative. The coefficient is 2 * rootg * d^2 P/dS^2.
RA_Rbc_Rde_Rfg := evalDG(RA &t Rab &t Rab &t Rab);
RA_RBC_Rde_RfG := RaiseLowerIndices(gIJ, RA_Rbc_Rde_Rfg, [2,3,7]);
RA_RBC_Rbc_RaG := ContractIndices(RA_RBC_Rde_RfG, [[1,6],[2,4],[3,5]]);
P10 := evalDG(4 * rootg &t RA_RBC_Rbc_RaG * dP[6]);

# The eleventh term daisy chains the second derivatives together, with one of the remaining indices contracted against the first derivative and the other raised. The coefficient is -2 * rootg * d^2 P/dS^2.
RA_RBC_RDe_Rfg := RaiseLowerIndices(gIJ, RA_Rbc_Rde_Rfg, [2,3,4]);
RA_RBC_RDc_Rab := ContractIndices(RA_RBC_RDe_Rfg, [[2,7],[3,5],[1,6]]);
P11 := evalDG(-4 * rootg &t RA_RBC_RDc_Rab * dP[6]);

evalDG(P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9 + P10 + P11)

end proc:

##################################################

PartialSum3 := proc(g,PQ,vars)
local gij, R, Ra, Rab, Rabc, C, rootg, gIJ, RA, S, dP, R_RA_Rbc, R_RA_RbC, R_RA_RaC, P1, R_RA_RBc, R_RA_RBb, P2, S_RA, P3, R_RA_RB_RC_Rde, R_RA_RB_RC_Rbc, P4, RA_Rbc_Rde, RA_RBC_Rde, RA_RBC_Rbc, P5, RA_RbC_RDe, RA_RaC_RDc, P6, RA_RB_RC_Rde_Rfg, RA_RB_RC_RDe_Rfg, RA_RB_RC_RDb_Rdc, P7, RA_RB_RC_Rde_RFg, RA_RB_RC_Rab_RFc, P8, RA_RB_Rcde, RA_RB_RCde, RA_RB_RCcb, P9, RA_RB_RCab, P10;
description "Computes the divergence of the sum of the first three terms in A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the Christoffel symbols of the metric.
C := Christoffel(gij);

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
S := ContractIndices(Ra &t RA, [[1,2]]);

# Compute the various derivatives of P.
dP := DP(g, PQ[1], vars);

# Construct the ten terms of PartialSum3. The first two terms are the product of R, a first derivative, and a second derivative. The first term contracts the second derivative with the first derivative, raising the free index. The coefficicent is -4/3 * rootg * dP/dS.
R_RA_Rbc := evalDG(R * RA &t Rab);
R_RA_RbC := RaiseLowerIndices(gIJ, R_RA_Rbc, [3]);
R_RA_RaC := ContractIndices(R_RA_RbC, [[1,2]]);
P1 := evalDG(-4/3 * rootg &t R_RA_RaC * dP[5]);

# The second term traces the second derivative and raises the first derivative. The coefficient is -1/3 * rootg * dP/dS.
R_RA_RBc := RaiseLowerIndices(gIJ, R_RA_Rbc, [2]);
R_RA_RBb := ContractIndices(R_RA_RBc, [[2,3]]);
P2 := evalDG(-1/3 * rootg &t R_RA_RBb * dP[5]);

# The third term is the product of S and a first derivative, with a coefficient of -1/3 * rootg * dP/dS.
S_RA := evalDG(S * RA);
P3 := evalDG(-1/3 * rootg &t S_RA * dP[5]);

# The fourth term is the product of three first derivatives and a second derivatives. The second derivative is contracted against two of the first derivatives, with the remaining first derivative raised. The coefficient is -2/3 * rootg * d^2 P/dS^2
R_RA_RB_RC_Rde := evalDG(R * RA &t RA &t RA &t Rab);
R_RA_RB_RC_Rbc := ContractIndices(R_RA_RB_RC_Rde, [[2,4],[3,5]]);
P4 := evalDG(-2/3 * rootg &t R_RA_RB_RC_Rbc * dP[6]);

# The fifth and sixth terms are the product of a first derivative and two second derivatives. The fifth term contracts the second derivatives against each other and raises the index on the first derivative. The coefficient is 2 * rootg * d^2 P/dR dS.
RA_Rbc_Rde := evalDG(RA &t Rab &t Rab);
RA_RBC_Rde := RaiseLowerIndices(gIJ, RA_Rbc_Rde, [2,3]);
RA_RBC_Rbc := ContractIndices(RA_RBC_Rde, [[2,4],[3,5]]);
P5 := evalDG(2 * rootg &t RA_RBC_Rbc * dP[8]);

# The sixth term contracts an index from each second derivative, with one remaining index contracted against the first derivative and the other raised. The coefficient is -2 * rootg * d^2 P/dR dS.
RA_RbC_RDe := RaiseLowerIndices(gIJ, RA_Rbc_Rde, [3,4]);
RA_RaC_RDc := ContractIndices(RA_RbC_RDe, [[1,2],[3,5]]);
P6 := evalDG(-2 * rootg &t RA_RaC_RDc * dP[8]);

# The seventh and eigth terms are the product of three first derivatives and two second derivatives. The seventh term contracts one index from each second derivative, with the remaining index on each second derivative contracted with a first derivative. The remaining first derivative is raised. The coefficient is 4 * rootg * d^3 P/dR dS^2.
RA_RB_RC_Rde_Rfg := evalDG(RA &t RA &t RA &t Rab &t Rab);
RA_RB_RC_RDe_Rfg := RaiseLowerIndices(gIJ, RA_RB_RC_Rde_Rfg, [4]);
RA_RB_RC_RDb_Rdc := ContractIndices(RA_RB_RC_RDe_Rfg, [[2,5],[3,7],[4,6]]);
P7 := evalDG(4 * rootg &t RA_RB_RC_RDb_Rdc * dP[10]);

# The eighth term contracts two first derivatives against a second derivative and the remaining first derivative against the remaining second derivative, raising the free index on this last second derivative. The coefficient is -4 * rootg * d^3 P/dR dS^2.
RA_RB_RC_Rde_RFg := RaiseLowerIndices(gIJ, RA_RB_RC_Rde_Rfg, [6]);
RA_RB_RC_Rab_RFc := ContractIndices(RA_RB_RC_Rde_RFg, [[1,4],[2,5],[3,7]]);
P8 := evalDG(-4 * rootg &t RA_RB_RC_Rab_RFc * dP[10]);

# The ninth and tenth terms are the product of two first derivatives and a third derivative. The ninth term traces two indices of the third derivative and contracts the remaining index with a first derivative. The remaining first derivative is raised. The coefficient is 2 * rootg * d^2 P/dR dS.
RA_RB_Rcde := evalDG(RA &t RA &t Rabc);
RA_RB_RCde := RaiseLowerIndices(gIJ, RA_RB_Rcde, [3]);
RA_RB_RCcb := ContractIndices(RA_RB_RCde, [[2,5],[3,4]]);
P9 := evalDG(2 * rootg &t RA_RB_RCcb * dP[8]);

# The tenth term contracts the two first derivatives against the third derivative, raising the remaining index. The coefficient is -2 * rootg * d^2 P/dR dS.
RA_RB_RCab := ContractIndices(RA_RB_RCde, [[1,4],[2,5]]);
P10 := evalDG(-2 * rootg &t RA_RB_RCab * dP[8]);

evalDG(P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9 + P10)

end proc:

##################################################

PartialSum4 := proc(g,PQ,vars)
local gij, R, Ra, Rab, Rabc, C, rootg, gIJ, RA, S, dP, R_RA_Rbc, R_RA_RBc, R_RA_RBa, P1, R_RA_RBb, P2, S_RA, P3, R_RA_RB_RC_Rde, R_RA_RB_RC_Rbc, P4, RA_Rbc_Rde, RA_RBC_Rde, RA_RBC_Rca, P5, RA_RBc_RDe, RA_RBa_RDd, P6, R_S_RA, P7, RA_RB_RC_Rde, RA_RB_RC_Rbc, P8, S_RA_Rbc, S_RA_RBc, S_RA_RBa, P9;
description "Computes the divergence of the sum of the first four terms in A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the Christoffel symbols of the metric.
C := Christoffel(gij);

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
S := ContractIndices(Ra &t RA, [[1,2]]);

# Compute the various derivatives of P.
dP := DP(g, PQ[1], vars);

# Construct the nine terms of PartialSum4. The first two terms consists of R, a first covariant derivative of R, and a second covariant derivative. The first term contracts the first and second derivatives and raises the remaining index on the second derivative. The coefficient is -4/3 * rootg * dP/dS.
R_RA_Rbc := evalDG(R * RA &t Rab);
R_RA_RBc := RaiseLowerIndices(gIJ, R_RA_Rbc, [2]);
R_RA_RBa := ContractIndices(R_RA_RBc, [[1,3]]);
P1 := evalDG(-4/3 * rootg &t R_RA_RBa * dP[5]);

# The second term traces the second derivative and raises the first index. The coefficient is -1/3 * rootg * dP/dS.
R_RA_RBb := ContractIndices(R_RA_RBc, [[2,3]]);
P2 := evalDG(-1/3 * rootg &t R_RA_RBb * dP[5]);

# The third term is the product of S and a raised covariant derivative. The coefficient is -1/3 * rootg * dP/dS.
S_RA := evalDG(S * RA);
P3 := evalDG(-1/3 * rootg &t S_RA * dP[5]);

# The fourth term is the product of R, three first derivatives, and one second derivative. The second derivative is contracted against two of the first derivatives and the remaining first derivative is raised. The coefficient is -2/3 * rootg * d^2 P/dS^2.
R_RA_RB_RC_Rde := evalDG(R * RA &t RA &t RA &t Rab);
R_RA_RB_RC_Rbc := ContractIndices(R_RA_RB_RC_Rde, [[2,4],[3,5]]);
P4 := evalDG(-2/3 * rootg &t R_RA_RB_RC_Rbc * dP[6]);

# The fifth and sixth terms involve a first derivative and two second derivatives. The fifth term contracts one index on each of the two second derivatives against each other, with one of the remaining indices contracted against the first derivative and the other raised. The coefficient is 2 * rootg * d^2 P/dR dS.
RA_Rbc_Rde := evalDG(RA &t Rab &t Rab);
RA_RBC_Rde := RaiseLowerIndices(gIJ, RA_Rbc_Rde, [2,3]);
RA_RBC_Rca := ContractIndices(RA_RBC_Rde, [[1,5],[3,4]]);
P5 := evalDG(2 * rootg &t RA_RBC_Rca * dP[8]);

# The sixth term traces one of the second derivatives and contracts the other second derivative against the first derivative. The free index is raised. The coefficient is -2 * rootg * d^2 P/dR dS.
RA_RBc_RDe := RaiseLowerIndices(gIJ, RA_Rbc_Rde, [2,4]);
RA_RBa_RDd := ContractIndices(RA_RBc_RDe, [[1,3],[4,5]]);
P6 := evalDG(-2 * rootg &t RA_RBa_RDd * dP[8]);

# The seventh term is the product of R, S, and a raised first derivative. The coefficient is -1/3 * rootg * d^2 P/dR dS.
R_S_RA := evalDG(R * S * RA);
P7 := evalDG(-1/3 * rootg &t R_S_RA * dP[8]);

# The eighth term is the product of three first derivatives and a seoncd derivative. The second derivative is contracted against two first derivatives and the remaining first derivative is raised. The coefficient is 2 * rootg * d^3 P/dR^2 dS.
RA_RB_RC_Rde := evalDG(RA &t RA &t RA &t Rab);
RA_RB_RC_Rbc := ContractIndices(RA_RB_RC_Rde, [[2,4],[3,5]]);
P8 := evalDG(2 * rootg &t RA_RB_RC_Rbc * dP[9]);

# The ninth term is the product of S, a first derivative, and a second derivative. The second derivative is contracted against the first derivative, with the free index raised. The coefficient is -2 * rootg * d^3 P/dR^2 dS.
S_RA_Rbc := evalDG(S * RA &t Rab);
S_RA_RBc := RaiseLowerIndices(gIJ, S_RA_Rbc, [3]);
S_RA_RBa := ContractIndices(S_RA_RBc, [[1,2]]);
P9 := evalDG(-2 * rootg &t S_RA_RBa * dP[9]);

evalDG(P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9)

end proc:

##################################################

PartialSum5 := proc(g,PQ,vars)
local gij, R, Ra, Rab, Rabc, C, rootg, gIJ, RA, S, dP, dQ, R_RA_Rbc, R_RA_RBc, R_RA_RBa, P1, R_RA_RBb, P2, S_RA, P3, R_RA_RB_RC_Rde, R_RA_RB_RC_Rbc, P4, R_S_RA, P5, RA_RB_RC_Rde, RA_RB_RC_Rbc, P6, S_RA_Rbc, S_RA_RBc, S_RA_RBa, P7, R_RA, P8, RA_Rbc, RA_RBc, RA_RBb, P9, RA_RbC, RA_RaC, P10;
description "Computes the divergence of the sum of the first five terms in A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the Christoffel symbols of the metric.
C := Christoffel(gij);

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
S := ContractIndices(Ra &t RA, [[1,2]]);

# Compute the various derivatives of P and Q.
dP := DP(g, PQ[1], vars);
dQ := DQ(g, PQ[2], vars);

# Construct the ten terms of PartialSum5. The first two terms consists of R, a first covariant derivative of R, and a second covariant derivative. The first term contracts the first and second derivatives and raises the remaining index on the second derivative. The coefficient is -4/3 * rootg * dP/dS.
R_RA_Rbc := evalDG(R * RA &t Rab);
R_RA_RBc := RaiseLowerIndices(gIJ, R_RA_Rbc, [2]);
R_RA_RBa := ContractIndices(R_RA_RBc, [[1,3]]);
P1 := evalDG(-4/3 * rootg &t R_RA_RBa * dP[5]);

# The second term traces the second derivative and raises the first index. The coefficient is -1/3 * rootg * dP/dS.
R_RA_RBb := ContractIndices(R_RA_RBc, [[2,3]]);
P2 := evalDG(-1/3 * rootg &t R_RA_RBb * dP[5]);

# The third term is the product of S and a raised covariant derivative. The coefficient is -1/3 * rootg * dP/dS.
S_RA := evalDG(S * RA);
P3 := evalDG(-1/3 * rootg &t S_RA * dP[5]);

# The fourth term is the product of R, three first derivatives, and one second derivative. The second derivative is contracted against two of the first derivatives and the remaining first derivative is raised. The coefficient is -2/3 * rootg * d^2 P/dS^2.
R_RA_RB_RC_Rde := evalDG(R * RA &t RA &t RA &t Rab);
R_RA_RB_RC_Rbc := ContractIndices(R_RA_RB_RC_Rde, [[2,4],[3,5]]);
P4 := evalDG(-2/3 * rootg &t R_RA_RB_RC_Rbc * dP[6]);

# The fifth term is the product of R, S, and a first derivative. The coefficient is -1/3 * rootg * d^2 P/dR dS.
R_S_RA := evalDG(R * S * RA);
P5 := evalDG(-1/3 * rootg &t R_S_RA * dP[8]);

# The sixth term is the product of three first derivatives and a seoncd derivative. The second derivative is contracted against two first derivatives and the remaining first derivative is raised. The coefficient is 2 * rootg * d^3 P/dR^2 dS.
RA_RB_RC_Rde := evalDG(RA &t RA &t RA &t Rab);
RA_RB_RC_Rbc := ContractIndices(RA_RB_RC_Rde, [[2,4],[3,5]]);
P6 := evalDG(2 * rootg &t RA_RB_RC_Rbc * dP[9]);

# The seventh term is the product of S, a first derivative, and a second derivative. The second derivative is contracted against the first derivative, with the free index raised. The coefficient is -2 * rootg * d^3 P/dR^2 dS.
S_RA_Rbc := evalDG(S * RA &t Rab);
S_RA_RBc := RaiseLowerIndices(gIJ, S_RA_Rbc, [3]);
S_RA_RBa := ContractIndices(S_RA_RBc, [[1,2]]);
P7 := evalDG(-2 * rootg &t S_RA_RBa * dP[9]);

# The eigth term is the product of R and a first derivative. The coefficient is -1/2 * rootg * (dP/dR + Q).
R_RA := evalDG(R * RA);
P8 := evalDG(-1/2 * rootg &t R_RA * (dP[2] + dQ[1]));

# The ninth and tenth terms are the product of a first and second derivative. The ninth term traces the second derivative and raises the first. The coefficient is rootg * (d^2 P/dR^2 + dQ/dR).
RA_Rbc := evalDG(RA &t Rab);
RA_RBc := RaiseLowerIndices(gIJ, RA_Rbc, [2]);
RA_RBb := ContractIndices(RA_RBc, [[2,3]]);
P9 := evalDG(rootg &t RA_RBb * (dP[3] + dQ[2]));

# The tenth term contracts the first and second derivatives, with the free index on the second derivative raised. The coefficient is -rootg * (d^2 P/dR^2 + dQ/dR).
RA_RbC := RaiseLowerIndices(gIJ, RA_Rbc, [3]);
RA_RaC := ContractIndices(RA_RbC, [[1,2]]);
P10 := evalDG(-rootg &t RA_RaC * (dP[3] + dQ[2]));

evalDG(P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9 + P10)

end proc:

##################################################

PartialSum6 := proc(g,PQ,vars)
local gij, R, Ra, Rab, Rabc, C, rootg, gIJ, RA, S, dP, dQ, R_RA_Rbc, R_RA_RBc, R_RA_RBa, P1, RA_RB_RC_Rde, RA_RB_RC_Rbc, P2, S_RA_Rbc, S_RA_RBc, S_RA_RBa, P3, R_RA, P4, RA_Rbc, RA_RBc, RA_RBb, P5, RA_RbC, RA_RaC, P6;
description "Computes the divergence of the sum of the first six terms in A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the Christoffel symbols of the metric.
C := Christoffel(gij);

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
S := ContractIndices(Ra &t RA, [[1,2]]);

# Compute the various derivatives of P and Q.
dP := DP(g, PQ[1], vars);
dQ := DQ(g, PQ[2], vars);

# Construct the six terms of PartialSum6. The first term consists of R, a first covariant derivative of R, and a second covariant derivative. Contract the first and second derivatives while raising the remaining index on the second derivative. The coefficient is -rootg * dP/dS.
R_RA_Rbc := evalDG(R * RA &t Rab);
R_RA_RBc := RaiseLowerIndices(gIJ, R_RA_Rbc, [2]);
R_RA_RBa := ContractIndices(R_RA_RBc, [[1,3]]);
P1 := evalDG(-rootg &t R_RA_RBa * dP[5]);

# The second term is the product of three first derivatives and a seoncd derivative. The second derivative is contracted against two first derivatives and the remaining first derivative is raised. The coefficient is 2 * rootg * d^3 P/dR^2 dS.
RA_RB_RC_Rde := evalDG(RA &t RA &t RA &t Rab);
RA_RB_RC_Rbc := ContractIndices(RA_RB_RC_Rde, [[2,4],[3,5]]);
P2 := evalDG(2 * rootg &t RA_RB_RC_Rbc * dP[9]);

# The third term is the product of S, a first derivative, and a second derivative. The second derivative is contracted against the first derivative, with the free index raised. The coefficient is -2 * rootg * d^3 P/dR^2 dS.
S_RA_Rbc := evalDG(S * RA &t Rab);
S_RA_RBc := RaiseLowerIndices(gIJ, S_RA_Rbc, [3]);
S_RA_RBa := ContractIndices(S_RA_RBc, [[1,2]]);
P3 := evalDG(-2 * rootg &t S_RA_RBa * dP[9]);

# The fourth term is the product of R and a first derivative. The coefficient is -1/2 * rootg * (dP/dR + Q).
R_RA := evalDG(R * RA);
P4 := evalDG(-1/2 * rootg &t R_RA * (dP[2] + dQ[1]));

# The fifth and sixth terms are the product of a first and second derivative. The fifth term traces the second derivative and raises the first. The coefficient is rootg * (d^2 P/dR^2 + dQ/dR).
RA_Rbc := evalDG(RA &t Rab);
RA_RBc := RaiseLowerIndices(gIJ, RA_Rbc, [2]);
RA_RBb := ContractIndices(RA_RBc, [[2,3]]);
P5 := evalDG(rootg &t RA_RBb * (dP[3] + dQ[2]));

# The sixth term contracts the first and second derivatives, with the free index on the second derivative raised. The coefficient is -rootg * (d^2 P/dR^2 + dQ/dR).
RA_RbC := RaiseLowerIndices(gIJ, RA_Rbc, [3]);
RA_RaC := ContractIndices(RA_RbC, [[1,2]]);
P6 := evalDG(-rootg &t RA_RaC * (dP[3] + dQ[2]));

evalDG(P1 + P2 + P3 + P4 + P5 + P6)

end proc:

##################################################

PartialSum7 := proc(g,PQ,vars)
local gij, R, Ra, Rab, Rabc, C, rootg, gIJ, RA, S, dP, dQ, R_RA_Rbc, R_RA_RBc, R_RA_RBa, P1, R_RA, P2;
description "Computes the divergence of the sum of the first seven terms in A.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(Init(g));

# Compute the Christoffel symbols of the metric.
C := Christoffel(gij);

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# Raise the index of the first covariant derivative of the Ricci scalar.
RA := RaiseLowerIndices(gIJ,Ra,[1]);

# Compute S = Ra_RA.
S := ContractIndices(Ra &t RA, [[1,2]]);

# Compute the various derivatives of P and Q.
dP := DP(g, PQ[1], vars);
dQ := DQ(g, PQ[2], vars);

# Construct the two terms of PartialSum7. The first term consists of R, a first covariant derivative of R, and a second covariant derivative. Contract the first and second derivatives while raising the remaining index on the second derivative. The coefficient is -rootg * dP/S.
R_RA_Rbc := evalDG(R * RA &t Rab);
R_RA_RBc := RaiseLowerIndices(gIJ, R_RA_Rbc, [2]);
R_RA_RBa := ContractIndices(R_RA_RBc, [[1,3]]);
P1 := evalDG(-rootg &t R_RA_RBa * dP[5]);

# The second term is the product of R and a first derivative. The coefficient is -1/2 * rootg * (dP/dR + Q).
R_RA := evalDG(R * RA);
P2 := evalDG(-1/2 * rootg &t R_RA * (dP[2] + dQ[1]));

evalDG(P1 + P2)

end proc:

##################################################


end module: