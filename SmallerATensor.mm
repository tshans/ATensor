ATensor := module()

description "A package containing commands relating to the fifth order symmetric (2,0) tensor density that is not divergence-free.";
	option package;
	export Init, Div, B1, B2, B3, B4, B5, B6, B7, B8, divB1, divB2, divB3, divB4, divB5, divB6, divB7, divB8;

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

B1 := proc(tensors)
local gij, R, Ra, Rab, Rabc, rootg, gIJ, RA, RAbc, RAac, gIJ_RAac, gIJ_RAac_RD, gIJ_RAac_RC, RIJc, RIJc_RD, RIJc_RC;
description "Computes the term linear in third order derivatives in the tensor A from a list containing the metric, Ricci scalar, and the first three symmetrized covariant derivatives of the Ricci scalar.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(tensors);

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

B2 := proc(tensors)
local gij, R, Ra, Rab, Rabc, rootg, gIJ, Rab_Rcd, Rab_RcD, Rab_RcB, Rab_RCB, Rab_RAB, gIJ_Rab_RAB, RIb_RcB, RIb_RJB;
description "Computes the term quadratic in second order derivatives only in the tensor A from a list containing the metric, Ricci scalar, and the first three symmetrized covariant derivatives of the Ricci scalar.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(tensors);

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

B3 := proc(tensors)
local gij, R, Ra, Rab, Rabc, rootg, gIJ, RA, Rab_Rcd, Rab_Rcd_RE_RF, Rab_Rcd_RB_RD, Rab_RCd_RB_RD, Rab_RAd_RB_RD, gIJ_Rab_RAd_RB_RD, RIb_Rcd_RB_RD, RIb_RJd_RB_RD;
description "Computes the term quadratic in second order and first order derivatives in the tensor A from a list containing the metric, Ricci scalar, and the first three symmetrized covariant derivatives of the Ricci scalar.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(tensors);

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

B4 := proc(tensors)
local gij, R, Ra, Rab, Rabc, rootg, gIJ, RA, Rab_Rc_RD, Rab_Rc_RB, Rab_RC_RB, Rab_RA_RB, gIJ_Rab_RA_RB, RIb_Rc_RB, RIb_RJ_RB, sym_RIb_RJ_RB;
description "Computes the term quadratic in first order and linear in second order derivatives in the tensor A from a list containing the metric, Ricci scalar, and the first three symmetrized covariant derivatives of the Ricci scalar.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(tensors);

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

B5 := proc(tensors)
local gij, R, Ra, Rab, Rabc, rootg, gIJ, RAb, RAa, gIJ_RAa, RIb, RIJ;
description "Computes the term linear in second order derivatives in the tensor A from a list containing the metric, Ricci scalar, and the first three symmetrized covariant derivatives of the Ricci scalar.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(tensors);

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

B6 := proc(tensors)
local gij, R, Ra, Rab, Rabc, rootg, gIJ, RA, R_RI_RJ;
description "Computes the term quadratic in first order derivatives and linear in the Ricci scalar in the tensor A from a list containing the metric, Ricci scalar, and the first three symmetrized covariant derivatives of the Ricci scalar.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(tensors);

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

B7 := proc(tensors)
local gij, R, Ra, Rab, Rabc, rootg, gIJ, RA, Ra_RB, Ra_RA, gIJ_S, RI_RJ;
description "Computes the term quadratic in first order derivatives in the tensor A from a list containing the metric, Ricci scalar, and the first three symmetrized covariant derivatives of the Ricci scalar.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(tensors);

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

B8 := proc(tensors)
local gij, R, Ra, Rab, Rabc, rootg, gIJ;
description "Computes the term linear in the Ricci scalar in the tensor A from a list containing the metric, Ricci scalar, and the first three symmetrized covariant derivatives of the Ricci scalar.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(tensors);

# Compute the square root of the determinant of the metric.
rootg := MetricDensity(gij,1);

# Compute the inverse metric for raising indices.
gIJ := InverseMetric(gij);

# There is one term in B8, consisting of the Ricci tensor and an inverse metric multiplied by a factor of 1/2*rootg.
evalDG(1/2*R*rootg &t gIJ)

end proc:

##################################################

divB1 := proc(tensors) 
local gij, R, Ra, Rab, Rabc, gIJ, rootg, RA, Ra_RB, S, R_Rab_RC, R_RIb_RC, R_RIb_RB, R_RAa_RI, S_RI, Rabc_Rde, RAbc_RDI, RAac_RCI, RIBC_Rde, RIBC_Rbc;
description "Computes the divergence of the B1 term in the tensor A from a list containing the metric, Ricci scalar, and the first three symmetrized covariant derivatives of the Ricci scalar.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(tensors);

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

divB2 := proc(tensors) 
local gij, R, Ra, Rab, Rabc, gIJ, rootg, RA, Rabc_Rde, RIBC_Rde, RIBC_Rbc, RAbc_RDI, RAac_RCI, R_Rab_RI, R_RAb_RI, R_RAa_RI, R_RIa_RA;
description "Computes the divergence of the B2 term in the tensor A from a list containing the metric, Ricci scalar, and the first three symmetrized covariant derivatives of the Ricci scalar.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(tensors);

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

divB3 := proc(tensors) 
local gij, R, Ra, Rab, Rabc, gIJ, rootg, RA, Rabc_Rde_RF_RG, RIbc_RDe_RF_RG, RIbc_RBe_RC_RE, RBbc_RIe_RC_RE, R_Rab_RC_RD_RE, R_Rab_RA_RB_RI, Rab_Rcd_Ref_RG, RIb_RCd_REf_RG, RIb_RBd_RDf_RF, RAB_Rcd_RIf_RG, RAB_Rab_RIf_RF;
description "Computes the divergence of the B3 term in the tensor A from a list containing the metric, Ricci scalar, and the first three symmetrized covariant derivatives of the Ricci scalar.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(tensors);

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

divB4 := proc(tensors) 
local gij, R, Ra, Rab, Rabc, gIJ, rootg, RA, Ra_RB, S, RIbc, RIbc_RD_RE, RIbc_RB_RC, RAab, RAab_RC_RI, RAab_RB_RI, R_S_RI, Rab_Rcd_RE, RIB_Rcd_RE, RIB_Rbe_RE, RAB_Rcd_RI, RAB_Rab_RI, RIb_RCd_RE, RIe_RCc_RE;
description "Computes the divergence of the B4 term in the tensor A from a list containing the metric, Ricci scalar, and the first three symmetrized covariant derivatives of the Ricci scalar.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(tensors);

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

divB5 := proc(tensors) 
local gij, R, Ra, Rab, Rabc, gIJ, rootg, RA;
description "Computes the divergence of the B5 term in the tensor A from a list containing the metric, Ricci scalar, and the first three symmetrized covariant derivatives of the Ricci scalar.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(tensors);

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

divB6 := proc(tensors) 
local gij, R, Ra, Rab, Rabc, gIJ, rootg, RA, Ra_RB, S, S_RI, Rab_RC, Rab_RB, RIb_RB, R_RIb_RB, RaB, RaA, RaA_RI, R_RaA_RI;
description "Computes the divergence of the B6 term in the tensor A from a list containing the metric, Ricci scalar, and the first three symmetrized covariant derivatives of the Ricci scalar.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(tensors);

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

divB7 := proc(tensors) 
local gij, R, Ra, Rab, Rabc, gIJ, rootg, RA, Rab_RC, Rab_RB, RIb_RB, RaB, RaA, RaA_RI;
description "Computes the divergence of the B7 term in the tensor A from a list containing the metric, Ricci scalar, and the first three symmetrized covariant derivatives of the Ricci scalar.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(tensors);

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

divB8 := proc(tensors) 
local gij, R, Ra, Rab, Rabc, gIJ, rootg, RA;
description "Computes the divergence of the B8 term in the tensor A from a list containing the metric, Ricci scalar, and the first three symmetrized covariant derivatives of the Ricci scalar.";
uses DifferentialGeometry, DifferentialGeometry:-Tensor;

# Name the metric and compute the Ricci scalar and its first three symmetrized covariant derivatives using Init.
gij, R, Ra, Rab, Rabc := op(tensors);

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


end module: