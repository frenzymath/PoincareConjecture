import PoincareConjecture.Proofs.M35.Thm12_28.ScalarDerivativeJets
import PoincareConjecture.Proofs.M35.CapGeometry.RadialUnitRicci









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.M35

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "B" => V →L[ℝ] V →L[ℝ] ℝ

local instance radialRicciNormedGroup : NormedAddCommGroup B := inferInstance
local instance radialRicciNormedSpace : NormedSpace ℝ B := inferInstance

private noncomputable def basisPair (i j : Fin 3) : B :=
  (EuclideanSpace.proj i).smulRight (EuclideanSpace.proj j)


noncomputable def radialRicciCoefficients {g : RiemannianMetric 3 V}
    (D : LeviCivitaData g) (x : V) : B :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    D.ricci x (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j) • basisPair i j


theorem radialRicciCoefficients_apply {g : RiemannianMetric 3 V}
    (D : LeviCivitaData g) (x u v : V) :
    radialRicciCoefficients D x u v = D.ricci x u v := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  have hexp (w : V) : (∑ i : Fin 3, w i • e i) = w := by
    simpa only [e, EuclideanSpace.basisFun_repr] using e.sum_repr w
  have h : M13.ricciLinear D x u v =
      ∑ i : Fin 3, ∑ j : Fin 3, u i * (v j * M13.ricciLinear D x (e i) (e j)) := by
    conv_lhs => rw [← hexp u, ← hexp v]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [← M13.ricciLinear_apply, h]
  simp only [radialRicciCoefficients, sum_apply, smul_apply, basisPair,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change D.ricci x (e i) (e j) * (u i * v j) =
    u i * (v j * D.ricci x (e i) (e j))
  ring


theorem radialRicciCoefficients_contDiffAt {g : RiemannianMetric 3 V}
    (D : LeviCivitaData g) (x : V) : ContDiffAt ℝ ∞ (radialRicciCoefficients D) x := by
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    (ricci_contDiffAt_euclidean D x (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j)).smul contDiffAt_const



theorem radialRicciCoefficients_jets_tendsto
    {gseq : ℕ → RiemannianMetric 3 V} {g : RiemannianMetric 3 V}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → V) (p : V) (r : ℕ)
    (hjet : ∀ m ≤ r + 2, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p))) :
    Tendsto (fun k => iteratedFDeriv ℝ r (radialRicciCoefficients (Dseq k)) (pseq k))
      atTop (𝓝 (iteratedFDeriv ℝ r (radialRicciCoefficients D) p)) := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  let term {g' : RiemannianMetric 3 V} (D' : LeviCivitaData g') (i j : Fin 3) (x : V) :=
    D'.ricci x (e i) (e j) • basisPair i j
  have hs {g' : RiemannianMetric 3 V} (D' : LeviCivitaData g') (i j : Fin 3) (x : V) :
      ContDiffAt ℝ ∞ (term D' i j) x :=
    (ricci_contDiffAt_euclidean D' x (e i) (e j)).smul contDiffAt_const
  have heq {g' : RiemannianMetric 3 V} (D' : LeviCivitaData g') (x : V) :
      iteratedFDeriv ℝ r (radialRicciCoefficients D') x =
        ∑ i : Fin 3, ∑ j : Fin 3, iteratedFDeriv ℝ r (term D' i j) x := by
    have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
    change iteratedFDeriv ℝ r (fun y => ∑ i, ∑ j, term D' i j y) x = _
    rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
      (ContDiffAt.sum fun j _ => hs D' i j x).of_le hr)]
    apply Finset.sum_congr rfl
    intro i _
    exact iteratedFDeriv_fun_sum_apply (fun j _ => (hs D' i j x).of_le hr)
  simp_rw [heq]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  let L : ℝ →L[ℝ] B := (ContinuousLinearMap.id ℝ ℝ).smulRight (basisPair i j)
  exact tendsto_iteratedFDeriv_clm_comp_of_jet r L
    (ricci_contDiffAt_euclidean D p (e i) (e j))
    (Eventually.of_forall fun k => ricci_contDiffAt_euclidean (Dseq k) (pseq k) (e i) (e j))
    (ricci_jets_tendsto_of_metric_jets Dseq D pseq p (e i) (e j) r hjet)

end

end PoincareConjecture.M35
