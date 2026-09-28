import PoincareConjecture.Proofs.M08.ConnectionTimeIdentity
import PoincareConjecture.Proofs.M08.JacobiPhase

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

section LinearAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance weightedPotentialEndGroup : NormedAddCommGroup (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance weightedPotentialEndSpace : NormedSpace ℝ (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
local instance weightedPotentialBivectorGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance weightedPotentialBivectorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
local instance weightedPotentialTrivectorGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance weightedPotentialTrivectorSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance weightedPotentialDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance weightedPotentialDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance weightedPotentialBilinGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance weightedPotentialBilinSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def chartCurvatureAlong (Γ : E →L[ℝ] E →L[ℝ] E)
    (DΓ : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (A : E) : E →L[ℝ] E :=
  (DΓ.flip A).flip A - (DΓ A).flip A + Γ.flip (Γ A A) - (Γ A).comp (Γ.flip A)

theorem chartCurvatureAlong_apply (Γ : E →L[ℝ] E →L[ℝ] E)
    (DΓ : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (A y : E) :
    chartCurvatureAlong Γ DΓ A y =
      DΓ y A A - DΓ A y A + Γ y (Γ A A) - Γ A (Γ y A) := rfl

def chartHessianForm (Γ : E →L[ℝ] E →L[ℝ] E)
    (D : E →L[ℝ] ℝ) (D₂ : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  D₂ - ((ContinuousLinearMap.compL ℝ E E ℝ) D).comp Γ

theorem chartHessianForm_apply (Γ : E →L[ℝ] E →L[ℝ] E)
    (D : E →L[ℝ] ℝ) (D₂ : E →L[ℝ] E →L[ℝ] ℝ) (y w : E) :
    chartHessianForm Γ D D₂ y w = D₂ y w - D (Γ y w) := rfl

def weightedChartPotential (G : E →L[ℝ] E →L[ℝ] ℝ)
    (Γ : E →L[ℝ] E →L[ℝ] E) (DΓ : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] E) (D : E →L[ℝ] ℝ)
    (D₂ : E →L[ℝ] E →L[ℝ] ℝ) (A : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  -(G.comp (chartCurvatureAlong Γ DΓ A)) + chartHessianForm Γ D D₂ -
    ((ContinuousLinearMap.compL ℝ E E ℝ) (G.flip A)).comp B

theorem weightedChartPotential_apply (G : E →L[ℝ] E →L[ℝ] ℝ)
    (Γ : E →L[ℝ] E →L[ℝ] E) (DΓ : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] E) (D : E →L[ℝ] ℝ)
    (D₂ : E →L[ℝ] E →L[ℝ] ℝ) (A y w : E) :
    weightedChartPotential G Γ DΓ B D D₂ A y w =
      -G (chartCurvatureAlong Γ DΓ A y) w +
        (D₂ y w - D (Γ y w)) - G (B y w) A := rfl

set_option maxHeartbeats 1200000 in
theorem weightedChartPotential_contDiffOn [FiniteDimensional ℝ E]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {S : Set X}
    (G : X → E →L[ℝ] E →L[ℝ] ℝ) (Γ : X → E →L[ℝ] E →L[ℝ] E)
    (DΓ : X → E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (B : X → E →L[ℝ] E →L[ℝ] E) (D : X → E →L[ℝ] ℝ)
    (D₂ : X → E →L[ℝ] E →L[ℝ] ℝ) (A : X → E)
    (hG : ContDiffOn ℝ ∞ G S) (hΓ : ContDiffOn ℝ ∞ Γ S)
    (hDΓ : ContDiffOn ℝ ∞ DΓ S) (hB : ContDiffOn ℝ ∞ B S)
    (hD : ContDiffOn ℝ ∞ D S) (hD₂ : ContDiffOn ℝ ∞ D₂ S)
    (hA : ContDiffOn ℝ ∞ A S) :
    ContDiffOn ℝ ∞ (fun z ↦ weightedChartPotential (G z) (Γ z) (DΓ z)
      (B z) (D z) (D₂ z) (A z)) S := by
  apply contDiffOn_clm_apply.mpr
  intro y
  apply contDiffOn_clm_apply.mpr
  intro w
  simp only [weightedChartPotential_apply]
  have hy : ContDiffOn ℝ ∞ (fun _ : X ↦ y) S := contDiffOn_const
  have hw : ContDiffOn ℝ ∞ (fun _ : X ↦ w) S := contDiffOn_const
  have hR : ContDiffOn ℝ ∞ (fun z ↦ chartCurvatureAlong (Γ z) (DΓ z) (A z) y) S :=
    ((((hDΓ.clm_apply hy).clm_apply hA).clm_apply hA).sub
      (((hDΓ.clm_apply hA).clm_apply hy).clm_apply hA)).add
      ((hΓ.clm_apply hy).clm_apply ((hΓ.clm_apply hA).clm_apply hA)) |>.sub
      ((hΓ.clm_apply hA).clm_apply ((hΓ.clm_apply hy).clm_apply hA))
  exact (((hG.clm_apply hR).clm_apply hw).neg.add
    (((hD₂.clm_apply hy).clm_apply hw).sub
      (hD.clm_apply ((hΓ.clm_apply hy).clm_apply hw)))).sub
    ((hG.clm_apply ((hB.clm_apply hy).clm_apply hw)).clm_apply hA)

end LinearAlgebra

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance weightedJacobiDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance weightedJacobiDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance weightedJacobiBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance weightedJacobiBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance weightedJacobiEndGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance weightedJacobiEndSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ContinuousLinearMap.toNormedSpace
local instance weightedJacobiConnectionGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) := ContinuousLinearMap.toNormedAddCommGroup
local instance weightedJacobiConnectionSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) := ContinuousLinearMap.toNormedSpace
local instance weightedJacobiTrilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance weightedJacobiTrilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance weightedJacobiTrivectorGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance weightedJacobiTrivectorSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ContinuousLinearMap.toNormedSpace

def chartMetricDualInverse {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) (z : ℝ × EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Ring.inverse (chartMetricOperator F T x z)).comp
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem chartMetricDualInverse_pair {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) {z : ℝ × EuclideanSpace ℝ (Fin n)}
    (hz : z.2 ∈ (extChartAt (𝓡 n) x).target)
    (η : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    chartActionMetric F T x z (chartMetricDualInverse F T x z η) w = η w :=
  chartMetricInverse_pair F T x hz η w

theorem chartMetricDualInverse_left {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) {z : ℝ × EuclideanSpace ℝ (Fin n)}
    (hz : z.2 ∈ (extChartAt (𝓡 n) x).target) (v : EuclideanSpace ℝ (Fin n)) :
    chartMetricDualInverse F T x z (chartActionMetric F T x z v) = v := by
  change Ring.inverse (chartMetricOperator F T x z) (chartMetricOperator F T x z v) = v
  exact congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) ↦ A v)
    (Ring.inverse_mul_cancel _ (chartMetricOperator_isUnit_of_target F T x hz))

theorem chartMetricDualInverse_contDiffOn {J C : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) :
    ContDiffOn ℝ ∞ (chartMetricDualInverse F T x)
      (C ×ˢ (extChartAt (𝓡 n) x).target) :=
  (chartMetricInverse_closed_contDiffOn F T x htime).clm_comp contDiffOn_const

def closedChartConnection {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) (C : Set ℝ) (z : ℝ × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  jacobiChristoffelOperator (chartMetricDualInverse F T x z)
    (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionMetric F T x) z)

theorem closedChartConnection_apply {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) (C : Set ℝ) (z : ℝ × EuclideanSpace ℝ (Fin n))
    (v w : EuclideanSpace ℝ (Fin n)) :
    closedChartConnection F T x C z v w = closedChartChristoffel F T x C z v w := rfl

set_option maxHeartbeats 2000000 in
theorem closedChartConnection_contDiffOn {J C : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) (hC : UniqueDiffOn ℝ C) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) :
    ContDiffOn ℝ ∞ (closedChartConnection F T x C)
      (C ×ˢ (extChartAt (𝓡 n) x).target) := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  change ContDiffOn ℝ ∞ (fun z ↦ closedChartChristoffel F T x C z v w)
    (C ×ˢ (extChartAt (𝓡 n) x).target)
  let k : ℝ × EuclideanSpace ℝ (Fin n) →
      (ℝ × EuclideanSpace ℝ (Fin n)) ×
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) := fun z ↦ (z, (v, w))
  have hk : ContDiff ℝ ∞ k := contDiff_id.prodMk contDiff_const
  have hm : MapsTo k (C ×ˢ (extChartAt (𝓡 n) x).target)
      ((C ×ˢ (extChartAt (𝓡 n) x).target) ×ˢ univ) := fun z hz ↦ ⟨hz, mem_univ (v, w)⟩
  have h := ContDiffOn.comp (closedChartChristoffel_contDiffOn F T x hC htime)
    hk.contDiffOn hm
  exact h

theorem closedChartConnection_time_apply {J C : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) (hC : UniqueDiffOn ℝ C) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {s : ℝ} (hs : s ∈ C) {q : EuclideanSpace ℝ (Fin n)}
    (hq : q ∈ (extChartAt (𝓡 n) x).target) (v w : EuclideanSpace ℝ (Fin n)) :
    timeWithinFDeriv C (extChartAt (𝓡 n) x).target (closedChartConnection F T x C) (s, q) v w =
      timeWithinFDeriv C (extChartAt (𝓡 n) x).target
        (fun z ↦ closedChartChristoffel F T x C z v w) (s, q) := by
  have hΓ := closedChartConnection_contDiffOn F T x hC htime
  have h := ((hasDerivWithinAt_timeWithin _ hΓ hs hq).clm_apply
    (hasDerivWithinAt_const s C v)).clm_apply (hasDerivWithinAt_const s C w)
  have hΓvw := (closedChartChristoffel_contDiffOn F T x hC htime).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun z hz ↦ ⟨hz, mem_univ (v, w)⟩)
  have h' := hasDerivWithinAt_timeWithin _ hΓvw hs hq
  have heq := (h.derivWithin (hC s hs)).symm.trans (h'.derivWithin (hC s hs))
  simpa only [map_zero, add_zero, add_apply, Function.comp_def, id_eq] using heq

theorem closedChartConnection_spatial_apply {J C : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) (hC : UniqueDiffOn ℝ C) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {s : ℝ} (hs : s ∈ C) {q : EuclideanSpace ℝ (Fin n)}
    (hq : q ∈ (extChartAt (𝓡 n) x).target) (v w z : EuclideanSpace ℝ (Fin n)) :
    spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
        (closedChartConnection F T x C) (s, q) v w z =
      fderiv ℝ (fun r ↦ closedChartChristoffel F T x C (s, r) w z) q v := by
  have hd := hasFDerivAt_spatialWithin (isOpen_extChartAt_target (I := 𝓡 n) x) _
    (closedChartConnection_contDiffOn F T x hC htime) hs hq
  have heq := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) ↦ A v)
    (((hd.clm_apply (hasFDerivAt_const w q)).clm_apply (hasFDerivAt_const z q)).fderiv)
  simpa only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, add_zero, closedChartConnection_apply] using heq.symm

def closedChartJacobiPotential {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) (C : Set ℝ) (z : ℝ × EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  weightedChartPotential (chartActionMetric F T x z) (closedChartConnection F T x C z)
    (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (closedChartConnection F T x C) z)
    (timeWithinFDeriv C (extChartAt (𝓡 n) x).target (closedChartConnection F T x C) z)
    (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionPotential F T x) z)
    (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
      (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionPotential F T x)) z) A

set_option maxHeartbeats 1200000 in
theorem closedChartJacobiPotential_contDiffOn {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x : M)
    (hC : UniqueDiffOn ℝ C) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) :
    ContDiffOn ℝ ∞
      (fun z : (ℝ × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) ↦
        closedChartJacobiPotential F T x C z.1 z.2)
      ((C ×ˢ (extChartAt (𝓡 n) x).target) ×ˢ univ) := by
  let U := (extChartAt (𝓡 n) x).target
  let Ω := (C ×ˢ U) ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n)))
  have hU : IsOpen U := isOpen_extChartAt_target (I := 𝓡 n) x
  have hmap : MapsTo (Prod.fst : (ℝ × EuclideanSpace ℝ (Fin n)) ×
      EuclideanSpace ℝ (Fin n) → ℝ × EuclideanSpace ℝ (Fin n)) Ω (C ×ˢ U) := fun z hz ↦ hz.1
  have hG := (chartActionMetric_closed_contDiffOn F T x htime).comp contDiffOn_fst hmap
  have hΓ₀ := closedChartConnection_contDiffOn F T x hC htime
  have hΓ := hΓ₀.comp contDiffOn_fst hmap
  have hDΓ := (spatialWithinFDeriv_contDiffOn hC hU _ hΓ₀).comp contDiffOn_fst hmap
  have hB := (timeWithinFDeriv_contDiffOn hC hU _ hΓ₀).comp contDiffOn_fst hmap
  have hD₀ := spatialWithinFDeriv_contDiffOn hC hU _
    (chartActionPotential_closed_contDiffOn F hM04 T x htime)
  have hD := hD₀.comp contDiffOn_fst hmap
  have hD₂ := (spatialWithinFDeriv_contDiffOn hC hU _ hD₀).comp contDiffOn_fst hmap
  exact weightedChartPotential_contDiffOn _ _ _ _ _ _ _ hG hΓ hDΓ hB hD hD₂ contDiffOn_snd

end PoincareConjecture.M08
