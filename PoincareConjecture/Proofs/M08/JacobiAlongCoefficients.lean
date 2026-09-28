import PoincareConjecture.Proofs.M08.WeightedJacobiIdentities
import PoincareConjecture.Proofs.M08.JacobiAlongPair
import PoincareConjecture.Proofs.M08.JacobiClosedCoordinates
import PoincareConjecture.Proofs.M08.VariationMetricPair
import PoincareConjecture.Proofs.M08.ChartEulerEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance jacobiAlongDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance jacobiAlongDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance jacobiAlongBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance jacobiAlongBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance jacobiAlongEndGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance jacobiAlongEndSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ContinuousLinearMap.toNormedSpace
local instance jacobiAlongConnectionGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) := ContinuousLinearMap.toNormedAddCommGroup
local instance jacobiAlongConnectionSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) := ContinuousLinearMap.toNormedSpace

def jacobiAlongSharp {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (x : M) (α : ℝ → M) (s : ℝ) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  chartMetricDualInverse F T x (s, extChartAt (𝓡 n) x (α s))

def jacobiAlongConnection {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (x : M) (S : Set ℝ) (α : ℝ → M) (s : ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  closedChartConnection F T x S (s, extChartAt (𝓡 n) x (α s))
    (deriv ((extChartAt (𝓡 n) x) ∘ α) s)

def jacobiAlongPotential {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (x : M) (S : Set ℝ) (α : ℝ → M) (s : ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  closedChartJacobiPotential F T x S (s, extChartAt (𝓡 n) x (α s))
    (deriv ((extChartAt (𝓡 n) x) ∘ α) s)

def jacobiAlongMetricTime {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (x : M) (S : Set ℝ) (α : ℝ → M) (s : ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  timeWithinFDeriv S (extChartAt (𝓡 n) x).target (chartActionMetric F T x)
    (s, extChartAt (𝓡 n) x (α s))

def jacobiAlongPhase {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (x : M) (S : Set ℝ) (α : ℝ → M) (s : ℝ) :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  covariantLinearPhaseOperator (jacobiAlongSharp F T x α s)
    (jacobiAlongConnection F T x S α s) (jacobiAlongPotential F T x S α s)
    (jacobiAlongMetricTime F T x S α s)

set_option maxHeartbeats 4000000 in
theorem jacobiAlongCoefficients_contDiffOn {J S U C : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ)
    (x : M) (α : ℝ → M) (hS : UniqueDiffOn ℝ S)
    (htime : ∀ s ∈ S, T - s ^ 2 ∈ J) (hCS : C ⊆ S)
    (hU : IsOpen U) (hCU : C ⊆ U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (hsrc : MapsTo α C (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ContDiffOn ℝ ∞ (jacobiAlongSharp F T x α) C ∧
    ContDiffOn ℝ ∞ (jacobiAlongConnection F T x S α) C ∧
    ContDiffOn ℝ ∞ (jacobiAlongPotential F T x S α) C ∧
    ContDiffOn ℝ ∞ (jacobiAlongMetricTime F T x S α) C := by
  let V := U ∩ α ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source
  have hV : IsOpen V := hα.continuousOn.isOpen_inter_preimage hU
    (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
  have hCV : C ⊆ V := fun s hs ↦ ⟨hCU hs, hsrc hs⟩
  have hqV := chart_curve_contDiffOn x α (hα.mono inter_subset_left)
    (show MapsTo α V (chartAt (EuclideanSpace ℝ (Fin n)) x).source from fun _ hs ↦ hs.2)
  have hq : ContDiffOn ℝ ∞ ((extChartAt (𝓡 n) x) ∘ α) C := hqV.mono hCV
  have hA : ContDiffOn ℝ ∞ (deriv ((extChartAt (𝓡 n) x) ∘ α)) C :=
    (hqV.deriv_of_isOpen hV (by simp)).mono hCV
  have hpoint : ContDiffOn ℝ ∞ (fun s ↦ (s, extChartAt (𝓡 n) x (α s))) C :=
    contDiffOn_id.prodMk hq
  have hmap : MapsTo (fun s ↦ (s, extChartAt (𝓡 n) x (α s))) C
      (S ×ˢ (extChartAt (𝓡 n) x).target) := by
    intro s hs
    exact ⟨hCS hs, (extChartAt (𝓡 n) x).map_source
      (by simpa only [extChartAt_source] using hsrc hs)⟩
  have hpointA : ContDiffOn ℝ ∞ (fun s ↦
      ((s, extChartAt (𝓡 n) x (α s)), deriv ((extChartAt (𝓡 n) x) ∘ α) s)) C :=
    hpoint.prodMk hA
  have hmapA : MapsTo (fun s ↦
      ((s, extChartAt (𝓡 n) x (α s)), deriv ((extChartAt (𝓡 n) x) ∘ α) s)) C
      ((S ×ˢ (extChartAt (𝓡 n) x).target) ×ˢ univ) :=
    fun s hs ↦ ⟨hmap hs, mem_univ _⟩
  have hB := (chartMetricDualInverse_contDiffOn F T x htime).comp hpoint hmap
  have hΓ := ((closedChartConnection_contDiffOn F T x hS htime).comp hpoint hmap).clm_apply hA
  have hV₀ := closedChartJacobiPotential_contDiffOn F hM04 T x hS htime
  have hV := hV₀.comp hpointA hmapA
  have hH := (timeWithinFDeriv_contDiffOn hS (isOpen_extChartAt_target (I := 𝓡 n) x)
    (chartActionMetric F T x) (chartActionMetric_closed_contDiffOn F T x htime)).comp hpoint hmap
  exact ⟨hB, hΓ, hV, hH⟩

theorem chartFrame_curveVelocityWithin {C : Set ℝ} {α : ℝ → M} {x : M} {s : ℝ}
    (hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hC : UniqueDiffWithinAt ℝ C s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    chartFrame x (deriv ((extChartAt (𝓡 n) x) ∘ α) s) (α s) =
      curveVelocityWithin (n := n) α C s := by
  rw [chartFrame_curveVelocity hx hα]
  unfold curveVelocityWithin curveVelocity
  rw [mfderivWithin_eq_mfderiv hC.uniqueMDiffWithinAt hα]

set_option maxHeartbeats 1800000 in
theorem jacobiPairResidual_chart {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {A B : ℝ} (hAB : A < B)
    (htime : ∀ s ∈ Icc A B, T - s ^ 2 ∈ J) (x : M) (α : ℝ → M)
    {s : ℝ} (hs : s ∈ Icc A B)
    (hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s)
    (y p dp w : EuclideanSpace ℝ (Fin n)) :
    jacobiPairResidual F T α (Icc A B) s (chartFrame x y (α s))
        (chartFrame x p (α s)) (chartFrame x dp (α s)) (chartFrame x w (α s)) =
      chartActionMetric F T x (s, extChartAt (𝓡 n) x (α s)) dp w -
        jacobiAlongPotential F T x (Icc A B) α s y w +
        jacobiAlongMetricTime F T x (Icc A B) α s p w := by
  have hq : extChartAt (𝓡 n) x (α s) ∈ (extChartAt (𝓡 n) x).target :=
    (extChartAt (𝓡 n) x).map_source (by simpa only [extChartAt_source] using hx)
  have hpotential := closedChartJacobiPotential_identification F hM04 T
    (uniqueDiffOn_Icc hAB) htime hx hs
    (mem_closure_interior_Icc_prod hAB (isOpen_extChartAt_target (I := 𝓡 n) x) hs hq)
    (deriv ((extChartAt (𝓡 n) x) ∘ α) s) y w
  have hmetric : jacobiAlongMetricTime F T x (Icc A B) α s p w =
      4 * s * (F.connection (T - s ^ 2)).ricci (α s)
        (chartFrame x p (α s)) (chartFrame x w (α s)) := by
    unfold jacobiAlongMetricTime
    rw [chartActionMetric_timeWithin F hM04 T x (uniqueDiffOn_Icc hAB) htime hs hq]
    simp only [smul_apply, smul_eq_mul, chartRicciForm_at hM04 _ hx]
  unfold jacobiPairResidual jacobiAlongPotential
  rw [← chartFrame_curveVelocityWithin hx (uniqueDiffOn_Icc hAB s hs) hα,
    chartActionMetric_apply F T hx s dp w, hpotential, hmetric]
  ring

end PoincareConjecture.M08
