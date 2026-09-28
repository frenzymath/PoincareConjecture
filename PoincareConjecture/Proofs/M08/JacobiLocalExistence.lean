import PoincareConjecture.Proofs.M08.JacobiAlongCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance jacobiLocalDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance jacobiLocalDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance jacobiLocalBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance jacobiLocalBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 2000000 in
theorem exists_chartJacobiPairOn {J U : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {A B a b t₀ : ℝ}
    (hAB : A < B) (hab : a < b) (hCS : Icc a b ⊆ Icc A B)
    (htime : ∀ s ∈ Icc A B, T - s ^ 2 ∈ J)
    (x : M) (α : ℝ → M) (hU : IsOpen U) (hCU : Icc a b ⊆ U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (hsrc : MapsTo α (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (ht₀ : t₀ ∈ Icc a b) (z₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    ∃ z : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      IsJacobiPairOn F T α (Icc A B) a b z ∧ z t₀ = z₀ := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let B₀ := jacobiAlongSharp F T x α
  let C₀ := jacobiAlongConnection F T x (Icc A B) α
  let V₀ := jacobiAlongPotential F T x (Icc A B) α
  let H₀ := jacobiAlongMetricTime F T x (Icc A B) α
  obtain ⟨hB, hC, hV, hH⟩ := jacobiAlongCoefficients_contDiffOn F hM04 T x α
    (uniqueDiffOn_Icc hAB) htime hCS hU hCU hα hsrc
  obtain ⟨v, hv₀, hv, hvd⟩ := exists_covariant_linear_phase_solution B₀ C₀ V₀ H₀ hB hC hV hH ht₀
    (e.continuousLinearMapAt ℝ (α t₀) z₀.1, e.continuousLinearMapAt ℝ (α t₀) z₀.2)
  let z : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    fun s ↦ (chartFrame x (v s).1 (α s), chartFrame x (v s).2 (α s))
  have hzsmooth₁ := closedChartField_contMDiffOn x α (fun s ↦ (v s).1)
    (hα.mono hCU) hv.fst hsrc
  have hzsmooth₂ := closedChartField_contMDiffOn x α (fun s ↦ (v s).2)
    (hα.mono hCU) hv.snd hsrc
  obtain ⟨EY⟩ := exists_closedChartSectionExtension hab x α (fun s ↦ (v s).1) hv.fst hsrc
    (fun s ↦ (z s).1) (fun _ _ ↦ rfl)
  obtain ⟨EP⟩ := exists_closedChartSectionExtension hab x α (fun s ↦ (v s).2) hv.snd hsrc
    (fun s ↦ (z s).2) (fun _ _ ↦ rfl)
  have hαs (s : ℝ) (hs : s ∈ Icc a b) : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s :=
    ((hα s (hCU hs)).contMDiffAt (hU.mem_nhds (hCU hs))).mdifferentiableAt (by simp)
  have hpair (s : ℝ) (hs : s ∈ Icc a b) := covariantPhase_pullback_pair F T hab hCS htime x α
    hsrc B₀ C₀ V₀ H₀ v hv EY EP hs (fun _ ↦ rfl) (hvd s hs) (hαs s hs)
  refine ⟨z, ⟨hab, hCS, hzsmooth₁, hzsmooth₂, EY, EP, ?_, ?_⟩, ?_⟩
  · intro s hs
    exact (hpair s hs).1
  · intro s hs W
    let w := e.continuousLinearMapAt ℝ (α s) W
    have hw : chartFrame x w (α s) = W := e.symmL_continuousLinearMapAt (hsrc hs) W
    have hq : extChartAt (𝓡 n) x (α s) ∈ (extChartAt (𝓡 n) x).target :=
      (extChartAt (𝓡 n) x).map_source (by simpa only [extChartAt_source] using hsrc hs)
    change jacobiPairResidual F T α (Icc A B) s (chartFrame x (v s).1 (α s))
      (chartFrame x (v s).2 (α s)) _ W = 0
    rw [(hpair s hs).2, ← hw,
      jacobiPairResidual_chart F hM04 T hAB htime x α (hCS hs) (hsrc hs) (hαs s hs)]
    change chartActionMetric F T x (s, extChartAt (𝓡 n) x (α s))
        (chartMetricDualInverse F T x (s, extChartAt (𝓡 n) x (α s))
          (V₀ s (v s).1 - H₀ s (v s).2)) w - V₀ s (v s).1 w + H₀ s (v s).2 w = 0
    rw [chartMetricDualInverse_pair F T x hq]
    simp only [sub_apply]
    ring
  · change (chartFrame x (v t₀).1 (α t₀), chartFrame x (v t₀).2 (α t₀)) = z₀
    rw [hv₀]
    exact Prod.ext (e.symmL_continuousLinearMapAt (hsrc ht₀) z₀.1)
      (e.symmL_continuousLinearMapAt (hsrc ht₀) z₀.2)

end PoincareConjecture.M08
