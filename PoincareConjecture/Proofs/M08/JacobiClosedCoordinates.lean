import PoincareConjecture.Proofs.M08.ChartConnection
import PoincareConjecture.Proofs.M08.SmoothEndpointExtension
import PoincareConjecture.Proofs.M08.JacobiPhase

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_closedChartSectionExtension {a b : ℝ} (hab : a < b)
    (x : M) (α : ℝ → M) (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : ContDiffOn ℝ ∞ c (Icc a b))
    (hsrc : MapsTo α (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (hY : ∀ s ∈ Icc a b, chartFrame x (c s) (α s) = Y s) :
    Nonempty (ParametricAlongCurveExtensionOn (Icc a b) α Y) := by
  obtain ⟨g, hg, hgc⟩ := exists_smooth_extension_Icc hab c hc
  exact ⟨chartSectionExtension isOpen_univ (subset_univ _) x α g hg.contDiffOn hsrc Y
    (fun s hs ↦ by rw [hgc hs]; exact hY s hs)⟩

theorem closedChartField_contMDiffOn {C : Set ℝ}
    (x : M) (α : ℝ → M) (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α C)
    (hc : ContDiffOn ℝ ∞ c C)
    (hsrc : MapsTo α C (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s)
        (chartFrame x (c s) (α s))) C := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  apply (e.contMDiffOn_symm.comp (hα.prodMk hc.contMDiffOn)
    (fun s hs ↦ e.mem_target.mpr (hsrc hs))).congr
  intro s hs
  rw [show chartFrame x (c s) (α s) = e.symm (α s) (c s) from
    Bundle.Trivialization.symmL_apply e (hsrc hs) (c s)]
  exact e.mk_symm (hsrc hs) (c s)

set_option maxHeartbeats 1000000 in
theorem pullbackCovariantDerivative_closedChart_formula {J S : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) {a b : ℝ} (hab : a < b)
    (hCS : Icc a b ⊆ S) (htime : ∀ s ∈ S, T - s ^ 2 ∈ J)
    (x : M) (α : ℝ → M) (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : ContDiffOn ℝ ∞ c (Icc a b))
    (hsrc : MapsTo α (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (Y : ∀ r, TangentSpace (𝓡 n) (α r))
    (hY : ∀ r ∈ Icc a b, chartFrame x (c r) (α r) = Y r)
    (E : ParametricAlongCurveExtensionOn (Icc a b) α Y)
    {s : ℝ} (hs : s ∈ Icc a b) (dc : EuclideanSpace ℝ (Fin n))
    (hdc : HasDerivWithinAt c dc (Icc a b) s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y (Icc a b) E s =
      chartFrame x (dc + closedChartChristoffel F T x S (s, extChartAt (𝓡 n) x (α s))
        (deriv ((extChartAt (𝓡 n) x) ∘ α) s) (c s)) (α s) := by
  obtain ⟨g, hg, hgc⟩ := exists_smooth_extension_Icc hab c hc
  have hgd : deriv g s = dc := by
    have hd : HasDerivWithinAt g (deriv g s) (Icc a b) s :=
      ((hg.differentiable (by simp)) s).hasDerivAt.hasDerivWithinAt
    exact UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc hab s hs)
      (hd.congr_of_mem (fun r hr ↦ (hgc hr).symm) hs) hdc
  have hfield : ∀ r ∈ Icc a b, chartFrame x (g r) (α r) = Y r := by
    intro r hr
    rw [hgc hr]
    exact hY r hr
  rw [pullbackCovariantDerivative_chart_formula F (fun r ↦ T - r ^ 2)
    isOpen_univ (subset_univ _) x α g hg.contDiffOn hsrc Y hfield E hs
      (uniqueDiffOn_Icc hab s hs) hα,
    hgd, hgc hs, closedChartChristoffel_connection F T htime (hsrc hs) (hCS hs)]
  exact ((trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) x).symmL ℝ (α s)).map_add _ _ |>.symm

local instance closedJacobiDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance closedJacobiDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance closedJacobiBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance closedJacobiBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 1000000 in
theorem covariantPhase_pullback_pair {J S : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) {a b : ℝ} (hab : a < b)
    (hCS : Icc a b ⊆ S) (htime : ∀ s ∈ S, T - s ^ 2 ∈ J)
    (x : M) (α : ℝ → M)
    (hsrc : MapsTo α (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (B : ℝ → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (C : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (V H : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (z : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (hz : ContDiffOn ℝ ∞ z (Icc a b))
    (EY : ParametricAlongCurveExtensionOn (Icc a b) α
      (fun r ↦ chartFrame x (z r).1 (α r)))
    (EP : ParametricAlongCurveExtensionOn (Icc a b) α
      (fun r ↦ chartFrame x (z r).2 (α r)))
    {s : ℝ} (hs : s ∈ Icc a b)
    (hΓ : ∀ v, C s v = closedChartChristoffel F T x S
      (s, extChartAt (𝓡 n) x (α s)) (deriv ((extChartAt (𝓡 n) x) ∘ α) s) v)
    (hd : HasDerivWithinAt z (covariantLinearPhaseOperator (B s) (C s) (V s) (H s) (z s))
      (Icc a b) s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
        (fun r ↦ chartFrame x (z r).1 (α r)) (Icc a b) EY s =
      chartFrame x (z s).2 (α s) ∧
    pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
        (fun r ↦ chartFrame x (z r).2 (α r)) (Icc a b) EP s =
      chartFrame x (B s (V s (z s).1 - H s (z s).2)) (α s) := by
  have hdy : HasDerivWithinAt (fun r ↦ (z r).1) ((z s).2 - C s (z s).1)
      (Icc a b) s := hd.fst
  have hdp : HasDerivWithinAt (fun r ↦ (z r).2)
      (B s (V s (z s).1 - H s (z s).2) - C s (z s).2) (Icc a b) s := hd.snd
  constructor
  · rw [pullbackCovariantDerivative_closedChart_formula F T hab hCS htime x α
      (fun r ↦ (z r).1) hz.fst hsrc _ (fun _ _ ↦ rfl) EY hs _ hdy hα,
      ← hΓ (z s).1, sub_add_cancel]
  · rw [pullbackCovariantDerivative_closedChart_formula F T hab hCS htime x α
      (fun r ↦ (z r).2) hz.snd hsrc _ (fun _ _ ↦ rfl) EP hs _ hdp hα,
      ← hΓ (z s).2, sub_add_cancel]

end PoincareConjecture.M08
