import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.TestRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.ChangeOfVariables
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Parabolic.WeakRegularity

namespace PoincareConjecture.RicciFlow.ConjugateHeat

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def spacetimeChartPullback
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (φ : M × ℝ → ℝ) : Spacetime n → ℝ :=
  (e.source ×ˢ univ).indicator (fun z => φ (e z.1, z.2))

theorem spacetimeChartPullback_apply
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (φ : M × ℝ → ℝ) {z : Spacetime n} (hz : z.1 ∈ e.source) :
    spacetimeChartPullback e φ z = φ (e z.1, z.2) :=
  indicator_of_mem (show z ∈ e.source ×ˢ univ from ⟨hz, mem_univ _⟩) _

theorem spacetimeChartPullback_nonneg
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {φ : M × ℝ → ℝ} (hφ : ∀ z, 0 ≤ φ z) (z : Spacetime n) :
    0 ≤ spacetimeChartPullback e φ z :=
  indicator_nonneg (fun y _ => hφ (e y.1, y.2)) z

private theorem compact_inverse_spacetime_support
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {φ : M × ℝ → ℝ} (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ e.target ×ˢ univ) :
    IsCompact ((fun z : M × ℝ => (e.symm z.1, z.2)) '' tsupport φ) := by
  apply hc.isCompact.image_of_continuousOn
  have hback : ContinuousOn (fun z : M × ℝ => (e.symm z.1, z.2))
      (e.target ×ˢ univ) :=
    (e.symm.continuousOn.comp continuous_fst.continuousOn
      (fun z hz => hz.1)).prodMk continuous_snd.continuousOn
  exact hback.mono hs

theorem tsupport_spacetimeChartPullback_subset_image
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {φ : M × ℝ → ℝ} (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ e.target ×ˢ univ) :
    tsupport (spacetimeChartPullback e φ) ⊆
      (fun z : M × ℝ => (e.symm z.1, z.2)) '' tsupport φ := by
  apply closure_minimal _ (compact_inverse_spacetime_support e hc hs).isClosed
  intro z hz
  have hsource : z.1 ∈ e.source := by
    by_contra h
    exact hz (indicator_of_notMem (fun hz' => h hz'.1) _)
  refine ⟨(e z.1, z.2), subset_tsupport φ ?_, ?_⟩
  · simpa only [Function.mem_support, spacetimeChartPullback_apply e φ hsource] using hz
  · simp only [e.left_inv hsource, Prod.eta]

theorem tsupport_spacetimeChartPullback_subset
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {φ : M × ℝ → ℝ} {T : Set ℝ} (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ e.target ×ˢ T) :
    tsupport (spacetimeChartPullback e φ) ⊆ e.source ×ˢ T := by
  have hs' := hs.trans (prod_mono Subset.rfl (subset_univ T))
  intro z hz
  obtain ⟨y, hy, rfl⟩ := tsupport_spacetimeChartPullback_subset_image e hc hs' hz
  exact ⟨e.map_target (hs hy).1, (hs hy).2⟩

theorem hasCompactSupport_spacetimeChartPullback
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {φ : M × ℝ → ℝ} (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ e.target ×ˢ univ) :
    HasCompactSupport (spacetimeChartPullback e φ) :=
  (compact_inverse_spacetime_support e hc hs).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_spacetimeChartPullback_subset_image e hc hs)

theorem contDiff_spacetimeChartPullback
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    {φ : M × ℝ → ℝ}
    (hφ : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ e.target ×ˢ univ) :
    ContDiff ℝ ∞ (spacetimeChartPullback e φ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z.1 ∈ e.source
  · have hmap : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ))
        ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
        (fun y : Spacetime n => (e y.1, y.2)) z :=
      ((he.contMDiffAt (e.open_source.mem_nhds hz)).comp z
        contMDiffAt_fst).prodMk contMDiffAt_snd
    have h := (hφ (e z.1, z.2)).comp z hmap
    simp +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    apply h.contDiffAt.congr_of_eventuallyEq
    filter_upwards [(continuous_fst.tendsto z) (e.open_source.mem_nhds hz)] with y hy
    exact spacetimeChartPullback_apply e φ hy
  · apply contDiffAt_const.congr_of_eventuallyEq
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro hz'
    exact hz (tsupport_spacetimeChartPullback_subset e hc hs hz').1

theorem coordinate_heatTest_eq_neg_testOperator
    (F : RicciFlow n M (Iio (0 : ℝ)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    {φ : M × ℝ → ℝ}
    (hφ : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ e.target ×ˢ univ)
    {z : Spacetime n} (hz : z.1 ∈ e.source) :
    -Canonical.timeDeriv (spacetimeChartPullback e φ) z -
      (F.connection (-z.2)).laplacian
        (fun y => spacetimeChartPullback e φ (e.symm y, z.2)) (e z.1) =
      -testOperator F φ (e z.1, z.2) := by
  let ψ := spacetimeChartPullback e φ
  have hψ : ContDiff ℝ ∞ ψ := contDiff_spacetimeChartPullback e he hφ hc hs
  have ht : Canonical.timeDeriv ψ z = deriv (fun τ => φ (e z.1, τ)) z.2 := by
    have hd := ((hψ.differentiable (by simp) z).hasFDerivAt.comp_hasDerivAt z.2
      ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv.symm
    have heq : (fun τ => ψ (z.1, τ)) = (fun τ => φ (e z.1, τ)) :=
      funext fun τ => spacetimeChartPullback_apply e φ hz
    exact hd.trans (congrArg (fun f : ℝ → ℝ => deriv f z.2) heq)
  have hspace : (fun y => ψ (e.symm y, z.2)) =ᶠ[𝓝 (e z.1)]
      (fun y => φ (y, z.2)) := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hz)] with y hy
    change spacetimeChartPullback e φ (e.symm y, z.2) = φ (y, z.2)
    rw [spacetimeChartPullback_apply e φ (e.map_target hy), e.right_inv hy]
  change -Canonical.timeDeriv ψ z - _ = _
  rw [ht, (F.connection (-z.2)).laplacian_eq_of_eventuallyEq hspace]
  simp only [testOperator, neg_add_rev]
  ring

section Measure

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem weakPairing_eq_neg_coordinate_pairing
    (F : RicciFlow n M (Iio (0 : ℝ)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {u φ : M × ℝ → ℝ} (hu : ContinuousOn u (univ ×ˢ Ioi (0 : ℝ)))
    (hφ : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ e.target ×ˢ Ioi (0 : ℝ))
    (hB : IntegrableOn (fun z : Spacetime n =>
      (F.metric (-z.2)).pullbackVolumeDensity e z.1 * u (e z.1, z.2) *
        (-Canonical.timeDeriv (spacetimeChartPullback e φ) z -
          (F.connection (-z.2)).laplacian
            (fun y => spacetimeChartPullback e φ (e.symm y, z.2)) (e z.1)))
      (e.source ×ˢ Ioi (0 : ℝ))) :
    weakPairing F u φ = -(∫ z in e.source ×ˢ Ioi (0 : ℝ),
      (F.metric (-z.2)).pullbackVolumeDensity e z.1 * u (e z.1, z.2) *
        (-Canonical.timeDeriv (spacetimeChartPullback e φ) z -
          (F.connection (-z.2)).laplacian
            (fun y => spacetimeChartPullback e φ (e.symm y, z.2)) (e z.1))) := by
  let B := fun z : Spacetime n =>
    (F.metric (-z.2)).pullbackVolumeDensity e z.1 * u (e z.1, z.2) *
      (-Canonical.timeDeriv (spacetimeChartPullback e φ) z -
        (F.connection (-z.2)).laplacian
          (fun y => spacetimeChartPullback e φ (e.symm y, z.2)) (e z.1))
  have hs' := hs.trans (prod_mono Subset.rfl (subset_univ (Ioi (0 : ℝ))))
  have hOp : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (testOperator F φ) := by
    apply contMDiff_testOperator_of_tsupport_subset F hφ
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    change -z.2 ∈ interior (Iio (0 : ℝ))
    rw [interior_Iio]
    change -z.2 < 0
    have ht : 0 < z.2 := (hs hz).2
    linarith
  have hslice (τ : ℝ) (hτ : 0 < τ) :
      (∫ x, u (x, τ) * testOperator F φ (x, τ) ∂(F.metric (-τ)).volumeMeasure) =
        -(∫ x in e.source, B (x, τ)) := by
    have huτ : Continuous (fun x => u (x, τ)) := by
      rw [← continuousOn_univ]
      exact hu.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x _ => ⟨mem_univ _, hτ⟩)
    have hOpτ : Continuous (fun x => testOperator F φ (x, τ)) :=
      hOp.continuous.comp (continuous_id.prodMk continuous_const)
    have hout : ∀ x ∉ e.target, u (x, τ) * testOperator F φ (x, τ) = 0 := by
      intro x hx
      rw [testOperator_eq_zero_of_notMem_tsupport F (fun h => hx (hs h).1), mul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout,
      (F.metric (-τ)).integral_target_eq_integral_pullback_density e he hei
        (f := fun x => u (x, τ) * testOperator F φ (x, τ))
        ((huτ.mul hOpτ).continuousOn), ← integral_neg]
    apply setIntegral_congr_fun e.open_source.measurableSet
    intro x hx
    dsimp only [B]
    rw [coordinate_heatTest_eq_neg_testOperator F e he hφ hc hs' hx]
    ring
  have houttime : ∀ τ ∉ Ioi (0 : ℝ),
      (∫ x, u (x, τ) * testOperator F φ (x, τ) ∂(F.metric (-τ)).volumeMeasure) = 0 := by
    intro τ hτ
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun x => by
      change u (x, τ) * testOperator F φ (x, τ) = 0
      rw [testOperator_eq_zero_of_notMem_tsupport F (fun h => hτ (hs h).2), mul_zero]
  have hBprod : Integrable B ((volume.restrict e.source).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [Measure.prod_restrict]
    exact hB
  have hFubini : (∫ z in e.source ×ˢ Ioi (0 : ℝ), B z) =
      ∫ τ in Ioi (0 : ℝ), ∫ x in e.source, B (x, τ) := by
    change (∫ z, B z ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
      (volume : Measure ℝ)).restrict (e.source ×ˢ Ioi (0 : ℝ))) = _
    rw [← Measure.prod_restrict, integral_prod_symm B hBprod]
  change weakPairing F u φ = -(∫ z in e.source ×ˢ Ioi (0 : ℝ), B z)
  rw [weakPairing, ← setIntegral_eq_integral_of_forall_compl_eq_zero houttime, hFubini,
    ← integral_neg]
  exact setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => hslice τ hτ)

end Measure
end PoincareConjecture.RicciFlow.ConjugateHeat
