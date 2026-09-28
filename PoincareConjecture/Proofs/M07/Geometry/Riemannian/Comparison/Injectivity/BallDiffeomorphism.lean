import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Lifting.Bounded
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.Coverage
import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_partialDiffeomorph_of_injOn_of_nonsingular
    {e : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hbij : ∀ x ∈ U, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e x))
    (hinj : InjOn e U) :
    ∃ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      (Φ : EuclideanSpace ℝ (Fin n) → M) = e ∧ Φ.source = U ∧ Φ.target = e '' U := by
  let q := hinj.toPartialEquiv e U
  let H := OpenPartialHomeomorph.ofContinuousOpenRestrict q he.continuousOn
    (isLocalHomeomorph_domRestrict_of_nonsingular hU he hbij).isOpenMap hU
  have hinverse : ContMDiffOn (𝓡 n) (𝓡 n) ∞ H.symm H.target := by
    intro y hy
    have hx := H.map_target hy
    have hleft : ∀ᶠ z in 𝓝 (H.symm y), H.symm (e z) = z := by
      filter_upwards [H.open_source.mem_nhds hx] with z hz
      exact H.left_inv hz
    have h := Poincare.contMDiffAt_of_local_left_inverse
      (he.contMDiffAt (hU.mem_nhds hx)) (hbij _ hx) hleft
    have hright : e (H.symm y) = y := H.right_inv hy
    rw [hright] at h
    exact h.contMDiffWithinAt
  let Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞ :=
    { H.toPartialEquiv with
      open_source := H.open_source
      open_target := H.open_target
      contMDiffOn_toFun := he
      contMDiffOn_invFun := hinverse }
  exact ⟨Φ, rfl, rfl, rfl⟩

namespace RiemannianMetric

theorem image_ball_and_radial_edist_eq_of_injOn
    (g : RiemannianMetric n M) (p : M)
    {e : EuclideanSpace ℝ (Fin n) → M} {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hcover : e '' Poincare.VolumeComparison.localMinimizingSet
      (fun v => g.edist p (e v)) R = g.ball p R)
    (hupper : ∀ v ∈ Metric.ball 0 ρ, g.edist p (e v) ≤ ENNReal.ofReal ‖v‖)
    (hinj : InjOn e (Metric.ball 0 ρ)) :
    e '' Metric.ball 0 ρ = g.ball p ρ ∧
      ∀ v ∈ Metric.ball 0 ρ, g.edist p (e v) = ENNReal.ofReal ‖v‖ := by
  have hcoverρ := Poincare.VolumeComparison.image_localMinimizingSet_inter_ball
    g p hcover hρ hρR
  have hmaps : MapsTo e (Metric.ball 0 ρ) (g.ball p ρ) := by
    intro v hv
    apply (hupper v hv).trans_lt
    exact (ENNReal.ofReal_lt_ofReal_iff hρ).mpr (by simpa using hv)
  refine ⟨?_, ?_⟩
  · apply Set.Subset.antisymm hmaps.image_subset
    rw [← hcoverρ]
    exact image_mono inter_subset_right
  · intro v hv
    have hq := hmaps hv
    rw [← hcoverρ] at hq
    obtain ⟨w, ⟨hw, hwρ⟩, heq⟩ := hq
    have hwv : w = v := hinj hwρ hv heq
    simpa only [hwv, mem_ofPred_eq] using hw.2

theorem exists_ball_partialDiffeomorph_of_precompact_exponential [T2Space M]
    (g : RiemannianMetric n M) (p : M) {R ρ : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (e : EuclideanSpace ℝ (Fin n) → M)
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v)) L.toContinuousLinearMap 0)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Metric.ball 0 R})
    (hupper : ∀ v ∈ Metric.ball 0 R, g.edist p (e v) ≤ ENNReal.ofReal ‖v‖)
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hbij : ∀ v ∈ Metric.ball 0 ρ, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e v))
    (hinj : InjOn e (Metric.closedBall 0 ρ)) :
    ∃ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      (Φ : EuclideanSpace ℝ (Fin n) → M) = e ∧
      Φ.source = Metric.ball 0 ρ ∧ Φ.target = g.ball p ρ ∧
      ∀ v ∈ Metric.ball 0 ρ, g.edist p (e v) = ENNReal.ofReal ‖v‖ := by
  have hcover := Poincare.VolumeComparison.image_localMinimizingSet_eq_ball
    g p hR hcompact L e hL he0 hed hgeo
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ρ ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball hρR.le
  have hinj' := hinj.mono Metric.ball_subset_closedBall
  obtain ⟨himage, hmin⟩ := g.image_ball_and_radial_edist_eq_of_injOn p hρ hρR.le hcover
    (fun v hv => hupper v (hsub hv)) hinj'
  obtain ⟨Φ, hΦ, hsource, htarget⟩ := exists_partialDiffeomorph_of_injOn_of_nonsingular
    Metric.isOpen_ball (he.mono hsub) hbij hinj'
  exact ⟨Φ, hΦ, hsource, htarget.trans himage, hmin⟩

end RiemannianMetric

end PoincareConjecture
