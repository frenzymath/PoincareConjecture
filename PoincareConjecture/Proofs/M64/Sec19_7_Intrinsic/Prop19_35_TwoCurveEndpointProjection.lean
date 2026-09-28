import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CurveEndpointProjection





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology Manifold ContDiff Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem m64Intrinsic_two_unit_curves_endpoint_projection_length_le
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (he : ContDiff ℝ ∞ e) {height : ℝ → ℝ} (hh : Measurable height)
    {S : Set ℝ} (hS : MeasurableSet S) {l u : ℝ} (hSsub : S ⊆ Icc l u)
    (hinj : InjOn (fun a => e !₂[a, height a]) S)
    (hregular : ∀ a ∈ S, Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, height a]))
    {target₁ target₂ : ℝ → AnnulusCoordinates}
    (htarget₁ : ContDiff ℝ ∞ target₁) (htarget₂ : ContDiff ℝ ∞ target₂)
    {a₁ b₁ a₂ b₂ : ℝ} (hab₁ : a₁ ≤ b₁) (hab₂ : a₂ ≤ b₂)
    (hinj₁ : InjOn target₁ (Icc a₁ b₁)) (hinj₂ : InjOn target₂ (Icc a₂ b₂))
    (hunit₁ : ∀ t ∈ Icc a₁ b₁,
      N.metric.inner (target₁ t) (deriv target₁ t) (deriv target₁ t) = 1)
    (hunit₂ : ∀ t ∈ Icc a₂ b₂,
      N.metric.inner (target₂ t) (deriv target₂ t) (deriv target₂ t) = 1)
    (hend : ∀ s ∈ S, e !₂[s, height s] ∈ target₁ '' Icc a₁ b₁ ∪ target₂ '' Icc a₂ b₂)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ s ∈ S, ∀ v : AnnulusCoordinates,
      c ^ 2 * (intrinsicBoundarySpeed N.metric 1 s ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        N.metric.inner (e !₂[s, height s])
          (fderiv ℝ e !₂[s, height s] v) (fderiv ℝ e !₂[s, height s] v)) :
    c * (∫ s in S, intrinsicBoundarySpeed N.metric 1 s) ≤ (b₁ - a₁) + (b₂ - a₂) := by
  let C := (fun s => e !₂[s, height s]) ⁻¹' (target₁ '' Icc a₁ b₁)
  have hgraph : Measurable (fun s => (!₂[s, height s] : AnnulusCoordinates)) := by fun_prop
  have hC : MeasurableSet C :=
    (isCompact_Icc.image htarget₁.continuous).isClosed.measurableSet.preimage
      (he.continuous.measurable.comp hgraph)
  have hfirst := m64Intrinsic_unit_curve_endpoint_projection_length_le N e he hh
    (hS.inter hC) (inter_subset_left.trans hSsub) (hinj.mono inter_subset_left)
    (fun s hs => hregular s hs.1) htarget₁ hab₁ hinj₁ hunit₁
    (fun _ hs => hs.2) hc (fun s hs => hbound s hs.1)
  have hsecond := m64Intrinsic_unit_curve_endpoint_projection_length_le N e he hh
    (hS.diff hC) (sdiff_subset.trans hSsub) (hinj.mono sdiff_subset)
    (fun s hs => hregular s hs.1) htarget₂ hab₂ hinj₂ hunit₂
    (fun s hs => (hend s hs.1).resolve_left hs.2) hc (fun s hs => hbound s hs.1)
  have hs := (m64Intrinsic_contDiff_boundarySpeed N one_ne_zero).continuous
  have hadd := integral_inter_add_sdiff (μ := volume) hC (hs.integrableOn_Icc.mono_set hSsub)
  calc
    _ = c * ((∫ s in S ∩ C, intrinsicBoundarySpeed N.metric 1 s) +
        ∫ s in S \ C, intrinsicBoundarySpeed N.metric 1 s) := by rw [hadd]
    _ = _ + _ := mul_add _ _ _
    _ ≤ _ := add_le_add hfirst hsecond

end PoincareConjecture
