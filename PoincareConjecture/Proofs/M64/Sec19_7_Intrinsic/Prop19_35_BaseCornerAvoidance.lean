import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AnnularCornerChart
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LipschitzCorner

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Matrix ENNReal
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_constrained_minimizer_avoids_annular_base_corner
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0)
    (hind : LinearIndependent ℝ
      (![deriv alpha 0, deriv beta 0] : Fin 2 → AnnulusCoordinates))
    {W U V : Set AnnulusCoordinates} (hW : IsCompact W) (hpW : alpha 0 ∉ W)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B ∪ W)
    (hfV : frontier V = frontier U)
    (hnorm : ‖alpha 0‖ = 1) (hinward : 0 < inner ℝ (alpha 0) (deriv beta 0))
    (hsub : closure U ⊆ standardAnnulusDomain)
    {gamma : ℝ → AnnulusCoordinates} {L : ℝ}
    (hc : ContinuousOn gamma (Icc 0 L))
    (hconf : MapsTo gamma (Icc 0 L) (closure U))
    (hlip : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      G.edist (gamma s) (gamma t) ≤ ENNReal.ofReal |s - t|)
    (hmin : ∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L, a ≤ b →
      ∀ tau : ℝ → AnnulusCoordinates, ContinuousOn tau (Icc 0 1) →
        tau 0 = gamma a → tau 1 = gamma b → MapsTo tau (Icc 0 1) (closure U) →
        ENNReal.ofReal (b - a) ≤ m64IntrinsicCurveVariation G tau 0 1)
    {u : ℝ} (hu : u ∈ Ioo 0 L) : gamma u ≠ alpha 0 := by
  obtain ⟨H, h0, hHbase, hH, hHi, hregion⟩ :=
    m64Intrinsic_exists_annular_corner_chart ha hb hA hB hai hbi hbase hind
      hW hpW hU hV hdisj hfU hfV hnorm hinward hsub
  let e := collarParameterEquiv
  let C := (ConvexCone.positive ℝ (ℝ × ℝ)).comap e.toLinearEquiv.toLinearMap
  have hC : IsClosed (C : Set AnnulusCoordinates) :=
    isClosed_le continuous_const e.continuous
  have hzero : (0 : AnnulusCoordinates) ∈ C := by change 0 ≤ e 0; simp
  have hsalient : C.Salient := by
    intro z hz hne hnz
    have hpos : (0 : ℝ × ℝ) ≤ e z := hz
    have hneg : (0 : ℝ × ℝ) ≤ e (-z) := hnz
    rw [map_neg, neg_nonneg] at hneg
    apply hne
    apply e.injective
    rw [map_zero]
    exact le_antisymm hneg hpos
  have hregionC : ∀ᶠ z in 𝓝 (0 : AnnulusCoordinates), H z ∈ closure U ↔ z ∈ C := by
    filter_upwards [hregion] with z hz
    exact hz
  simpa only [hHbase] using
    m64Intrinsic_constrained_minimizer_avoids_salient_corner G hc hconf hlip hmin
      H h0 hH hHi C hC hzero hsalient hregionC hu

end PoincareConjecture
