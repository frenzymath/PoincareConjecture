import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.ChartCompactRanges









set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {a b : ℝ} {F : RicciFlow n M (Icc a b)}



theorem m65IntrinsicChartField_compact_finiteRange {κ : Type*}
    {circumference : κ → ℝ} (P : ∀ k, M62.CircleProductData F (circumference k))
    (c : ∀ k, ℝ → ℝ → (P k).charts.Point) (p : M) {r s : ℝ}
    (hsub : Icc r s ⊆ Ioo a b) {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hbound : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ k t x, t ∈ Icc r s →
      ((P k).flow.metric t).tangentNorm (c k x t)
        (m65IntrinsicTangentJet (P k).flow (c k) j t x) ≤ B)
    (N : ℕ) (hN : 0 < N) :
    ∃ C : Set (Fin N → EuclideanSpace ℝ (Fin n) × ℝ), IsCompact C ∧
      (∀ z ∈ C, (z ⟨0, hN⟩).2 ∈ Ioo a b ∧
        (z ⟨0, hN⟩).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target) ∧
      ∀ k t x, t ∈ Icc r s → (c k x t).1 ∈ K →
        (fun l : Fin N => m65IntrinsicChartField (P k) (c k) p l t x) ∈ C := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let e := chartAt E p
  let H : Set (E × ℝ) := (fun z : ℝ × E => (z.2, z.1)) '' (Icc r s ×ˢ (e '' K))
  have hH : IsCompact H := (isCompact_Icc.prod
    (hK.image_of_continuousOn (e.continuousOn.mono hKs))).image
      (continuous_snd.prodMk continuous_fst)
  have hHd : ∀ z ∈ H, z.2 ∈ Ioo a b ∧ z.1 ∈ e.target := by
    rintro z ⟨⟨t, y⟩, ⟨ht, q, hq, hqy⟩, rfl⟩
    refine ⟨hsub ht, ?_⟩
    change y ∈ e.target
    change e q = y at hqy
    rw [← hqy]
    exact e.map_source (hKs hq)
  choose B hB hb using fun j =>
    m65IntrinsicChartField_uniform_zero P c p hsub hK hKs hbound j
  let C : Set (Fin N → E × ℝ) :=
    {z | ∀ l : Fin N, z l ∈ Metric.closedBall 0 (B l)} ∩ (fun z => z ⟨0, hN⟩) ⁻¹' H
  have heval : Continuous (fun z : Fin N → E × ℝ => z ⟨0, hN⟩) := continuous_apply _
  have hC : IsCompact C :=
    (isCompact_pi_infinite (fun l : Fin N => isCompact_closedBall (0 : E × ℝ) (B l))).inter_right
      (hH.isClosed.preimage heval)
  refine ⟨C, hC, fun z hz => hHd _ hz.2, ?_⟩
  intro k t x ht hx
  constructor
  · intro l
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hb l k t x ht hx
  · exact ⟨(t, e (c k x t).1), ⟨ht, ⟨_, hx, rfl⟩⟩, rfl⟩



theorem m65IntrinsicSpatialOperator_compact_range {κ : Type*}
    {circumference : κ → ℝ} (P : ∀ k, M62.CircleProductData F (circumference k))
    (c : ∀ k, ℝ → ℝ → (P k).charts.Point) (p : M) {r s : ℝ}
    (hsub : Icc r s ⊆ Ioo a b) {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hbound : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ k t x, t ∈ Icc r s →
      ((P k).flow.metric t).tangentNorm (c k x t)
        (m65IntrinsicTangentJet (P k).flow (c k) j t x) ≤ B)
    (hv : ∃ B : ℝ, 0 ≤ B ∧ ∀ k t x, t ∈ Icc r s →
      |curveSpeed (P k).flow (c k) t x| ≤ B) (j : ℕ) :
    ∃ C : Set (ℝ × (Fin (j + 2) → EuclideanSpace ℝ (Fin n) × ℝ)), IsCompact C ∧
      C ⊆ m65IntrinsicSpatialDomain (a := a) (b := b) p j ∧
      ∀ k t x, t ∈ Icc r s → (c k x t).1 ∈ K →
        (curveSpeed (P k).flow (c k) t x,
          fun l : Fin (j + 2) => m65IntrinsicChartField (P k) (c k) p l t x) ∈ C := by
  obtain ⟨C, hC, hCd, hCr⟩ :=
    m65IntrinsicChartField_compact_finiteRange P c p hsub hK hKs hbound (j + 2) (by omega)
  obtain ⟨B, _hB, hb⟩ := hv
  refine ⟨Metric.closedBall 0 B ×ˢ C, (isCompact_closedBall 0 B).prod hC,
    fun z hz => hCd z.2 hz.2, ?_⟩
  intro k t x ht hx
  exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    using hb k t x ht, hCr k t x ht hx⟩

end PoincareConjecture
