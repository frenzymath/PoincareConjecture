import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith












set_option autoImplicit false

open Set Function

namespace PoincareConjecture.M25.Topology3D




theorem exists_fixedTail_openLine_separation {Z : Type*}
    [TopologicalSpace Z] {K : Set Z} (hK : IsCompact K)
    {R r : ℝ} (_hR : 0 < R) (hr : 0 < r)
    (f : Z → ℝ → ℝ × ℝ)
    (hf : ContinuousOn (fun p : Z × ℝ => f p.1 p.2) (K ×ˢ univ))
    (hinj : ∀ z ∈ K, Injective (f z))
    (htail : ∀ z ∈ K, ∀ u, R ≤ |u| → f z u = (u, 0)) :
    ∃ η : ℝ, 0 < η ∧ ∀ z ∈ K, ∀ s t : ℝ,
      r ≤ |s - t| → η ≤ dist (f z s) (f z t) := by
  have hcore : ContinuousOn (fun p : Z × ℝ => |(f p.1 p.2).1|)
      (K ×ˢ Icc (-R) R) :=
    hf.fst.abs.mono (fun _ hp => ⟨hp.1, mem_univ _⟩)
  obtain ⟨B, hB⟩ := (hK.prod isCompact_Icc).bddAbove_image hcore
  let L : ℝ := max R B + r + 1
  have hRL : R < L := by
    dsimp only [L]
    linarith [le_max_left R B]
  have hBL : B + r < L := by
    dsimp only [L]
    linarith [le_max_right R B]
  let C : Set (Z × (ℝ × ℝ)) :=
    (K ×ˢ (Icc (-L) L ×ˢ Icc (-L) L)) ∩
      {p | r ≤ |p.2.1 - p.2.2|}
  have hC : IsCompact C :=
    (hK.prod (isCompact_Icc.prod isCompact_Icc)).inter_right
      (isClosed_le continuous_const (continuous_snd.fst.sub continuous_snd.snd).abs)
  have hf₁ : ContinuousOn (fun p : Z × (ℝ × ℝ) => f p.1 p.2.1) C :=
    hf.comp (continuous_fst.prodMk continuous_snd.fst).continuousOn
      (fun _ hp => ⟨hp.1.1, mem_univ _⟩)
  have hf₂ : ContinuousOn (fun p : Z × (ℝ × ℝ) => f p.1 p.2.2) C :=
    hf.comp (continuous_fst.prodMk continuous_snd.snd).continuousOn
      (fun _ hp => ⟨hp.1.1, mem_univ _⟩)
  have hd : ContinuousOn
      (fun p : Z × (ℝ × ℝ) => dist (f p.1 p.2.1) (f p.1 p.2.2)) C :=
    continuous_dist.continuousOn.comp (hf₁.prodMk hf₂) (mapsTo_univ _ _)
  have hpos : ∀ p ∈ C, 0 < dist (f p.1 p.2.1) (f p.1 p.2.2) := by
    rintro ⟨z, s, t⟩ ⟨⟨hz, _, _⟩, hgap⟩
    apply dist_pos.mpr
    intro heq
    have hst : s = t := hinj z hz heq
    change r ≤ |s - t| at hgap
    rw [hst, sub_self, abs_zero] at hgap
    linarith
  obtain ⟨η, hη, hηle⟩ := hC.exists_forall_le' hd hpos
  have hfar (z : Z) (hz : z ∈ K) (s t : ℝ) (hs : L < |s|)
      (hst : r ≤ |s - t|) : r ≤ dist (f z s) (f z t) := by
    rw [htail z hz s (hRL.trans hs).le]
    by_cases ht : R ≤ |t|
    · rw [htail z hz t ht]
      simpa only [dist_prod_same_right, Real.dist_eq] using hst
    · have htcore : t ∈ Icc (-R) R := abs_le.mp (le_of_not_ge ht)
      have hbound : |(f z t).1| ≤ B :=
        hB ⟨(z, t), ⟨hz, htcore⟩, rfl⟩
      have hcoord : |s - (f z t).1| ≤ dist (s, 0) (f z t) := by
        rw [Prod.dist_eq, Real.dist_eq]
        exact le_max_left _ _
      have hsum : |s| ≤ |s - (f z t).1| + |(f z t).1| := by
        simpa only [sub_zero] using (_root_.abs_sub_le s (f z t).1 0)
      linarith
  refine ⟨min η r, lt_min hη hr, ?_⟩
  intro z hz s t hst
  by_cases hs : |s| ≤ L
  · by_cases ht : |t| ≤ L
    · exact (min_le_left η r).trans
        (hηle (z, s, t) ⟨⟨hz, abs_le.mp hs, abs_le.mp ht⟩, hst⟩)
    · have hsep := hfar z hz t s (lt_of_not_ge ht)
        (by simpa only [abs_sub_comm] using hst)
      exact (min_le_right η r).trans (by simpa only [dist_comm] using hsep)
  · exact (min_le_right η r).trans (hfar z hz s t (lt_of_not_ge hs) hst)





theorem exists_fixedTail_openLine_injection_tolerance {Z : Type*}
    [TopologicalSpace Z] {K : Set Z} (hK : IsCompact K)
    {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (f : Z → ℝ → ℝ × ℝ)
    (hf : ContinuousOn (fun p : Z × ℝ => f p.1 p.2) (K ×ˢ univ))
    (hinj : ∀ z ∈ K, Injective (f z))
    (htail : ∀ z ∈ K, ∀ u, R ≤ |u| → f z u = (u, 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : Z → ℝ → ℝ × ℝ,
      (∀ z ∈ K, ∀ u : ℝ, dist (g z u) (f z u) < ε) →
      (∀ z ∈ K, ∀ s t : ℝ, |s - t| < r → g z s = g z t → s = t) →
      ∀ z ∈ K, Injective (g z) := by
  obtain ⟨η, hη, hsep⟩ :=
    exists_fixedTail_openLine_separation hK hR hr f hf hinj htail
  refine ⟨η / 3, by linarith, ?_⟩
  intro g hclose hlocal z hz s t heq
  by_cases hnear : |s - t| < r
  · exact hlocal z hz s t hnear heq
  · have hgap := hsep z hz s t (le_of_not_gt hnear)
    have hleft : dist (f z s) (g z s) < η / 3 := by
      rw [dist_comm]
      exact hclose z hz s
    have hright : dist (g z s) (f z t) < η / 3 := by
      rw [heq]
      exact hclose z hz t
    linarith [dist_triangle (f z s) (g z s) (f z t)]

end PoincareConjecture.M25.Topology3D
