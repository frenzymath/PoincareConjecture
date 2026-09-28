import PoincareConjecture.Proofs.M76.Wall.InteriorArcSegments
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ArcEndpointLocalization
import PoincareConjecture.Proofs.M76.Wall.Mathlib.DistinctRayStraightening
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection
import PoincareConjecture.Proofs.M76.Rigidity.CenteredHalfspaceCharts










set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph





theorem exists_interior_arc_pair_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X E)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    {f : ℝ → X} (hf : PolyhedralPLInCharts e f (Icc (0 : ℝ) 1))
    (hi : InjOn f (Icc (0 : ℝ) 1)) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    {W : Set X} (hW : IsOpen W) (hxW : f a ∈ W) :
    ∃ (G : OpenPartialHomeomorph X E) (w : E), w ≠ 0 ∧
      f a ∈ G.source ∧ G.source ⊆ W ∧ G (f a) = 0 ∧
      (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid E) ∧
      ∀ y ∈ G.source, y ∈ f '' Icc (0 : ℝ) 1 ↔ ∃ r : ℝ, G y = r • w := by
  obtain ⟨i, hix⟩ := hcover (f a)
  obtain ⟨B, hBs, hzero, hBcompat, _⟩ :=
    exists_centered_compatible_halfspace_chart e (e i) (fun j => hcompat j i)
      (f a) (0 : E →ᴬ[ℝ] ℝ) (by rfl)
  have hxB : f a ∈ B.source := hBs.symm.subset hix
  obtain ⟨u, v, hu, hv, hne, δm, hδm, δp, hδp, hmapm, hmapp, hformm, hformp⟩ :=
    hf.exists_interior_chart_vectors hi ha B hBcompat hxB hzero
  let fm : ℝ → X := fun t => f (a - a * t)
  let fp : ℝ → X := fun t => f (a + (1 - a) * t)
  have ham : MapsTo (fun t : ℝ => a - a * t) (Icc 0 1) (Icc 0 1) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2, ha.1, ha.2]
  have hap : MapsTo (fun t : ℝ => a + (1 - a) * t) (Icc 0 1) (Icc 0 1) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2, ha.1, ha.2]
  have hcm : ContinuousOn fm (Icc (0 : ℝ) 1) :=
    hf.continuousOn.comp
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn ham
  have hcp : ContinuousOn fp (Icc (0 : ℝ) 1) :=
    hf.continuousOn.comp
      (continuous_const.add (continuous_const.mul continuous_id)).continuousOn hap
  have him : InjOn fm (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    have heq := hi (ham hs) (ham ht) hst
    exact (mul_left_cancel₀ ha.1.ne') (by linarith)
  have hip : InjOn fp (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    have heq := hi (hap hs) (hap ht) hst
    exact (mul_left_cancel₀ (sub_pos.mpr ha.2).ne') (by linarith)
  have hm0 : fm 0 = f a := by simp [fm]
  have hp0 : fp 0 = f a := by simp [fp]
  obtain ⟨Um, hUm, hxm, hUmW, hraym⟩ := B.exists_endpoint_arc_neighborhood hcm him
    (by simpa only [hm0] using hxB) (by simpa only [hm0] using hzero)
    hδm.1 hδm.2.le hu hmapm hformm hW (by simpa only [hm0] using hxW)
  obtain ⟨Up, hUp, hxp, _, hrayp⟩ := B.exists_endpoint_arc_neighborhood hcp hip
    (by simpa only [hp0] using hxB) (by simpa only [hp0] using hzero)
    hδp.1 hδp.2.le hv hmapp hformp hW (by simpa only [hp0] using hxW)
  have hsplit : f '' Icc (0 : ℝ) 1 = fm '' Icc 0 1 ∪ fp '' Icc 0 1 := by
    ext y
    constructor
    · rintro ⟨t, ht, hft⟩
      by_cases hta : t ≤ a
      · have hs : (a - t) / a ∈ Icc (0 : ℝ) 1 :=
          ⟨div_nonneg (sub_nonneg.mpr hta) ha.1.le,
            (div_le_iff₀ ha.1).mpr (by nlinarith [ht.1])⟩
        refine Or.inl ⟨(a - t) / a, hs, ?_⟩
        change f (a - a * ((a - t) / a)) = y
        rw [mul_div_cancel₀ _ ha.1.ne', sub_sub_cancel]
        exact hft
      · have hpos : 0 < 1 - a := sub_pos.mpr ha.2
        have hs : (t - a) / (1 - a) ∈ Icc (0 : ℝ) 1 :=
          ⟨div_nonneg (by linarith) hpos.le,
            (div_le_iff₀ hpos).mpr (by nlinarith [ht.2])⟩
        refine Or.inr ⟨(t - a) / (1 - a), hs, ?_⟩
        change f (a + (1 - a) * ((t - a) / (1 - a))) = y
        rw [mul_div_cancel₀ _ hpos.ne', show a + (t - a) = t by ring]
        exact hft
    · rintro (⟨t, ht, hft⟩ | ⟨t, ht, hft⟩)
      · exact ⟨a - a * t, ham ht, hft⟩
      · exact ⟨a + (1 - a) * t, hap ht, hft⟩
  obtain ⟨ell, w, hellu, _, hw, H, hHPL, hHzero, _, hHm, hHp⟩ :=
    ContinuousLinearMap.exists_straightening_of_distinct_rays hu hv hne
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, map_zero] at hw
    exact zero_ne_one hw
  let U := Um ∩ Up
  have hU : IsOpen U := hUm.inter hUp
  have hxU : f a ∈ U := ⟨by simpa only [hm0] using hxm, by simpa only [hp0] using hxp⟩
  let G := (B.restrOpen U hU).trans H.toOpenPartialHomeomorph
  have hGs : G.source = B.source ∩ U := by
    change (B.source ∩ U) ∩ B ⁻¹' (univ : Set E) = B.source ∩ U
    rw [preimage_univ, inter_univ]
  refine ⟨G, w, hw0, hGs.symm.subset ⟨hxB, hxU⟩,
    fun _ hy => (hUmW (hGs.subset hy).2.1).2, ?_, ?_, ?_⟩
  · change H (B (f a)) = 0
    rw [hzero, hHzero]
  · intro j
    have hj := (e j).piecewiseAffine_compatible_restrOpen_right B (hBcompat j) hU
    simpa only [G, ← OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid E).trans hj hHPL
  · intro y hy
    have hyU := (hGs.subset hy).2
    change y ∈ f '' Icc (0 : ℝ) 1 ↔ ∃ r : ℝ, H (B y) = r • w
    rw [hsplit, mem_union, hraym y hyU.1, hrayp y hyU.2]
    constructor
    · rintro (⟨t, ht, hyt⟩ | ⟨t, ht, hyt⟩)
      · refine ⟨t * ell u, ?_⟩
        rw [hyt, hHm t ht]
      · refine ⟨t, ?_⟩
        rw [hyt, hHp t ht]
    · rintro ⟨r, hyr⟩
      by_cases hr : r ≤ 0
      · have ht : 0 ≤ r / ell u := div_nonneg_of_nonpos hr hellu.le
        refine Or.inl ⟨r / ell u, ht, H.injective ?_⟩
        rw [hHm _ ht, div_mul_cancel₀ _ hellu.ne]
        exact hyr
      · have hrpos : 0 ≤ r := (lt_of_not_ge hr).le
        exact Or.inr ⟨r, hrpos, H.injective (hyr.trans (hHp r hrpos).symm)⟩

end OpenPartialHomeomorph
