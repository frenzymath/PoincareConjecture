import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CommonCornerCaps













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Triangles PoincareConjecture.Topology.Surface
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture





theorem m64Intrinsic_exists_four_corner_cap_coordinates
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (h0 : (0 : ℝ × ℝ) ∈ H.source)
    (hH : ContDiffOn ℝ ∞ H H.source) (hHi : ContDiffOn ℝ ∞ H.symm H.target)
    {T : ℝ} (hT : 0 < T) :
    ∃ (r : ℝ) (F : Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
      (W : Set AnnulusCoordinates),
      0 < r ∧ r ≤ T ∧ IsOpen W ∧ H 0 ∈ W ∧ W ⊆ H.target ∧
      ∀ i,
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ (F i).source ∧
        ContDiffOn ℝ ∞ (F i) (F i).source ∧
        ContDiffOn ℝ ∞ (F i).symm (F i).target ∧
        (∀ s ∈ Icc (0 : ℝ) r, F i (s, 0) = H (sectorParameterEquiv 0 i (s, 0))) ∧
        (∀ s ∈ Icc (0 : ℝ) r, F i (0, s) = H (sectorParameterEquiv 0 i (0, s))) ∧
        (∀ t : ℝ, F i ((1 - t) * r, t * r) =
          (1 - t) • F i (r, 0) + t • F i (0, r)) ∧
        F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆
          H '' (H.source ∩ (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) ∧
        W ∩ H '' (H.source ∩ (sectorParameterEquiv 0 i) ''
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) ⊆
            F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} := by
  classical
  let J (i : Bool × Bool) := (sectorParameterEquiv 0 i).toOpenPartialHomeomorph.trans H
  have hJ0 (i : Bool × Bool) : (0 : ℝ × ℝ) ∈ (J i).source := by
    refine ⟨mem_univ _, ?_⟩
    change sectorParameterEquiv 0 i 0 ∈ H.source
    simpa only [sectorParameterEquiv_zero] using h0
  have hJ (i : Bool × Bool) : ContDiffOn ℝ ∞ (J i) (J i).source :=
    hH.comp (contDiff_sectorParameterEquiv 0 i).contDiffOn (fun _ hz => hz.2)
  have hJi (i : Bool × Bool) : ContDiffOn ℝ ∞ (J i).symm (J i).target :=
    (contDiff_sectorParameterEquiv_symm 0 i).comp_contDiffOn
      (hHi.mono (fun _ hz => hz.1))
  choose rho hrho hcaps using fun i => exists_smooth_coordinate_corner_caps (J i)
    (hJ0 i) (hJ i) (hJi i)
  let mu := Finset.univ.inf' Finset.univ_nonempty rho
  have hmu : 0 < mu := by simpa [mu] using hrho
  have hmule (i : Bool × Bool) : mu ≤ rho i := Finset.inf'_le rho (Finset.mem_univ i)
  let r := min (mu / 2) (T / 2)
  have hr : 0 < r := lt_min (half_pos hmu) (half_pos hT)
  have hrT : r ≤ T := (min_le_right _ _).trans (half_le_self hT.le)
  have hrrho (i : Bool × Bool) : r < rho i :=
    ((min_le_left _ _).trans_lt (half_lt_self hmu)).trans_le (hmule i)
  choose F hsource htarget hF hFi hfirst hsecond hchord hbase hsub V hV hpV hVt hcover using
    fun i => hcaps i r hr (hrrho i)
  let W := ⋂ i, V i
  have hW : IsOpen W := isOpen_iInter_of_finite hV
  have hWV (i : Bool × Bool) : W ⊆ V i := iInter_subset _ i
  have hpW : H 0 ∈ W := by
    apply mem_iInter.mpr
    intro i
    simpa only [J, OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply,
      sectorParameterEquiv_zero] using hpV i
  have hWt : W ⊆ H.target := fun _ hz => (hVt (false, false) (hWV _ hz)).1
  have hsector (i : Bool × Bool) :
      J i '' ((J i).source ∩ {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) =
        H '' (H.source ∩ (sectorParameterEquiv 0 i) ''
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) := by
    ext z
    constructor
    · rintro ⟨q, ⟨hq, hqpos⟩, rfl⟩
      exact ⟨sectorParameterEquiv 0 i q, ⟨hq.2, q, hqpos, rfl⟩, rfl⟩
    · rintro ⟨q, ⟨hq, p, hp, rfl⟩, rfl⟩
      exact ⟨p, ⟨⟨mem_univ _, hq⟩, hp⟩, rfl⟩
  have hsmall (i : Bool × Bool) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) r) : |s| < rho i := by
    rw [abs_of_nonneg hs.1]
    exact hs.2.trans_lt (hrrho i)
  refine ⟨r, F, W, hr, hrT, hW, hpW, hWt, ?_⟩
  intro i
  refine ⟨hsource i, hF i, hFi i, fun s hs => hfirst i s (hsmall i hs),
    fun s hs => hsecond i s (hsmall i hs), ?_, ?_, ?_⟩
  · intro t
    rw [hfirst i r (hsmall i ⟨hr.le, le_rfl⟩), hsecond i r (hsmall i ⟨hr.le, le_rfl⟩)]
    have h := hchord i (1 - t)
    rw [show 1 - (1 - t) = t by ring, add_comm] at h
    exact h
  · simpa only [hsector] using hsub i
  · intro z hz
    apply hcover i
    exact ⟨hWV i hz.1, (hsector i).symm ▸ hz.2⟩

end PoincareConjecture
