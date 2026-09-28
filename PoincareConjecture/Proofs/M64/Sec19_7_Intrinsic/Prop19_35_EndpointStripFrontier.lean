import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcStripSeparation









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture




theorem m64Intrinsic_exists_endpoint_strip_frontier_width
    {gamma : ℝ → AnnulusCoordinates} (hg : Continuous gamma) {A B a b : ℝ}
    (hinj : InjOn gamma (Icc A B)) (hab : a < b) (hcell : Icc a b ⊆ Icc A B)
    {E K U : Set AnnulusCoordinates} (hK : IsCompact K)
    (havoid : ∀ t ∈ Icc a b, gamma t ∉ K)
    (hfront : frontier U = gamma '' Icc A B ∪ E ∪ K)
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (G : OpenPartialHomeomorph ℝ ℝ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f G.target)
    (hI : Icc a b ⊆ G.source) (hmono : StrictMonoOn G G.source)
    (hgraph : ∀ t ∈ G.source, L (gamma t) = (G t, f (G t)))
    (himage : G '' Icc a b = Icc (G a) (G b))
    (htarget : Icc (G a) (G b) ⊆ G.target)
    {ua wa ub wb : ℝ} (P : TransverseGraphCuts f (G a) (G b) ua wa ub wb)
    {rho : ℝ} (hrho : 0 < rho) :
    let S := P.linearCoordinates L.symm G.open_target hf
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < rho → S (t, z) ∈ E → z = 0) →
    ∃ delta > 0, delta ≤ rho ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < delta →
        (t, z) ∈ S.source ∧ (S (t, z) ∈ frontier U ↔ z = 0) := by
  intro S hother
  have hGab := hmono (hI (left_mem_Icc.mpr hab.le)) (hI (right_mem_Icc.mpr hab.le)) hab
  have haxis := m64Intrinsic_graph_strip_axis_image L G hf hI hGab.le hgraph himage P
  let tail := gamma '' (Icc A B \ G.source)
  have htail : IsClosed tail := ((isCompact_Icc.diff G.open_source).image hg).isClosed
  let W := S.source ∩ S ⁻¹' (tail ∪ K)ᶜ
  have hW : IsOpen W := S.isOpen_inter_preimage (htail.union hK.isClosed).isOpen_compl
  let H := S.restrOpen W hW
  have haxisH (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (t, (0 : ℝ)) ∈ H.source := by
    have hs := P.linearCoordinates_axis_mem_source L.symm G.open_target hf hGab htarget ht
    refine ⟨hs, hs, ?_⟩
    have hp : S (t, 0) ∈ gamma '' Icc a b := haxis.subset ⟨t, ht, rfl⟩
    obtain ⟨s, hsab, hst⟩ := hp
    rintro (⟨u, hu, hut⟩ | hKpoint)
    · exact hu.2 ((hinj hu.1 (hcell hsab) (hut.trans hst.symm)) ▸ hI hsab)
    · exact havoid s hsab (hst ▸ hKpoint)
  obtain ⟨eta, heta, hstrip⟩ := exists_strip_source_width H haxisH
  refine ⟨min rho eta, lt_min hrho heta, min_le_left _ _, ?_⟩
  intro t ht z hz
  have hze : |z| < eta := hz.trans_le (min_le_right _ _)
  have hzr : |z| < rho := hz.trans_le (min_le_left _ _)
  have hq : (t, z) ∈ H.source := hstrip (show (t, z) ∈
    Icc (0 : ℝ) 1 ×ˢ Ioo (-eta) eta from ⟨ht, abs_lt.mp hze⟩)
  refine ⟨hq.1, ?_⟩
  constructor
  · intro hp
    rw [hfront] at hp
    rcases hp with (⟨s, hs, hsz⟩ | hpE) | hpK
    · have hsG : s ∈ G.source := by
        by_contra hn
        exact hq.2.2 (Or.inl ⟨s, ⟨hs, hn⟩, hsz⟩)
      have hzero : (L (S (t, z))).2 = f (L (S (t, z))).1 := by
        rw [← hsz, hgraph s hsG]
      change (L (P.linearCoordinates L.symm G.open_target hf (t, z))).2 =
        f (L (P.linearCoordinates L.symm G.open_target hf (t, z))).1 at hzero
      rw [P.linearCoordinates_apply, L.apply_symm_apply, P.coordinates_apply] at hzero
      exact add_eq_left.mp hzero
    · exact hother t ht z hzr hpE
    · exact False.elim (hq.2.2 (Or.inr hpK))
  · rintro rfl
    rw [hfront]
    exact Or.inl (Or.inl ((image_mono hcell) (haxis.subset ⟨t, ht, rfl⟩)))

end PoincareConjecture
