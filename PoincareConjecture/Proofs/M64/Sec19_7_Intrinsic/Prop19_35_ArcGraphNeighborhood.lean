import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcReparametrization













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture




theorem m64Intrinsic_exists_arc_graph_neighborhood
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {a b p : ℝ}
    (hinj : InjOn gamma (Icc a b)) (hp : p ∈ Ioo a b) (hregular : deriv gamma p ≠ 0)
    {K : Set AnnulusCoordinates} (hK : IsCompact K) (hpK : gamma p ∉ K) :
    ∃ (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)) (h : ℝ → ℝ)
      (X : Set ℝ) (W : Set AnnulusCoordinates),
      IsOpen X ∧ ContDiffOn ℝ ∞ h X ∧ IsOpen W ∧ gamma p ∈ W ∧
      ∀ z ∈ W, (L z).1 ∈ X ∧
        (z ∈ gamma '' Icc a b ∪ K ↔ (L z).2 = h (L z).1) := by
  obtain ⟨l, r, G, L, h, hlp, hpr, hsource, _, _, _,
    _, hGi, _, hh, hgraph, _, _, _⟩ :=
    exists_graph_coordinates_of_positive_projection hg (le_refl p)
      (v := deriv gamma p) (by
        intro x hx
        have hx' : x = p := le_antisymm hx.2 hx.1
        subst x
        exact real_inner_self_pos.mpr hregular)
  have hpG : p ∈ G.source := by rw [hsource]; exact ⟨hlp, hpr⟩
  let tail := gamma '' (Icc a b \ G.source)
  have htail : IsClosed tail :=
    ((isCompact_Icc.diff G.open_source).image hg.continuous).isClosed
  have hpTail : gamma p ∉ tail := by
    rintro ⟨s, hs, hsp⟩
    exact hs.2 ((hinj hs.1 (Ioo_subset_Icc_self hp) hsp) ▸ hpG)
  have hpTarget : (L (gamma p)).1 ∈ G.target := by
    rw [hgraph p hpG]
    exact G.map_source hpG
  let phi := fun z : AnnulusCoordinates => G.symm (L z).1
  have hphi : ContinuousAt phi (gamma p) :=
    (hGi.contDiffAt (G.open_target.mem_nhds hpTarget)).continuousAt.comp
      (f := fun z : AnnulusCoordinates => (L z).1)
      L.continuous.fst.continuousAt
  have hphip : phi (gamma p) = p := by
    dsimp only [phi]
    rw [hgraph p hpG]
    exact G.left_inv hpG
  have htarget : ∀ᶠ z in 𝓝 (gamma p), (L z).1 ∈ G.target :=
    L.continuous.fst.continuousAt.eventually (G.open_target.mem_nhds hpTarget)
  have hparam : ∀ᶠ z in 𝓝 (gamma p), phi z ∈ Ioo a b :=
    hphi.eventually (by rw [hphip]; exact isOpen_Ioo.mem_nhds hp)
  have hnear : {z : AnnulusCoordinates | (L z).1 ∈ G.target ∧
      phi z ∈ Ioo a b ∧ z ∉ tail ∧ z ∉ K} ∈ 𝓝 (gamma p) := by
    filter_upwards [htarget, hparam, htail.isOpen_compl.mem_nhds hpTail,
      hK.isClosed.isOpen_compl.mem_nhds hpK] with z hz hp' ht hk
    exact ⟨hz, hp', ht, hk⟩
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp hnear
  refine ⟨L, h, G.target, W, G.open_target, hh, hW, hpW, ?_⟩
  intro z hz
  obtain ⟨hzTarget, hzParam, hzTail, hzK⟩ := hWsub hz
  refine ⟨hzTarget, ?_⟩
  constructor
  · rintro (⟨s, hs, hsz⟩ | hzk)
    · have hsG : s ∈ G.source := by
        by_contra h
        exact hzTail ⟨s, ⟨hs, h⟩, hsz⟩
      rw [← hsz, hgraph s hsG]
    · exact False.elim (hzK hzk)
  · intro hzg
    refine Or.inl ⟨phi z, Ioo_subset_Icc_self hzParam, ?_⟩
    apply L.injective
    change L (gamma (G.symm (L z).1)) = L z
    rw [hgraph _ (G.map_target hzTarget), G.right_inv hzTarget]
    exact Prod.ext rfl hzg.symm

end PoincareConjecture
