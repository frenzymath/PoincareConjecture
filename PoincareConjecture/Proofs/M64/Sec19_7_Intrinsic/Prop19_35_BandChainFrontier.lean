import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandBoundaryGeometry













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture




theorem m64Intrinsic_band_chain_frontier
    {gamma d : ℝ → AnnulusCoordinates} {a b : ℝ} {n : ℕ}
    (c : Fin (n + 1) → ℝ) (hc : StrictMono c)
    (hfirst : c 0 = a) (hlast : c (Fin.last n) = b)
    (L : Fin n → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (G : Fin n → OpenPartialHomeomorph ℝ ℝ) (f : Fin n → ℝ → ℝ)
    (lengths : Fin (n + 1) → ℝ)
    (B : ∀ i : Fin n,
      ObliqueBandFaces
        (collarParameterEquiv.trans (L i).symm).toHomeomorph.toOpenPartialHomeomorph
        (f i) (G i (c i.castSucc)) (G i (c i.succ))
        (L i (d (c i.castSucc))).1 (L i (d (c i.castSucc))).2
        (L i (d (c i.succ))).1 (L i (d (c i.succ))).2
        (lengths i.castSucc) (lengths i.succ))
    (hboundary : ∀ i, (B i).lowerArc = gamma '' Icc (c i.castSucc) (c i.succ) ∧
      (B i).leftCut = segment ℝ (gamma (c i.castSucc))
        (gamma (c i.castSucc) + lengths i.castSucc • d (c i.castSucc)) ∧
      (B i).rightCut = segment ℝ (gamma (c i.succ))
        (gamma (c i.succ) + lengths i.succ • d (c i.succ)))
    (hadj : ∀ i j : Fin n, i.succ = j.castSucc →
      (B i).carrier ∩ (B j).carrier = segment ℝ (gamma (c i.succ))
        (gamma (c i.succ) + lengths i.succ • d (c i.succ))) :
    (∀ i j : Fin n, i.succ = j.castSucc →
      (fun u : ℝ => gamma (c i.succ) + u • d (c i.succ)) '' Ioo 0 (lengths i.succ) ⊆
        interior ((B i).carrier ∪ (B j).carrier)) ∧
    frontier (⋃ i, (B i).carrier) ⊆
      gamma '' Icc a b ∪ (⋃ i, (B i).polygonalTop) ∪
        (⋃ i, ⋃ (_ : c i.castSucc = a), (B i).leftCut) ∪
          (⋃ i, ⋃ (_ : c i.succ = b), (B i).rightCut) := by
  classical
  have hleftBase (i : Fin n) :
      (L i).symm (G i (c i.castSucc), f i (G i (c i.castSucc))) = gamma (c i.castSucc) := by
    have h := m64Intrinsic_band_left_cut (L i).symm (B i)
    simp only [Prod.eta, (L i).symm_apply_apply] at h
    exact m64Intrinsic_segment_base_eq_of_same_direction (h.symm.trans (hboundary i).2.1)
  have hrightBase (i : Fin n) :
      (L i).symm (G i (c i.succ), f i (G i (c i.succ))) = gamma (c i.succ) := by
    have h := m64Intrinsic_band_right_cut (L i).symm (B i)
    simp only [Prod.eta, (L i).symm_apply_apply] at h
    exact m64Intrinsic_segment_base_eq_of_same_direction (h.symm.trans (hboundary i).2.2)
  have hcancel (i j : Fin n) (hij : i.succ = j.castSucc) :
      (fun u : ℝ => gamma (c i.succ) + u • d (c i.succ)) '' Ioo 0 (lengths i.succ) ⊆
        interior ((B i).carrier ∪ (B j).carrier) := by
    have hi : (fun u : ℝ => gamma (c i.succ) + u • d (c i.succ)) ''
        Ioo 0 (lengths i.succ) ⊆ ((B i).endpointEdge true).map '' Ioo (0 : ℝ) 1 := by
      simpa only [Prod.eta, (L i).symm_apply_apply, hrightBase] using
        m64Intrinsic_band_open_right_ray (L i).symm (B i)
    have hj : (fun u : ℝ => gamma (c i.succ) + u • d (c i.succ)) ''
        Ioo 0 (lengths i.succ) ⊆ ((B j).endpointEdge false).map '' Ioo (0 : ℝ) 1 := by
      simpa only [Prod.eta, (L j).symm_apply_apply, hleftBase, hij] using
        m64Intrinsic_band_open_left_ray (L j).symm (B j)
    apply (subset_inter hi hj).trans
    apply (B i).shared_endpointCut_subset_interior_union (B j) true false
    · rw [(B i).endpointEdge_image, (B j).endpointEdge_image]
      simp only [Bool.false_eq_true, ↓reduceIte, (hboundary i).2.2, (hboundary j).2.1, hij]
    · rw [hadj i j hij, ← (hboundary i).2.2]
      exact fun _ hz => (B i).outer_boundaries_subset_frontier (Or.inr hz)
  have htop (i : Fin n) :
      gamma (c i.castSucc) + lengths i.castSucc • d (c i.castSucc) ∈ (B i).polygonalTop ∧
      gamma (c i.succ) + lengths i.succ • d (c i.succ) ∈ (B i).polygonalTop := by
    constructor
    · simpa only [Prod.eta, (L i).symm_apply_apply, hleftBase] using
        m64Intrinsic_band_left_tip_mem_top (L i).symm (B i)
    · simpa only [Prod.eta, (L i).symm_apply_apply, hrightBase] using
        m64Intrinsic_band_right_tip_mem_top (L i).symm (B i)
  have hcut (k : Fin (n + 1)) : c k ∈ Icc a b := by
    constructor
    · simpa only [hfirst] using hc.monotone (Fin.zero_le k)
    · simpa only [hlast] using hc.monotone (Fin.le_last k)
  refine ⟨hcancel, ?_⟩
  intro p hp
  obtain ⟨i, hi⟩ := mem_iUnion.mp
    (Poincare.Topology.frontier_iUnion_subset_iUnion_frontier_of_isClosed
      (fun i => (B i).carrier) (fun i => (B i).isClosed_carrier) hp)
  have hnot (j k : Fin n) : p ∉ interior ((B j).carrier ∪ (B k).carrier) := by
    intro hint
    exact hp.2 (interior_mono
      (union_subset (subset_iUnion _ j) (subset_iUnion _ k)) hint)
  rw [(B i).frontier_carrier] at hi
  rcases hi with ((hlower | hupper) | hleft) | hright
  · apply Or.inl (Or.inl (Or.inl ?_))
    rw [(hboundary i).1] at hlower
    obtain ⟨s, hs, rfl⟩ := hlower
    exact ⟨s, ⟨(hcut i.castSucc).1.trans hs.1, hs.2.trans (hcut i.succ).2⟩, rfl⟩
  · exact Or.inl (Or.inl (Or.inr (mem_iUnion.mpr ⟨i, hupper⟩)))
  · by_cases hia : c i.castSucc = a
    · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hia, hleft⟩⟩))
    rw [(hboundary i).2.1, ← m64Intrinsic_ray_image_eq_segment _ _
      (B i).left_length_pos.le] at hleft
    obtain ⟨u, hu, hup⟩ := hleft
    by_cases hu0 : u = 0
    · apply Or.inl (Or.inl (Or.inl ?_))
      exact ⟨c i.castSucc, hcut _, by simpa only [hu0, zero_smul, add_zero] using hup⟩
    by_cases hutop : u = lengths i.castSucc
    · apply Or.inl (Or.inl (Or.inr (mem_iUnion.mpr ⟨i, ?_⟩)))
      exact hup ▸ (hutop.symm ▸ (htop i).1)
    have hi0 : 0 < i.val := by
      by_contra hn
      have hzero : i.castSucc = 0 := Fin.ext (by dsimp; omega)
      exact hia (hzero ▸ hfirst)
    let j : Fin n := ⟨i.val - 1, by omega⟩
    have hji : j.succ = i.castSucc := Fin.ext (by dsimp [j]; omega)
    apply False.elim (hnot j i (hcancel j i hji ?_))
    rw [hji]
    exact ⟨u, ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), lt_of_le_of_ne hu.2 hutop⟩, hup⟩
  · by_cases hib : c i.succ = b
    · exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hib, hright⟩⟩)
    rw [(hboundary i).2.2, ← m64Intrinsic_ray_image_eq_segment _ _
      (B i).right_length_pos.le] at hright
    obtain ⟨u, hu, hup⟩ := hright
    by_cases hu0 : u = 0
    · apply Or.inl (Or.inl (Or.inl ?_))
      exact ⟨c i.succ, hcut _, by simpa only [hu0, zero_smul, add_zero] using hup⟩
    by_cases hutop : u = lengths i.succ
    · apply Or.inl (Or.inl (Or.inr (mem_iUnion.mpr ⟨i, ?_⟩)))
      exact hup ▸ (hutop.symm ▸ (htop i).2)
    have hilast : i.val + 1 < n := by
      by_contra hn
      have hlast' : i.succ = Fin.last n := Fin.ext (by dsimp; omega)
      exact hib (hlast' ▸ hlast)
    let j : Fin n := ⟨i.val + 1, hilast⟩
    have hij : i.succ = j.castSucc := Fin.ext rfl
    apply False.elim (hnot i j (hcancel i j hij ?_))
    exact ⟨u, ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), lt_of_le_of_ne hu.2 hutop⟩, hup⟩

end PoincareConjecture
