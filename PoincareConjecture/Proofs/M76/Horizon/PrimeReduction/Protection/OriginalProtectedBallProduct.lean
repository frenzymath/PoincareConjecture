import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.ProtectedBallCubeProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalAttachmentAnnulus
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)
local notation "J" => Icc (-1 : ℝ) 1
local notation "Square" => (J ×ˢ J : Set P2)
local notation "Cube" => (Square ×ˢ J : Set P3)

theorem mem_frontier_closed_product_cube (z : Cube) :
    (z : P3) ∈ frontier Cube ↔
      (|z.val.1.1| = 1 ∨ |z.val.1.2| = 1) ∨ |z.val.2| = 1 := by
  rw [frontier_prod_eq, frontier_prod_eq]
  simp only [closure_prod_eq, isClosed_Icc.closure_eq,
    frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1), mem_union, mem_prod,
    mem_insert_iff, mem_singleton_iff, z.property.1.1, z.property.1.2,
    z.property.2, true_and, and_true,
    abs_eq (by norm_num : (0 : ℝ) ≤ 1)]
  tauto

theorem HamiltonMarkedProtectedBall.exists_original_protected_ball_product
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 2) :
    ∃ (p : P3 → LatticeHandleAmbient ι κ L) (G : Cube ≃ₜ D),
      PolyhedralPLInCharts e p Cube ∧
      (∀ z : Cube, p z = (G z : LatticeHandleAmbient ι κ L)) ∧
      InjOn p Cube ∧ p '' Cube = D ∧
      (∀ z ∈ Cube, p z ∈ hamiltonAttachingBlock ι κ L (3 / 2) ↔
        |z.1.1| = 1 ∨ |z.1.2| = 1) ∧
      (∀ z ∈ Cube, p z ∈ frontier D ↔ z ∈ frontier Cube) ∧
      (∀ i : Bool, ∀ z ∈ Cube,
        p z ∈ p '' (Square ×ˢ {if i then (1 : ℝ) else -1}) ↔
          z.2 = if i then 1 else -1) ∧
      Disjoint (p '' (Square ×ˢ {(1 : ℝ)})) (p '' (Square ×ˢ {(-1 : ℝ)})) ∧
      ((p '' (Square ×ˢ {(1 : ℝ)})) ∪ (p '' (Square ×ˢ {(-1 : ℝ)}))) ∪
        hamiltonAttachingBlock ι κ L (3 / 2) = frontier D := by
  classical
  obtain ⟨s, F, K, A, H, g, J0, B, ann, hFc, hF, hfi, hK, hA, hKs, hA0, hA1, hA2,
      hH, hgc, hg, hgPL, hball, _, hJA0, hJA2, _, _, hJs, hJmark,
      _, _, _, _, hann, _, _⟩ := b.exists_original_attachment_annulus_model he hdim hi
  have hmark : D ∩ frontier (latticeHandleDomain ι κ L) =
      hamiltonAttachingBlock ι κ L (3 / 2) := by
    rcases b.position with ⟨hzero, _⟩ | ⟨_, _, _, _, _, hm⟩
    · omega
    · exact hm
  have hattachR : hamiltonAttachingBlock ι κ L (3 / 2) ⊆ latticeHandleDomain ι κ L := by
    rw [← hmark]
    exact inter_subset_left.trans b.subset_domain
  have hattachS : hamiltonAttachingBlock ι κ L (3 / 2) ⊆ frontier D := by
    rw [← hmark]
    intro x hx
    exact ((b.ball.frontier_inter_eq_of_subset b.subset_domain).symm.subset hx).1
  obtain ⟨d, r, Q, hQ, hd, _, _, hlat, hends, hboundary⟩ :=
    exists_protected_ball_cube_product hball ann hann (SimplicialComplex.space_subset_of_le hJA2)
  obtain ⟨q, hq, hqval⟩ := hQ
  have hqA (z : P3) (hz : z ∈ Cube) : q z ∈ (A 1).space := by
    rw [← hqval ⟨z, hz⟩]
    exact (Q ⟨z, hz⟩).property
  have hqK : MapsTo q Cube K.space := fun z hz =>
    SimplicialComplex.space_subset_of_le (hA 1).1 (hqA z hz)
  let p : P3 → LatticeHandleAmbient ι κ L := fun z => g (q z)
  have hpPL : PolyhedralPLInCharts e p Cube := by
    obtain ⟨T, hT, hTs, hfaces⟩ := hq
    rw [← hTs]
    exact hgPL.comp_finitePiecewiseAffineOn T hT ⟨T, hT, rfl, hfaces⟩
      (fun z hz => hqK (hTs.subset hz))
  have hgF (x : LatticeHandleAmbient ι κ L) (hx : x ∈ latticeHandleDomain ι κ L) :
      (g (F x) : LatticeHandleAmbient ι κ L) = x := by
    have hFx : F x ∈ K.space := hKs.symm.subset ⟨x, hx, rfl⟩
    rw [hg ⟨F x, hFx⟩]
    have hh : (⟨F x, hFx⟩ : K.space) = H ⟨x, hx⟩ := Subtype.ext (hH ⟨x, hx⟩).symm
    rw [hh, H.symm_apply_apply]
  have hFg (z : s → ℝ × V3) (hz : z ∈ K.space) : F (g z) = z := by
    rw [hg ⟨z, hz⟩, ← hH (H.symm ⟨z, hz⟩), H.apply_symm_apply]
  have hpD (z : P3) (hz : z ∈ Cube) : p z ∈ D := by
    apply (original_model_mem_image_iff H F g hH hg b.subset_domain ⟨q z, hqK hz⟩).mpr
    exact hA1.subset (hqA z hz)
  have hpi : InjOn p Cube := by
    intro z hz w hw h
    have hh : q z = q w := by
      rw [← hFg (q z) (hqK hz), ← hFg (q w) (hqK hw)]
      exact congrArg F h
    have hQeq : Q ⟨z, hz⟩ = Q ⟨w, hw⟩ := Subtype.ext
      ((hqval ⟨z, hz⟩).trans (hh.trans (hqval ⟨w, hw⟩).symm))
    exact congrArg Subtype.val (Q.injective hQeq)
  have hpimage : p '' Cube = D := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hpD z hz
    · intro x hx
      have hFx : F x ∈ (A 1).space := hA1.symm.subset ⟨x, hx, rfl⟩
      let z := Q.symm ⟨F x, hFx⟩
      refine ⟨z, z.property, ?_⟩
      have hqz : q z = F x := (hqval z).symm.trans
        (congrArg Subtype.val (Q.apply_symm_apply _))
      exact (congrArg (fun y => (g y : LatticeHandleAmbient ι κ L)) hqz).trans
        (hgF x (b.subset_domain hx))
  let f : Cube → D := fun z => ⟨p z, hpD z z.property⟩
  have hfc : Continuous f := hpPL.continuousOn.domRestrict.subtype_mk _
  have hfb : Function.Bijective f := by
    constructor
    · intro z w h
      exact Subtype.ext (hpi z.property w.property
        (congrArg (fun x : D => (x : LatticeHandleAmbient ι κ L)) h))
    · intro x
      obtain ⟨z, hz, hzx⟩ := hpimage.symm.subset x.property
      exact ⟨⟨z, hz⟩, Subtype.ext hzx⟩
  let : CompactSpace Cube := isCompact_iff_compactSpace.mp
    ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc)
  let G : Cube ≃ₜ D := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f hfb) hfc
  have hpA (z : P3) (hz : z ∈ Cube) : p z ∈ hamiltonAttachingBlock ι κ L (3 / 2) ↔
      |z.1.1| = 1 ∨ |z.1.2| = 1 := by
    have hm := original_model_mem_image_iff H F g hH hg hattachR ⟨q z, hqK hz⟩
    change (g (q z) : LatticeHandleAmbient ι κ L) ∈ _ ↔ _
    rw [hm]
    change q z ∈ F '' hamiltonAttachingBlock ι κ L (3 / 2) ↔ _
    rw [← hJmark, ← hqval ⟨z, hz⟩]
    exact hlat ⟨z, hz⟩
  have hpfront (z : P3) (hz : z ∈ Cube) : p z ∈ frontier D ↔ z ∈ frontier Cube := by
    have hm := original_model_mem_image_iff H F g hH hg
      (b.ball.boundary_subset.trans b.subset_domain) ⟨q z, hqK hz⟩
    change (g (q z) : LatticeHandleAmbient ι κ L) ∈ _ ↔ _
    rw [hm]
    change q z ∈ F '' frontier D ↔ _
    rw [← hA2, ← hqval ⟨z, hz⟩, hboundary, mem_frontier_closed_product_cube ⟨z, hz⟩]
  have hendcube (i : Bool) : Square ×ˢ {if i then (1 : ℝ) else -1} ⊆ Cube := by
    rintro z ⟨hz, ht⟩
    refine ⟨hz, ?_⟩
    rw [show z.2 = if i then (1 : ℝ) else -1 from ht]
    cases i <;> norm_num
  have hpends (i : Bool) (z : P3) (hz : z ∈ Cube) :
      p z ∈ p '' (Square ×ˢ {if i then (1 : ℝ) else -1}) ↔
        z.2 = if i then 1 else -1 := by
    constructor
    · rintro ⟨w, hw, hwz⟩
      exact (hpi (hendcube i hw) hz hwz) ▸ hw.2
    · intro ht
      exact ⟨z, ⟨hz.1, ht⟩, rfl⟩
  refine ⟨p, G, hpPL, fun _ => rfl, hpi, hpimage, hpA, hpfront, hpends, ?_, ?_⟩
  · apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    have hh := congrArg Prod.snd (hpi (hendcube false hw) (hendcube true hz) hwz)
    have hz1 : z.2 = 1 := hz.2
    have hw1 : w.2 = -1 := hw.2
    linarith
  · ext x
    constructor
    · rintro ((⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩) | hx)
      · apply (hpfront z (hendcube true hz)).mpr
        apply (mem_frontier_closed_product_cube ⟨z, hendcube true hz⟩).mpr
        right
        rw [show z.2 = 1 from hz.2]
        norm_num
      · apply (hpfront z (hendcube false hz)).mpr
        apply (mem_frontier_closed_product_cube ⟨z, hendcube false hz⟩).mpr
        right
        rw [show z.2 = -1 from hz.2]
        norm_num
      · exact hattachS hx
    · intro hx
      obtain ⟨z, hz, rfl⟩ := hpimage.symm.subset (b.ball.boundary_subset hx)
      have hf := (mem_frontier_closed_product_cube ⟨z, hz⟩).mp ((hpfront z hz).mp hx)
      rcases hf with hlat | hheight
      · exact Or.inr ((hpA z hz).mpr hlat)
      · rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hheight with h | h
        · exact Or.inl (Or.inl ⟨z, ⟨hz.1, h⟩, rfl⟩)
        · exact Or.inl (Or.inr ⟨z, ⟨hz.1, h⟩, rfl⟩)

end PoincareConjecture.M76
