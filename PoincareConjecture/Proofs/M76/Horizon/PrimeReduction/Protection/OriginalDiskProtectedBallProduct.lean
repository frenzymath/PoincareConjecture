import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalProtectedBallProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalDiskAttachmentComplement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "Cube" => ((I ×ˢ I) ×ˢ I : Set P3)

theorem exists_cube_product_with_prescribed_disks_with_height
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Q S J B : Set E} (hball : IsFinitePLBallPair V3 Q S)
    (d r : Bool → Set E) (hd : ∀ i, IsFinitePLBallPair P2 (d i) (r i))
    (hdS : ∀ i, d i ⊆ S) (hdis : Disjoint (d false) (d true))
    (hcover : d false ∪ d true = J) (hrcover : r false ∪ r true = B)
    (ann : squareAnnulus 8 1 ≃ₜ (S \ (J \ B) : Set E)) (hann : ann.IsFinitePL)
    (hlo : ∀ z : squareAnnulus 8 1, depth 8 (z : P2) = -1 ↔ (ann z : E) ∈ r false)
    (hhi : ∀ z : squareAnnulus 8 1, depth 8 (z : P2) = 1 ↔ (ann z : E) ∈ r true) :
    ∃ G : Cube ≃ₜ Q, G.IsFinitePL ∧
      (∀ i (z : Cube), (G z : E) ∈ d i ↔ z.val.2 = if i then 1 else -1) ∧
      (∀ z : Cube, (G z : E) ∈ S ↔ z.val ∈ frontier Cube) ∧
      (∀ z : Cube, (G z : E) ∈ S \ (J \ B) ↔ |z.val.1.1| = 1 ∨ |z.val.1.2| = 1) ∧
      ∀ z : squareAnnulus 8 1,
        (G.symm ⟨ann z, hball.1 (ann z).property.1⟩).val.2 = depth 8 z := by
  classical
  let A := S \ (J \ B)
  have hmeet (i : Bool) : d i ∩ A = r i := by
    ext x
    constructor
    · rintro ⟨hxd, hxS, hx⟩
      have hxJ : x ∈ J := hcover.subset (by
        cases i
        · exact Or.inl hxd
        · exact Or.inr hxd)
      have hxB : x ∈ B := by by_contra hn; exact hx ⟨hxJ, hn⟩
      rcases hrcover.symm.subset hxB with h | h
      · cases i
        · exact h
        · exact False.elim (disjoint_left.mp hdis ((hd false).1 h) hxd)
      · cases i
        · exact False.elim (disjoint_left.mp hdis hxd ((hd true).1 h))
        · exact h
    · intro hx
      refine ⟨(hd i).1 hx, hdS i ((hd i).1 hx), ?_⟩
      rintro ⟨_, hnot⟩
      apply hnot
      apply hrcover.subset
      cases i
      · exact Or.inl hx
      · exact Or.inr hx
  have hrmark (i : Bool) : r i = (fun z : squareAnnulus 8 1 => (ann z : E)) ''
      {z | depth 8 z = if i then 1 else -1} := by
    have hm (z : squareAnnulus 8 1) : depth 8 (z : P2) = (if i then 1 else -1) ↔
        (ann z : E) ∈ r i := by
      cases i
      · exact hlo z
      · exact hhi z
    apply Subset.antisymm
    · intro x hx
      have hxA : x ∈ A := (hmeet i).symm.subset hx |>.2
      let z := ann.symm ⟨x, hxA⟩
      have hz : (ann z : E) = x := congrArg Subtype.val (ann.apply_symm_apply _)
      exact ⟨z, (hm z).mpr (hz.symm ▸ hx), hz⟩
    · rintro x ⟨z, hz, rfl⟩
      exact (hm z).mp hz
  have hS : A ∪ (d false ∪ d true) = S := by
    apply Subset.antisymm
    · exact union_subset sdiff_subset (union_subset (hdS false) (hdS true))
    · intro x hx
      by_cases hxJ : x ∈ J
      · exact Or.inr (hcover.symm.subset hxJ)
      · exact Or.inl ⟨hx, fun h => hxJ h.1⟩
  obtain ⟨a, ha, hamark, haheight⟩ := exists_attachment_annulus_product_with_height ann hann r hrmark
  have hb : IsFinitePLBallPair V3 Q (A ∪ (d false ∪ d true)) := hS.symm ▸ hball
  obtain ⟨P, hP, hkeep, hPc, hPa⟩ := hb.exists_product_extending_annulus d r hd hmeet hdis.symm a ha hamark
  have hS' : (d true ∪ d false) ∪ A = S := by rw [← hS]; ac_rfl
  obtain ⟨G, hG, hlat, hends, hfront, hheight⟩ := exists_cube_coordinates_of_marked_ball_product_with_height
    d r P hP (hd false) hS' hPc hPa
  refine ⟨G, hG, hends, fun z => (hfront z).trans (mem_frontier_closed_product_cube z).symm, hlat, ?_⟩
  intro z
  let x : Q := ⟨ann z, hball.1 (ann z).property.1⟩
  have hv := congrArg Prod.snd (hkeep (ann z))
  have hh := hheight (G.symm x)
  rw [G.apply_symm_apply] at hh
  have haH := haheight (ann z)
  rw [ann.symm_apply_apply] at haH
  change (P x : E × ℝ).2 = (a (ann z) : E × ℝ).2 at hv
  change (G.symm x).val.2 = depth 8 z
  linarith

theorem exists_cube_product_with_prescribed_disks
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Q S J B : Set E} (hball : IsFinitePLBallPair V3 Q S)
    (d r : Bool → Set E) (hd : ∀ i, IsFinitePLBallPair P2 (d i) (r i))
    (hdS : ∀ i, d i ⊆ S) (hdis : Disjoint (d false) (d true))
    (hcover : d false ∪ d true = J) (hrcover : r false ∪ r true = B)
    (ann : squareAnnulus 8 1 ≃ₜ (S \ (J \ B) : Set E)) (hann : ann.IsFinitePL)
    (hlo : ∀ z : squareAnnulus 8 1, depth 8 (z : P2) = -1 ↔ (ann z : E) ∈ r false)
    (hhi : ∀ z : squareAnnulus 8 1, depth 8 (z : P2) = 1 ↔ (ann z : E) ∈ r true) :
    ∃ G : Cube ≃ₜ Q, G.IsFinitePL ∧
      (∀ i (z : Cube), (G z : E) ∈ d i ↔ z.val.2 = if i then 1 else -1) ∧
      (∀ z : Cube, (G z : E) ∈ S ↔ z.val ∈ frontier Cube) := by
  obtain ⟨G, hG, hends, hfront, _⟩ := exists_cube_product_with_prescribed_disks_with_height
    hball d r hd hdS hdis hcover hrcover ann hann hlo hhi
  exact ⟨G, hG, hends, hfront⟩

theorem exists_original_cube_transport
    {X α E : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : α → OpenPartialHomeomorph X V3} {R D : Set X} (hDR : D ⊆ R)
    (K : SimplicialComplex ℝ E) (F : X → E) (H : R ≃ₜ K.space) (g : E → R)
    (hKs : K.space = F '' R) (hH : ∀ x, (H x : E) = F x)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (Q : Cube ≃ₜ (F '' D)) (hQ : Q.IsFinitePL) :
    ∃ (p : P3 → X) (G : Cube ≃ₜ D),
      PolyhedralPLInCharts e p Cube ∧ (∀ z : Cube, p z = (G z : X)) ∧
      InjOn p Cube ∧ p '' Cube = D ∧
      ∀ U : Set X, U ⊆ R → ∀ z : Cube, p z ∈ U ↔ (Q z : E) ∈ F '' U := by
  classical
  obtain ⟨q, hq, hqval⟩ := hQ
  have hqK : MapsTo q Cube K.space := by
    intro z hz
    rw [← hqval ⟨z, hz⟩, hKs]
    exact image_mono hDR (Q ⟨z, hz⟩).property
  let p : P3 → X := fun z => g (q z)
  have hpPL : PolyhedralPLInCharts e p Cube := by
    obtain ⟨T, hT, hTs, hfaces⟩ := hq
    rw [← hTs]
    exact hgPL.comp_finitePiecewiseAffineOn T hT ⟨T, hT, rfl, hfaces⟩
      (fun z hz => hqK (hTs.subset hz))
  have hmem (U : Set X) (hU : U ⊆ R) (z : Cube) : p z ∈ U ↔ (Q z : E) ∈ F '' U := by
    have hm := original_model_mem_image_iff H F g hH hg hU ⟨q z, hqK z.property⟩
    change (g (q z) : X) ∈ U ↔ _
    rw [hm]
    change q z ∈ F '' U ↔ _
    rw [← hqval z]
  have hpD (z : P3) (hz : z ∈ Cube) : p z ∈ D :=
    (hmem D hDR ⟨z, hz⟩).mpr (Q ⟨z, hz⟩).property
  have hFg (z : E) (hz : z ∈ K.space) : F (g z) = z := by
    rw [hg ⟨z, hz⟩, ← hH (H.symm ⟨z, hz⟩), H.apply_symm_apply]
  have hpi : InjOn p Cube := by
    intro z hz w hw h
    have hh : q z = q w := by
      rw [← hFg (q z) (hqK hz), ← hFg (q w) (hqK hw)]
      exact congrArg F h
    exact congrArg Subtype.val (Q.injective (Subtype.ext
      ((hqval ⟨z, hz⟩).trans (hh.trans (hqval ⟨w, hw⟩).symm))))
  have hpimage : p '' Cube = D := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hpD z hz
    · intro x hx
      have hFx : F x ∈ F '' D := ⟨x, hx, rfl⟩
      let z := Q.symm ⟨F x, hFx⟩
      have hqz : q z = F x := (hqval z).symm.trans
        (congrArg Subtype.val (Q.apply_symm_apply _))
      refine ⟨z, z.property, ?_⟩
      change (g (q z) : X) = x
      rw [hg ⟨q z, hqK z.property⟩]
      have hh : (⟨q z, hqK z.property⟩ : K.space) = H ⟨x, hDR hx⟩ :=
        Subtype.ext (hqz.trans (hH ⟨x, hDR hx⟩).symm)
      rw [hh, H.symm_apply_apply]
  let f : Cube → D := fun z => ⟨p z, hpD z z.property⟩
  have hfc : Continuous f := hpPL.continuousOn.domRestrict.subtype_mk _
  have hfb : Function.Bijective f := by
    constructor
    · intro z w h
      exact Subtype.ext (hpi z.property w.property (congrArg (fun x : D => (x : X)) h))
    · intro x
      obtain ⟨z, hz, hzx⟩ := hpimage.symm.subset x.property
      exact ⟨⟨z, hz⟩, Subtype.ext hzx⟩
  let : CompactSpace Cube := isCompact_iff_compactSpace.mp
    ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc)
  let G : Cube ≃ₜ D := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f hfb) hfc
  exact ⟨p, G, hpPL, fun _ => rfl, hpi, hpimage, hmem⟩

theorem HamiltonMarkedProtectedBall.exists_original_disk_protected_ball_product_with_lateral
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    ∃ (p : P3 → LatticeHandleAmbient ι κ L) (G : Cube ≃ₜ D),
      PolyhedralPLInCharts e p Cube ∧
      (∀ z : Cube, p z = (G z : LatticeHandleAmbient ι κ L)) ∧
      InjOn p Cube ∧ p '' Cube = D ∧
      (∀ z ∈ Cube, p z ∈ frontier D ↔ z ∈ frontier Cube) ∧
      (∀ z ∈ Cube, p z ∈ frontier (latticeHandleDomain ι κ L) ↔ |z.2| = 1) ∧
      (∀ z ∈ Cube, p z ∈ hamiltonAttachingBlock ι κ L (3 / 2) ↔ |z.2| = 1) ∧
      (∀ i : Bool, ∀ z ∈ Cube,
        p z ∈ hamiltonMarkedProjection ι κ L ''
          ({fun _ : ι => if i then (1 : ℝ) else -1} ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) ↔
            z.2 = if i then 1 else -1) ∧
      ∀ z ∈ Cube, p z ∈ frontier D \ (hamiltonAttachingBlock ι κ L (3 / 2) \
          hamiltonMarkedProjection ι κ L ''
            (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2))) ↔
        |z.1.1| = 1 ∨ |z.1.2| = 1 := by
  classical
  obtain ⟨hι⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hi
  let : Unique ι := hι
  obtain ⟨s, F, K, J, B, H, g, d, r, ann, C, hFc, hF, hfi, hK, hKs, hH, hgc, hg,
      hgPL, hball, hJK, hBJ, hJ, hB, hJmark, hBmark, hd, hdis, hcover, hrcover,
      hann, hlo, hhi, _⟩ := b.exists_original_disk_complement_model he (by omega)
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
  have hdS (i : Bool) : d i ⊆ F '' frontier D := by
    intro x hx
    apply image_mono hattachS
    apply hcover.subset
    cases i
    · exact Or.inl hx
    · exact Or.inr hx
  obtain ⟨Q, hQ, hends, hfront, hlat, _⟩ := exists_cube_product_with_prescribed_disks_with_height
    hball d r (fun i => (hd i).1) hdS hdis (hcover.trans hJmark.symm) hrcover ann hann hlo hhi
  obtain ⟨p, G, hp, hval, hpi, himage, hmem⟩ := exists_original_cube_transport
    b.subset_domain K F H g hKs hH hg hgPL Q hQ
  have hpA (z : P3) (hz : z ∈ Cube) : p z ∈ hamiltonAttachingBlock ι κ L (3 / 2) ↔
      |z.2| = 1 := by
    rw [hmem _ hattachR ⟨z, hz⟩, ← hcover, mem_union, hends, hends]
    simp only [Bool.false_eq_true, if_false, if_true, abs_eq (by norm_num : (0 : ℝ) ≤ 1)]
    exact or_comm
  refine ⟨p, G, hp, hval, hpi, himage, ?_, ?_, hpA, ?_, ?_⟩
  · intro z hz
    exact (hmem _ (b.ball.boundary_subset.trans b.subset_domain) ⟨z, hz⟩).trans (hfront ⟨z, hz⟩)
  · intro z hz
    have hpD : p z ∈ D := himage.subset ⟨z, hz, rfl⟩
    have hm : p z ∈ frontier (latticeHandleDomain ι κ L) ↔
        p z ∈ hamiltonAttachingBlock ι κ L (3 / 2) := by
      rw [← hmark]
      exact ⟨fun hx => ⟨hpD, hx⟩, fun hx => hx.2⟩
    exact hm.trans (hpA z hz)
  · intro i z hz
    have hsub : hamiltonMarkedProjection ι κ L ''
        ({fun _ : ι => if i then (1 : ℝ) else -1} ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) ⊆
          latticeHandleDomain ι κ L := by
      apply Subset.trans _ hattachR
      apply image_mono
      apply prod_mono _ subset_rfl
      apply singleton_subset_iff.mpr
      rw [mem_sphere_zero_iff_norm, pi_norm_const, Real.norm_eq_abs]
      cases i <;> norm_num
    rw [hmem _ hsub ⟨z, hz⟩, ← (hd i).2.1]
    exact hends i ⟨z, hz⟩
  · intro z hz
    have hrimR : hamiltonMarkedProjection ι κ L ''
        (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2)) ⊆
        latticeHandleDomain ι κ L := by
      apply Subset.trans _ hattachR
      exact image_mono (prod_mono subset_rfl sphere_subset_closedBall)
    change p z ∈ frontier D \ (hamiltonAttachingBlock ι κ L (3 / 2) \ _) ↔ _
    simp only [mem_sdiff]
    rw [hmem _ (b.ball.boundary_subset.trans b.subset_domain) ⟨z,hz⟩,
      hmem _ hattachR ⟨z,hz⟩,hmem _ hrimR ⟨z,hz⟩,←hJmark,←hBmark]
    exact hlat ⟨z,hz⟩

theorem HamiltonMarkedProtectedBall.exists_original_disk_protected_ball_product
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    ∃ (p : P3 → LatticeHandleAmbient ι κ L) (G : Cube ≃ₜ D),
      PolyhedralPLInCharts e p Cube ∧
      (∀ z : Cube, p z = (G z : LatticeHandleAmbient ι κ L)) ∧
      InjOn p Cube ∧ p '' Cube = D ∧
      (∀ z ∈ Cube, p z ∈ frontier D ↔ z ∈ frontier Cube) ∧
      (∀ z ∈ Cube, p z ∈ frontier (latticeHandleDomain ι κ L) ↔ |z.2| = 1) ∧
      (∀ z ∈ Cube, p z ∈ hamiltonAttachingBlock ι κ L (3 / 2) ↔ |z.2| = 1) ∧
      ∀ i : Bool, ∀ z ∈ Cube,
        p z ∈ hamiltonMarkedProjection ι κ L ''
          ({fun _ : ι => if i then (1 : ℝ) else -1} ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) ↔
            z.2 = if i then 1 else -1 := by
  obtain ⟨p,G,hp,hval,hpi,himage,hfront,hboundary,hattach,hends,_⟩ :=
    b.exists_original_disk_protected_ball_product_with_lateral he hdim hi
  exact ⟨p,G,hp,hval,hpi,himage,hfront,hboundary,hattach,hends⟩

end PoincareConjecture.M76
