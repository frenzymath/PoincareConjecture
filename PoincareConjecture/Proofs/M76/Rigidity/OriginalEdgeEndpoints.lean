import PoincareConjecture.Proofs.M76.Rigidity.OriginalTriangleFibers
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBoundaryEdgeFiber
import PoincareConjecture.Proofs.M76.Rigidity.OriginalEdgeZeroArcs

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  {T : OriginalProperDiskTriangulation e R j}

structure OriginalEdgeEndpoints (F : OriginalTriangleFibers T)
    (s : Finset (T.index → ℝ × V3)) where
  endpoint : Bool → (T.index → ℝ × V3)
  distinct : endpoint false ≠ endpoint true
  base : IsFinitePLBallPair ℝ (T.dualRegion s ∩ (T.marked 2).space)
    {endpoint false, endpoint true}
  base_rim : T.dualRegionRim s ∩ (T.marked 2).space = {endpoint false, endpoint true}
  fiber : Bool → ℝ → (T.index → ℝ × V3)
  piecewiseAffine : ∀ i, FinitePiecewiseAffineOn (fiber i) I
  injective : ∀ i, InjOn (fiber i) I
  central : ∀ i, fiber i 0 = endpoint i
  image_subset : ∀ i, fiber i '' I ⊆ T.dualRegionRim s
  disjoint : Disjoint (fiber false '' I) (fiber true '' I)
  positive : ∀ i, ∀ p : (T.marked 2).vertices,
    (p : T.index → ℝ × V3) ∈ s → ∀ r ∈ I, 0 ≤ T.height p (fiber i r) ↔ 0 ≤ r
  negative : ∀ i, ∀ p : (T.marked 2).vertices,
    (p : T.index → ℝ × V3) ∈ s → ∀ r ∈ I, T.height p (fiber i r) ≤ 0 ↔ r ≤ 0
  coface : ∀ t ∈ (T.marked 2).faces, t.card = 3 → s ⊆ t →
    ∃ i, endpoint i = t.centroid ℝ id ∧ EqOn (fiber i) (F.map t) I
  boundary : s ∈ (T.marked 1).faces → ∃ i, endpoint i = s.centroid ℝ id ∧
    fiber i '' I = T.dualRegion s ∩ (T.marked 1).space

private theorem original_edge_base_of_two_rim_marks
    {s : Finset (T.index → ℝ × V3)} (hs : s ∈ (T.marked 2).faces)
    (hcard : s.card = 2) {x y : T.index → ℝ × V3} (hxy : x ≠ y)
    (hx : x ∈ T.dualRegionRim s ∩ (T.marked 2).space)
    (hy : y ∈ T.dualRegionRim s ∩ (T.marked 2).space) :
    IsFinitePLBallPair ℝ (T.dualRegion s ∩ (T.marked 2).space) {x, y} ∧
      T.dualRegionRim s ∩ (T.marked 2).space = {x, y} := by
  obtain ⟨a, z, _, hB, hQ⟩ := T.exists_edge_zero_arc hs hcard
  have hx' := hQ.subset hx
  have hy' := hQ.subset hy
  have he : ({x, y} : Set (T.index → ℝ × V3)) = {a, z} := by
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact False.elim (hxy rfl)
    · rfl
    · exact pair_comm _ _
    · exact False.elim (hxy rfl)
  exact ⟨he.symm ▸ hB, hQ.trans he.symm⟩

theorem OriginalTriangleFibers.exists_edge_endpoints [T2Space X]
    (F : OriginalTriangleFibers T)
    {s : Finset (T.index → ℝ × V3)} (hs : s ∈ (T.marked 2).faces)
    (hcard : s.card = 2) : Nonempty (OriginalEdgeEndpoints F s) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  have htri {t : Finset (T.index → ℝ × V3)} (_ht : t ∈ (T.marked 2).faces)
      (htc : t.card = 3) (hst : s ⊆ t) : T.dualRegion t ⊆ T.dualRegionRim s := by
    apply T.dualRegion_subset_rim_of_ssubset hs
    refine hst.ssubset_of_ne ?_
    intro he
    have hc := congrArg Finset.card he
    omega
  have hcenter {t : Finset (T.index → ℝ × V3)} (ht : t ∈ (T.marked 2).faces)
      (htc : t.card = 3) (hst : s ⊆ t) :
      t.centroid ℝ id ∈ T.dualRegionRim s ∩ (T.marked 2).space := by
    have hx := (T.triangle_base_eq_singleton ht htc).symm.subset
      (show t.centroid ℝ id ∈ ({t.centroid ℝ id} : Set (T.index → ℝ × V3)) from rfl)
    exact ⟨htri ht htc hst hx.1, hx.2⟩
  by_cases hsB : s ∈ (T.marked 1).faces
  · obtain ⟨t, ht, hst, htc, hunique⟩ := T.exists_rim_edge_triangle_coface hs hcard
      ((T.disk_face_mem_boundary_iff hs).mp hsB)
    obtain ⟨B, hB, hiB, himB, h0B, hposB, hnegB⟩ :=
      T.exists_boundary_edge_fiber hs hcard hsB
    have hcs : s.centroid ℝ id ∈
        (T.dualRegion s ∩ (T.marked 2).space) ∩ (T.marked 1).space :=
      (T.boundary_edge_base_contact hs hcard hsB).symm.subset rfl
    have hcsQ : s.centroid ℝ id ∈ T.dualRegionRim s ∩ (T.marked 2).space :=
      ⟨Or.inr ⟨hcs.1.1.1, hcs.2⟩, hcs.1.2⟩
    have hne : s.centroid ℝ id ≠ t.centroid ℝ id := by
      intro he
      have heq : (⟨s, hs⟩ : (T.marked 2).faces) = ⟨t, ht⟩ :=
        (T.marked 2).faceCentroid_injective he
      have hc := congrArg (fun a : (T.marked 2).faces => a.val.card) heq
      change s.card = t.card at hc
      omega
    obtain ⟨hbase, hrim⟩ := original_edge_base_of_two_rim_marks hs hcard hne
      hcsQ (hcenter ht htc hst)
    let a : Bool → (T.index → ℝ × V3) :=
      fun i => if i then t.centroid ℝ id else s.centroid ℝ id
    let g : Bool → ℝ → (T.index → ℝ × V3) := fun i => if i then F.map t else B
    refine ⟨⟨a, hne, hbase, hrim, g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro i
      cases i
      · exact hB
      · exact F.piecewiseAffine t ht htc
    · intro i
      cases i
      · exact hiB
      · exact F.injective t ht htc
    · intro i
      cases i
      · exact h0B
      · exact F.central t ht htc
    · intro i
      cases i
      · intro x hx
        have hxB := himB.subset hx
        exact Or.inr ⟨hxB.1.1, hxB.2⟩
      · exact (F.image_eq t ht htc).subset.trans (htri ht htc hst)
    · change Disjoint (B '' I) (F.map t '' I)
      rw [himB, F.image_eq t ht htc]
      exact disjoint_left.mpr (fun _ hx hy =>
        (T.triangle_dualRegion_inter_boundary ht htc).subset ⟨hy, hx.2⟩)
    · intro i p hp r hr
      cases i
      · exact hposB p hp r hr
      · exact F.positive t ht htc p (hst hp) r hr
    · intro i p hp r hr
      cases i
      · exact hnegB p hp r hr
      · exact F.negative t ht htc p (hst hp) r hr
    · intro u hu huc hsu
      have he := hunique u hu hsu huc
      subst u
      exact ⟨true, rfl, fun _ _ => rfl⟩
    · intro _
      exact ⟨false, rfl, himB⟩
  · have hsQ : s ∉ (T.marked 3).faces :=
      fun h => hsB ((T.disk_face_mem_boundary_iff hs).mpr h)
    obtain ⟨t, ht, u, hu, hst, hsu, htc, huc, htu, hcofaces⟩ :=
      T.exists_interior_edge_triangle_cofaces hs hcard hsQ
    have hne : t.centroid ℝ id ≠ u.centroid ℝ id := by
      intro he
      have heq : (⟨t, ht⟩ : (T.marked 2).faces) = ⟨u, hu⟩ :=
        (T.marked 2).faceCentroid_injective he
      exact htu (congrArg Subtype.val heq)
    obtain ⟨hbase, hrim⟩ := original_edge_base_of_two_rim_marks hs hcard hne
      (hcenter ht htc hst) (hcenter hu huc hsu)
    have hnotface : t ∪ u ∉ (T.marked 2).faces := by
      intro hface
      have hbnd := T.disk_face_card_le hface
      have het : t = t ∪ u :=
        Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
      have heu : u = t ∪ u :=
        Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
      exact htu (het.trans heu.symm)
    have hdis : Disjoint (T.dualRegion t) (T.dualRegion u) := by
      apply disjoint_iff_inter_eq_empty.mpr
      rw [T.dualRegion_inter]
      apply T.dualRegion_eq_empty_of_not_disk_face
        (((T.marked 2).nonempty_of_mem_faces ht).mono Finset.subset_union_left) ?_ hnotface
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (T.marked 2).face_subset_vertices ht hx
      · exact (T.marked 2).face_subset_vertices hu hx
    let a : Bool → (T.index → ℝ × V3) :=
      fun i => if i then u.centroid ℝ id else t.centroid ℝ id
    let g : Bool → ℝ → (T.index → ℝ × V3) := fun i => if i then F.map u else F.map t
    refine ⟨⟨a, hne, hbase, hrim, g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro i
      cases i
      · exact F.piecewiseAffine t ht htc
      · exact F.piecewiseAffine u hu huc
    · intro i
      cases i
      · exact F.injective t ht htc
      · exact F.injective u hu huc
    · intro i
      cases i
      · exact F.central t ht htc
      · exact F.central u hu huc
    · intro i
      cases i
      · exact (F.image_eq t ht htc).subset.trans (htri ht htc hst)
      · exact (F.image_eq u hu huc).subset.trans (htri hu huc hsu)
    · change Disjoint (F.map t '' I) (F.map u '' I)
      rwa [F.image_eq t ht htc, F.image_eq u hu huc]
    · intro i p hp r hr
      cases i
      · exact F.positive t ht htc p (hst hp) r hr
      · exact F.positive u hu huc p (hsu hp) r hr
    · intro i p hp r hr
      cases i
      · exact F.negative t ht htc p (hst hp) r hr
      · exact F.negative u hu huc p (hsu hp) r hr
    · intro v hv hvc hsv
      rcases hcofaces v hv hsv hvc with rfl | rfl
      · exact ⟨false, rfl, fun _ _ => rfl⟩
      · exact ⟨true, rfl, fun _ _ => rfl⟩
    · exact fun h => False.elim (hsB h)

end PoincareConjecture.M76
