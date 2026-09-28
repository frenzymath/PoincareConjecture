import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskFaceProducts










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "Cube" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : Cube ≃ₜ D}
  {T : HamiltonProperDiskTriangulation R D b} {c : E ≃ᴬ[ℝ] V}
  {C : HamiltonProperDiskCoherentSides T c}




structure HamiltonProperDiskEdgeEndpoints
    (F : HamiltonProperDiskTriangleFibers C) (s : Finset E) where
  endpoint : Bool → E
  distinct : endpoint false ≠ endpoint true
  base : IsFinitePLBallPair ℝ (T.diskDualBase s) {endpoint false, endpoint true}
  base_rim : T.dualRegionRim s ∩ D = {endpoint false, endpoint true}
  fiber : Bool → ℝ → E
  piecewiseAffine : ∀ i, FinitePiecewiseAffineOn (fiber i) I
  injective : ∀ i, InjOn (fiber i) I
  central : ∀ i, fiber i 0 = endpoint i
  image_subset : ∀ i, fiber i '' I ⊆ T.dualRegionRim s
  disjoint : Disjoint (fiber false '' I) (fiber true '' I)
  positive : ∀ i, ∀ p : T.disk.vertices, (p : E) ∈ s → ∀ t ∈ I,
    0 ≤ C.labels.height p (fiber i t) ↔ 0 ≤ t
  negative : ∀ i, ∀ p : T.disk.vertices, (p : E) ∈ s → ∀ t ∈ I,
    C.labels.height p (fiber i t) ≤ 0 ↔ t ≤ 0
  coface : ∀ t ∈ T.disk.faces, t.card = 3 → s ⊆ t →
    ∃ i, endpoint i = t.centroid ℝ id ∧ EqOn (fiber i) (F.map t) I
  boundary : s ∈ T.boundary.faces → ∃ i, endpoint i = s.centroid ℝ id ∧
    fiber i '' I = T.dualRegion s ∩ frontier R

variable [FiniteDimensional ℝ E]

private theorem edge_base_of_two_rim_marks
    (hproper : ∀ x : Cube, (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    {s : Finset E} (hs : s ∈ T.disk.faces) (hcard : s.card = 2)
    {x y : E} (hxy : x ≠ y) (hx : x ∈ T.dualRegionRim s ∩ D)
    (hy : y ∈ T.dualRegionRim s ∩ D) :
    IsFinitePLBallPair ℝ (T.diskDualBase s) {x, y} ∧
      T.dualRegionRim s ∩ D = {x, y} := by
  obtain ⟨a, z, _, hB, hQ⟩ := T.exists_edge_zero_arc hproper hs hcard
  have hx' := hQ.subset hx
  have hy' := hQ.subset hy
  have he : ({x, y} : Set E) = {a, z} := by
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact False.elim (hxy rfl)
    · rfl
    · exact pair_comm _ _
    · exact False.elim (hxy rfl)
  exact ⟨he.symm ▸ hB, hQ.trans he.symm⟩




theorem HamiltonProperDiskTriangleFibers.exists_edge_endpoints
    (F : HamiltonProperDiskTriangleFibers C) (h3 : Module.finrank ℝ E = 3)
    (hproper : ∀ x : Cube, (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    {s : Finset E} (hs : s ∈ T.disk.faces) (hcard : s.card = 2) :
    Nonempty (HamiltonProperDiskEdgeEndpoints F s) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype T.disk.faces := (T.finite.subset T.disk_le).fintype
  have htri {t : Finset E} (ht : t ∈ T.disk.faces) (htc : t.card = 3) (hst : s ⊆ t) :
      T.dualRegion t ⊆ T.dualRegionRim s := by
    apply T.dualRegion_subset_rim_of_ssubset hs ht
    refine hst.ssubset_of_ne ?_
    intro he
    have hc := congrArg Finset.card he
    omega
  have hcenter {t : Finset E} (ht : t ∈ T.disk.faces) (htc : t.card = 3)
      (hst : s ⊆ t) : t.centroid ℝ id ∈ T.dualRegionRim s ∩ D := by
    have hx := (T.triangle_base_eq_singleton ht htc).symm.subset
      (show t.centroid ℝ id ∈ ({t.centroid ℝ id} : Set E) from rfl)
    exact ⟨htri ht htc hst hx.1, hx.2⟩
  have hinside {t : Finset E} (ht : t ∈ T.disk.faces) (htc : t.card = 3) :
      T.dualRegion t ⊆ interior R :=
    inter_subset_left.trans
      (T.dualBlock_subset_interior ht (T.disk_triangle_not_boundary hproper ht htc))
  by_cases hsF : s ∈ T.boundary.faces
  · have hboundary : convexHull ℝ (s : Set E) ⊆ frontier R :=
      (T.boundary.convexHull_subset_space hsF).trans T.boundary_space.subset
    obtain ⟨t, ht, hst, htc, hunique⟩ :=
      T.exists_boundary_triangle_coface hproper hs hcard hboundary
    obtain ⟨B, hB, hiB, himB, h0B, hposB, hnegB⟩ :=
      C.exists_boundary_edge_fiber h3 hproper hs hcard hsF
    have hcs : s.centroid ℝ id ∈ T.diskDualBase s ∩ frontier R :=
      (T.boundary_edge_base_contact hproper hs hcard hsF).symm.subset rfl
    have hcsQ : s.centroid ℝ id ∈ T.dualRegionRim s ∩ D :=
      ⟨Or.inr ⟨hcs.1.1.1, hcs.2⟩, hcs.1.2⟩
    have hne : s.centroid ℝ id ≠ t.centroid ℝ id := by
      intro he
      have heq : (⟨s, hs⟩ : T.disk.faces) = ⟨t, ht⟩ := T.disk.faceCentroid_injective he
      have hc := congrArg (fun a : T.disk.faces => a.val.card) heq
      change s.card = t.card at hc
      omega
    obtain ⟨hbase, hrim⟩ := edge_base_of_two_rim_marks hproper hs hcard hne
      hcsQ (hcenter ht htc hst)
    let a : Bool → E := fun i => if i then t.centroid ℝ id else s.centroid ℝ id
    let g : Bool → ℝ → E := fun i => if i then F.map t else B
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
        have hxF := himB.subset hx
        exact Or.inr ⟨hxF.1.1, hxF.2⟩
      · exact (F.image_eq t ht htc).subset.trans (htri ht htc hst)
    · change Disjoint (B '' I) (F.map t '' I)
      rw [himB, F.image_eq t ht htc]
      exact disjoint_left.mpr (fun x hx hy => hx.2.2 (hinside ht htc hy))
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
  · have hNint := T.dualBlock_subset_interior hs hsF
    have hcs : s.centroid ℝ id ∈ (T.ambient.barycentricDualBlock s).space :=
      (T.ambient.barycentricDualBlock s).vertices_subset_space
        (T.ambient.faceCentroid_mem_barycentricDualBlock_vertices (T.disk_le hs))
    have hmeet : (convexHull ℝ (s : Set E) ∩ interior R).Nonempty :=
      ⟨s.centroid ℝ id, s.centroid_mem_convexHull (T.disk.nonempty_of_mem_faces hs), hNint hcs⟩
    obtain ⟨t, ht, u, hu, hst, hsu, htc, huc, htu, hcofaces⟩ :=
      T.exists_interior_triangle_cofaces hproper hs hcard hmeet
    have hne : t.centroid ℝ id ≠ u.centroid ℝ id := by
      intro he
      have heq : (⟨t, ht⟩ : T.disk.faces) = ⟨u, hu⟩ := T.disk.faceCentroid_injective he
      exact htu (congrArg Subtype.val heq)
    obtain ⟨hbase, hrim⟩ := edge_base_of_two_rim_marks hproper hs hcard hne
      (hcenter ht htc hst) (hcenter hu huc hsu)
    have hnotface : t ∪ u ∉ T.disk.faces := by
      intro hface
      have hbnd := T.disk_face_card_le hface
      have het : t = t ∪ u := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
      have heu : u = t ∪ u := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
      exact htu (het.trans heu.symm)
    have hdis : Disjoint (T.dualRegion t) (T.dualRegion u) := by
      apply disjoint_iff_inter_eq_empty.mpr
      rw [T.dualRegion_inter]
      apply T.dualRegion_eq_empty_of_not_disk_face
        ((T.disk.nonempty_of_mem_faces ht).mono Finset.subset_union_left) ?_ hnotface
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact T.disk.face_subset_vertices ht hx
      · exact T.disk.face_subset_vertices hu hx
    let a : Bool → E := fun i => if i then u.centroid ℝ id else t.centroid ℝ id
    let g : Bool → ℝ → E := fun i => if i then F.map u else F.map t
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
    · exact fun h => False.elim (hsF h)

end PoincareConjecture.M76.HamiltonIndexOne
