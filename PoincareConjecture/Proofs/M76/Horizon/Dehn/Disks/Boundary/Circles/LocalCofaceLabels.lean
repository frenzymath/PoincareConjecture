import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.LocalJoints
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.LocalVertexCut

set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]



theorem exists_boundary_joint_coface_arc_labels
    (A L : SimplicialComplex ℝ E) [Fintype A.faces]
    (hLA : L ≤ A)
    (hbound : ∀ t ∈ A.faces, t.card ≤ 3)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hfull : ∀ t ∈ A.faces, (∀ v ∈ t, v ∈ L.vertices) → t ∈ L.faces)
    (hLcard : ∀ t ∈ L.faces, t.card ≤ 2)
    {p : E} (s : Bool → Finset E) (hs : ∀ j, s j ∈ L.faces)
    (hsc : ∀ j, (s j).card = 2) (hps : ∀ j, p ∈ s j)
    (hsne : s false ≠ s true)
    (arc : Bool → Set E)
    (hArc : ∀ b, IsFinitePLBallPair ℝ (arc b)
      {(s false).centroid ℝ id, (s true).centroid ℝ id})
    (hArcU : arc false ∪ arc true = (A.barycentricSubdivision.link p).space)
    (hArcI : arc false ∩ arc true = {(s false).centroid ℝ id, (s true).centroid ℝ id}) :
    ∃ t : Bool → Bool → Finset E,
      (∀ j b, t j b ∈ A.faces ∧ (t j b).card = 3 ∧ s j ⊆ t j b) ∧
      (∀ j, t j false ≠ t j true) ∧
      (∀ j u, u ∈ A.faces → u.card = 3 → s j ⊆ u →
        u = t j false ∨ u = t j true) ∧
      (∀ j b, (s j).centroid ℝ id ≠ (t j b).centroid ℝ id) ∧
      (∀ j b, IsFinitePLBallPair ℝ
        (segment ℝ ((s j).centroid ℝ id) ((t j b).centroid ℝ id))
        {(s j).centroid ℝ id, (t j b).centroid ℝ id}) ∧
      (∀ j b, segment ℝ ((s j).centroid ℝ id) ((t j b).centroid ℝ id) ⊆ arc b) ∧
      (∀ j, (A.barycentricDualBlock (s j)).space =
        segment ℝ ((s j).centroid ℝ id) ((t j false).centroid ℝ id) ∪
          segment ℝ ((s j).centroid ℝ id) ((t j true).centroid ℝ id)) ∧
      ∀ j, segment ℝ ((s j).centroid ℝ id) ((t j false).centroid ℝ id) ∩
        segment ℝ ((s j).centroid ℝ id) ((t j true).centroid ℝ id) =
          {(s j).centroid ℝ id} := by
  classical
  have hdata (j : Bool) := exists_boundary_circle_joint A hbound hcofaces (hLA (hs j)) (hsc j)
  choose t ht htn htex hI hne hd hU hInter using hdata
  let c := fun j => (s j).centroid ℝ id
  let d := fun j b => segment ℝ (c j) ((t j b).centroid ℝ id)
  have hdis := boundary_circle_joints_disjoint A L hfull hLcard
    (hs false) (hs true) (hsc false) (hsc true) hsne
  have hcenter (j : Bool) : c j ∈ (A.barycentricDualBlock (s j)).space :=
    (A.barycentricDualBlock (s j)).vertices_subset_space
      (A.faceCentroid_mem_barycentricDualBlock_vertices (hLA (hs j)))
  have hcn : c false ≠ c true := fun h =>
    disjoint_left.mp hdis (hcenter false) (h.symm ▸ hcenter true)
  have hdJ (j b : Bool) : d j b ⊆ (A.barycentricDualBlock (s j)).space := by
    rw [hU j]
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have hdW (j b : Bool) : d j b ⊆ ⋃ b, arc b := by
    intro x hx
    have hxW := boundary_circle_joint_subset_vertex_rim A (hLA (hs j)) (hsc j) (hps j)
      (hdJ j b hx)
    rw [← hArcU] at hxW
    rcases hxW with hxW | hxW
    · exact mem_iUnion.mpr ⟨false, hxW⟩
    · exact mem_iUnion.mpr ⟨true, hxW⟩
  have hmiss (j b : Bool) : c (!j) ∉ d j b := by
    intro h
    cases j
    · exact disjoint_left.mp hdis (hdJ false b h) (hcenter true)
    · exact disjoint_left.mp hdis (hcenter false) (hdJ true b h)
  have hlabels (j : Bool) : ∃ i : Bool, d j false ⊆ arc i ∧ d j true ⊆ arc (!i) := by
    have hAj (b : Bool) : IsFinitePLBallPair ℝ (arc b) {c j, c (!j)} := by
      cases j
      · exact hArc b
      · simpa only [c, Bool.not_true, pair_comm] using hArc b
    have hIj : Pairwise (fun b e => arc b ∩ arc e = {c j, c (!j)}) := by
      intro b e hbe
      cases b <;> cases e
      · exact (hbe rfl).elim
      · cases j
        · exact hArcI
        · simpa only [c, Bool.not_true, pair_comm] using hArcI
      · cases j
        · simpa only [c, Bool.not_false, inter_comm] using hArcI
        · simpa only [c, Bool.not_true, pair_comm, inter_comm] using hArcI
      · exact (hbe rfl).elim
    exact exists_opposite_circle_arc_labels arc (d j) (fun b => (t j b).centroid ℝ id)
      hAj (by cases j; exact hcn; exact hcn.symm) hIj (hd j)
      (fun b => (hne j b).symm) (hdW j) (hmiss j) (hInter j)
  choose label hl using hlabels
  let t' : Bool → Bool → Finset E := fun j b => t j (Bool.xor (label j) b)
  have hsub (j b : Bool) : segment ℝ (c j) ((t' j b).centroid ℝ id) ⊆ arc b := by
    rcases hl j with ⟨h₀, h₁⟩
    cases hlabel : label j <;> cases b <;> simp only [hlabel, Bool.not_false,
      Bool.not_true] at h₀ h₁ <;> simp only [t', hlabel, Bool.xor_false,
      Bool.xor_true, Bool.not_true, Bool.not_false] <;> assumption
  refine ⟨t', (fun j b => ht j _), ?_, ?_, (fun j b => hne j _),
    (fun j b => hd j _), hsub, ?_, ?_⟩
  · intro j
    cases hlabel : label j
    · simpa only [t', hlabel, Bool.false_xor] using htn j
    · simpa only [t', hlabel, Bool.true_xor, Bool.not_false, Bool.not_true] using (htn j).symm
  · intro j u hu huc hsu
    have h := htex j u hu huc hsu
    cases hlabel : label j
    · simpa only [t', hlabel, Bool.false_xor] using h
    · simpa only [t', hlabel, Bool.true_xor, Bool.not_false, Bool.not_true] using h.symm
  · intro j
    cases hlabel : label j
    · simpa only [t', hlabel, Bool.false_xor] using hU j
    · simpa only [t', hlabel, Bool.true_xor, Bool.not_false, Bool.not_true, union_comm] using hU j
  · intro j
    cases hlabel : label j
    · simpa only [t', hlabel, Bool.false_xor] using hInter j
    · simpa only [t', hlabel, Bool.true_xor, Bool.not_false, Bool.not_true, inter_comm] using hInter j

end PoincareConjecture.M76.Dehn
