import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteFaceCounts
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount

set_option autoImplicit false

open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E)

noncomputable def vertexLinkFaceEquiv {n : ℕ} (hn : 0 < n) :
    (Σ p : K.vertices, (K.faceLink {p.val}).FaceOfCard n) ≃
      Σ t : K.FaceOfCard (n + 1), {p : E // p ∈ t.val} := by
  let f : (Σ p : K.vertices, (K.faceLink {p.val}).FaceOfCard n) →
      Σ t : K.FaceOfCard (n + 1), {p : E // p ∈ t.val} := fun x =>
    ⟨⟨insert x.1.val x.2.val,
        by simpa only [Finset.singleton_union] using x.2.property.1.2.2,
        by rw [Finset.card_insert_of_notMem
          (Finset.disjoint_singleton_left.mp x.2.property.1.2.1), x.2.property.2]⟩,
      ⟨x.1.val, Finset.mem_insert_self _ _⟩⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨p, s⟩ ⟨q, t⟩ h
    have hpq : p = q := Subtype.ext (congrArg (fun z => z.2.val) h)
    subst q
    have hst : insert p.val s.val = insert p.val t.val :=
      congrArg (fun z => z.1.val) h
    have hs : p.val ∉ s.val := Finset.disjoint_singleton_left.mp s.property.1.2.1
    have ht : p.val ∉ t.val := Finset.disjoint_singleton_left.mp t.property.1.2.1
    have heq : s = t := Subtype.ext (by
      simpa only [Finset.erase_insert hs, Finset.erase_insert ht] using
        congrArg (fun u : Finset E => u.erase p.val) hst)
    subst t
    rfl
  · rintro ⟨t, p⟩
    have hpK : p.val ∈ K.vertices := K.down_closed t.property.1
      (Finset.singleton_subset_iff.mpr p.property) (Finset.singleton_nonempty p.val)
    have hcard : (t.val.erase p.val).card = n := by
      rw [Finset.card_erase_of_mem p.property, t.property.2]
      omega
    have hne : (t.val.erase p.val).Nonempty := Finset.card_pos.mp (by omega)
    have hface : t.val.erase p.val ∈ (K.faceLink {p.val}).faces := by
      refine ⟨K.down_closed t.property.1 (Finset.erase_subset _ _) hne,
        Finset.disjoint_singleton_left.mpr (Finset.notMem_erase _ _), ?_⟩
      simpa only [Finset.singleton_union, Finset.insert_erase p.property] using t.property.1
    refine ⟨⟨⟨p.val, hpK⟩, ⟨t.val.erase p.val, hface, hcard⟩⟩, ?_⟩
    apply Sigma.subtype_ext
    · apply Subtype.ext
      exact Finset.insert_erase p.property
    · rfl

theorem sum_card_vertexLink_faces (hK : K.faces.Finite)
    [Fintype K.vertices] {n : ℕ} (hn : 0 < n) :
    (∑ p : K.vertices, Nat.card ((K.faceLink {p.val}).FaceOfCard n)) =
      (n + 1) * Nat.card (K.FaceOfCard (n + 1)) := by
  classical
  let (p : K.vertices) : Finite ((K.faceLink {p.val}).FaceOfCard n) :=
    (K.faceLink {p.val}).finite_faceOfCard (finite_faceLink_faces hK _) n
  let : Finite (K.FaceOfCard (n + 1)) := K.finite_faceOfCard hK _
  let : Fintype (K.FaceOfCard (n + 1)) := Fintype.ofFinite _
  have hcount := Nat.card_congr (K.vertexLinkFaceEquiv hn)
  rw [Nat.card_sigma, Nat.card_sigma] at hcount
  calc
    (∑ p : K.vertices, Nat.card ((K.faceLink {p.val}).FaceOfCard n)) =
        ∑ t : K.FaceOfCard (n + 1), Nat.card {p : E // p ∈ t.val} := hcount
    _ = ∑ _t : K.FaceOfCard (n + 1), (n + 1) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Nat.card_eq_finsetCard, t.property.2]
    _ = (n + 1) * Nat.card (K.FaceOfCard (n + 1)) := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
        smul_eq_mul, Nat.mul_comm]

theorem vertexLink_face_double_counts (hK : K.faces.Finite) [Fintype K.vertices] :
    (∑ p : K.vertices, Nat.card (K.faceLink {p.val}).vertices) =
        2 * Nat.card (K.FaceOfCard 2) ∧
      (∑ p : K.vertices, Nat.card ((K.faceLink {p.val}).FaceOfCard 2)) =
        3 * Nat.card (K.FaceOfCard 3) ∧
      (∑ p : K.vertices, Nat.card ((K.faceLink {p.val}).FaceOfCard 3)) =
        4 * Nat.card (K.FaceOfCard 4) := by
  refine ⟨?_, K.sum_card_vertexLink_faces hK (by decide : 0 < 2),
    K.sum_card_vertexLink_faces hK (by decide : 0 < 3)⟩
  simpa only [card_faceOfCard_one] using
    K.sum_card_vertexLink_faces hK (by decide : 0 < 1)

open Classical in

theorem sum_vertexLink_local_counts (A : SimplicialComplex ℝ E) (hAK : A ≤ K)
    (hK : K.faces.Finite)
    (hlocal : ∀ p : K.vertices,
      Nat.card (K.faceLink {p.val}).vertices +
          Nat.card ((K.faceLink {p.val}).FaceOfCard 3) =
        Nat.card ((K.faceLink {p.val}).FaceOfCard 2) +
          if p.val ∈ A.vertices then 1 else 2) :
    2 * Nat.card (K.FaceOfCard 2) + 4 * Nat.card (K.FaceOfCard 4) +
        Nat.card A.vertices =
      3 * Nat.card (K.FaceOfCard 3) + 2 * Nat.card K.vertices := by
  classical
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ)
    rfl (fun p _ => hlocal p)
  simp only [Finset.sum_add_distrib] at hsum
  obtain ⟨hvertices, hedges, htriangles⟩ := K.vertexLink_face_double_counts hK
  rw [hvertices, hedges, htriangles] at hsum
  have hmark := Nat.card_congr (K.markedVertexEquiv A hAK)
  have hconditional := Fintype.sum_one_two_add_card_subtype
    (fun p : K.vertices => p.val ∈ A.vertices)
  rw [hmark] at hconditional
  omega

end Geometry.SimplicialComplex
