import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteFaceCounts

set_option autoImplicit false

open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E)

noncomputable def faceFacetEquiv {n : ℕ} (hn : 0 < n)
    (t : K.FaceOfCard (n + 1)) :
    {p : E // p ∈ t.val} ≃ {s : K.FaceOfCard n // s.val ⊆ t.val} := by
  have hcard (p : E) (hp : p ∈ t.val) : (t.val.erase p).card = n := by
    rw [Finset.card_erase_of_mem hp, t.property.2]
    omega
  let f : {p : E // p ∈ t.val} → {s : K.FaceOfCard n // s.val ⊆ t.val} := fun p =>
    ⟨⟨t.val.erase p.val,
      K.down_closed t.property.1 (Finset.erase_subset _ _)
        (Finset.card_pos.mp (by rw [hcard p.val p.property]; exact hn)),
      hcard p.val p.property⟩, Finset.erase_subset _ _⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q h
    apply Subtype.ext
    apply (Finset.erase_inj t.val p.property).mp
    exact congrArg (fun z => z.val.val) h
  · intro s
    have hdiff : (t.val \ s.val.val).card = 1 := by
      rw [Finset.card_sdiff_of_subset s.property, t.property.2, s.val.property.2]
      omega
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hdiff
    have hpmem : p ∈ t.val \ s.val.val := hp.symm ▸ Finset.mem_singleton_self p
    have hpt := (Finset.mem_sdiff.mp hpmem).1
    have hps := (Finset.mem_sdiff.mp hpmem).2
    have hinsert : insert p s.val.val = t.val := by
      rw [← Finset.singleton_union, ← hp, Finset.sdiff_union_of_subset s.property]
    have herase : t.val.erase p = s.val.val := by
      have h := congrArg (fun u : Finset E => u.erase p) hinsert
      exact h.symm.trans (Finset.erase_insert hps)
    exact ⟨⟨p, hpt⟩, Subtype.ext (Subtype.ext herase)⟩

omit [DecidableEq E] in

theorem card_face_facets {n : ℕ} (hn : 0 < n) (t : K.FaceOfCard (n + 1)) :
    Nat.card {s : K.FaceOfCard n // s.val ⊆ t.val} = n + 1 := by
  classical
  rw [← Nat.card_congr (K.faceFacetEquiv hn t), Nat.card_eq_finsetCard, t.property.2]

omit [DecidableEq E] in

theorem card_face_cofaces {n m : ℕ} (s : K.FaceOfCard n) :
    Nat.card {t : K.FaceOfCard m // s.val ⊆ t.val} =
      {t : Finset E | t ∈ K.faces ∧ t.card = m ∧ s.val ⊆ t}.ncard := by
  let e : {t : K.FaceOfCard m // s.val ⊆ t.val} ≃
      {t : Finset E // t ∈ K.faces ∧ t.card = m ∧ s.val ⊆ t} := {
    toFun := fun t => ⟨t.val.val, t.val.property.1, t.val.property.2, t.property⟩
    invFun := fun t => ⟨⟨t.val, t.property.1, t.property.2.1⟩, t.property.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact Nat.card_congr e

omit [DecidableEq E] in

theorem sum_original_coface_counts (hK : K.faces.Finite)
    {n : ℕ} (hn : 0 < n) [Fintype (K.FaceOfCard n)] :
    (∑ s : K.FaceOfCard n,
      {t : Finset E | t ∈ K.faces ∧ t.card = n + 1 ∧ s.val ⊆ t}.ncard) =
      (n + 1) * Nat.card (K.FaceOfCard (n + 1)) := by
  classical
  let : Finite (K.FaceOfCard (n + 1)) := K.finite_faceOfCard hK _
  let : Fintype (K.FaceOfCard (n + 1)) := Fintype.ofFinite _
  let e : (Σ s : K.FaceOfCard n, {t : K.FaceOfCard (n + 1) // s.val ⊆ t.val}) ≃
      Σ t : K.FaceOfCard (n + 1), {s : K.FaceOfCard n // s.val ⊆ t.val} := {
    toFun := fun x => ⟨x.2.val, ⟨x.1, x.2.property⟩⟩
    invFun := fun x => ⟨x.2.val, ⟨x.1, x.2.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcount := Nat.card_congr e
  rw [Nat.card_sigma, Nat.card_sigma] at hcount
  simp_rw [K.card_face_cofaces] at hcount
  calc
    (∑ s : K.FaceOfCard n,
        {t : Finset E | t ∈ K.faces ∧ t.card = n + 1 ∧ s.val ⊆ t}.ncard) =
        ∑ t : K.FaceOfCard (n + 1), Nat.card {s : K.FaceOfCard n // s.val ⊆ t.val} :=
      hcount
    _ = ∑ _t : K.FaceOfCard (n + 1), (n + 1) := by
      apply Finset.sum_congr rfl
      intro t _
      exact K.card_face_facets hn t
    _ = (n + 1) * Nat.card (K.FaceOfCard (n + 1)) := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
        smul_eq_mul, Nat.mul_comm]

open Classical in
omit [DecidableEq E] in

theorem original_face_coface_count_of_one_two
    (A : SimplicialComplex ℝ E) (hAK : A ≤ K) (hK : K.faces.Finite)
    {n : ℕ} (hn : 0 < n)
    (hcofaces : ∀ s : K.FaceOfCard n,
      {t : Finset E | t ∈ K.faces ∧ t.card = n + 1 ∧ s.val ⊆ t}.ncard =
        if s.val ∈ A.faces then 1 else 2) :
    (n + 1) * Nat.card (K.FaceOfCard (n + 1)) + Nat.card (A.FaceOfCard n) =
      2 * Nat.card (K.FaceOfCard n) := by
  classical
  let : Finite (K.FaceOfCard n) := K.finite_faceOfCard hK n
  let : Fintype (K.FaceOfCard n) := Fintype.ofFinite _
  rw [← K.sum_original_coface_counts hK hn]
  simp_rw [hcofaces]
  have hmark := Nat.card_congr (K.markedFaceEquiv A hAK n)
  simpa only [hmark] using
    Fintype.sum_one_two_add_card_subtype (fun s : K.FaceOfCard n => s.val ∈ A.faces)

omit [DecidableEq E] in

theorem original_face_coface_count_of_two
    (hK : K.faces.Finite) {n : ℕ} (hn : 0 < n)
    (hcofaces : ∀ s : K.FaceOfCard n,
      {t : Finset E | t ∈ K.faces ∧ t.card = n + 1 ∧ s.val ⊆ t}.ncard = 2) :
    (n + 1) * Nat.card (K.FaceOfCard (n + 1)) = 2 * Nat.card (K.FaceOfCard n) := by
  classical
  let : Finite (K.FaceOfCard n) := K.finite_faceOfCard hK n
  let : Fintype (K.FaceOfCard n) := Fintype.ofFinite _
  rw [← K.sum_original_coface_counts hK hn]
  simp only [hcofaces, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
    smul_eq_mul, Nat.mul_comm]

end Geometry.SimplicialComplex
