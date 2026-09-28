import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SurfaceEulerValuation
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialCone










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)

include hlin in
omit [DecidableEq E] in
private theorem zero_not_mem_base {s : Finset E} (hs : s ∈ K.faces) : (0 : E) ∉ s :=
  fun h => (hlin s hs).zero_notMem_convexHull (subset_convexHull ℝ _ h)


noncomputable def coneFaceEquiv {n : ℕ} (hn : 0 < n) :
    K.FaceOfCard (n + 1) ⊕ K.FaceOfCard n ≃ (K.coneAtZero hlin hinj).FaceOfCard (n + 1) := by
  let f : K.FaceOfCard (n + 1) ⊕ K.FaceOfCard n →
      (K.coneAtZero hlin hinj).FaceOfCard (n + 1) := fun z => match z with
    | Sum.inl s => ⟨s.val, K.le_coneAtZero hlin hinj s.property.1, s.property.2⟩
    | Sum.inr s => ⟨insert 0 s.val, ⟨Finset.insert_nonempty _ _, Or.inr (by
        rw [Finset.erase_insert (zero_not_mem_base K hlin s.property.1)]
        exact s.property.1)⟩, by
        rw [Finset.card_insert_of_notMem (zero_not_mem_base K hlin s.property.1), s.property.2]⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    have hval := congrArg Subtype.val hxy
    cases x with
    | inl s =>
      cases y with
      | inl t => exact congrArg Sum.inl (Subtype.ext hval)
      | inr t =>
        have hzero : (0 : E) ∈ s.val := hval.symm ▸ Finset.mem_insert_self 0 t.val
        exact (zero_not_mem_base K hlin s.property.1 hzero).elim
    | inr s =>
      cases y with
      | inl t =>
        have hzero : (0 : E) ∈ t.val := hval ▸ Finset.mem_insert_self 0 s.val
        exact (zero_not_mem_base K hlin t.property.1 hzero).elim
      | inr t =>
        apply congrArg Sum.inr
        apply Subtype.ext
        have he := congrArg (fun a : Finset E => a.erase 0) hval
        simpa only [f, Finset.erase_insert (zero_not_mem_base K hlin s.property.1),
          Finset.erase_insert (zero_not_mem_base K hlin t.property.1)] using he
  · intro s
    by_cases hs0 : (0 : E) ∈ s.val
    · have hcard : (s.val.erase 0).card = n := by
        rw [Finset.card_erase_of_mem hs0, s.property.2]
        omega
      have hface : s.val.erase 0 ∈ K.faces := s.property.1.2.resolve_left (by
        intro he
        rw [he, Finset.card_empty] at hcard
        omega)
      refine ⟨Sum.inr ⟨s.val.erase 0, hface, hcard⟩, ?_⟩
      apply Subtype.ext
      exact Finset.insert_erase hs0
    · have hface : s.val ∈ K.faces := by
        have h := s.property.1.2
        rw [Finset.erase_eq_of_notMem hs0] at h
        exact h.resolve_left s.property.1.1.ne_empty
      exact ⟨Sum.inl ⟨s.val, hface, s.property.2⟩, rfl⟩

theorem card_cone_faces {n : ℕ} (hn : 0 < n) (hK : K.faces.Finite) :
    Nat.card ((K.coneAtZero hlin hinj).FaceOfCard (n + 1)) =
      Nat.card (K.FaceOfCard (n + 1)) + Nat.card (K.FaceOfCard n) := by
  let : Finite (K.FaceOfCard n) := K.finite_faceOfCard hK n
  let : Finite (K.FaceOfCard (n + 1)) := K.finite_faceOfCard hK (n + 1)
  rw [← Nat.card_congr (K.coneFaceEquiv hlin hinj hn), Nat.card_sum]

theorem cone_vertices : (K.coneAtZero hlin hinj).vertices = insert 0 K.vertices := by
  ext x
  by_cases hx : x = 0
  · subst x
    exact iff_of_true (K.zero_mem_coneAtZero_vertices hlin hinj) (Or.inl rfl)
  · change (({x} : Finset E).Nonempty ∧ (({x} : Finset E).erase 0 = ∅ ∨
        ({x} : Finset E).erase 0 ∈ K.faces)) ↔ x = 0 ∨ {x} ∈ K.faces
    have hzero : (0 : E) ∉ ({x} : Finset E) := by simpa using Ne.symm hx
    simp [Finset.erase_eq_of_notMem hzero, hx]

theorem card_cone_vertices (hK : K.faces.Finite) :
    Nat.card (K.coneAtZero hlin hinj).vertices = Nat.card K.vertices + 1 := by
  change (K.coneAtZero hlin hinj).vertices.ncard = K.vertices.ncard + 1
  rw [K.cone_vertices hlin hinj]
  have hzero : (0 : E) ∉ K.vertices := fun h =>
    zero_not_mem_base K hlin h (Finset.mem_singleton_self 0)
  exact Set.ncard_insert_of_notMem hzero (K.finite_vertices_of_finite_faces hK)


theorem surfaceEulerCount_cone_eq_one (hK : K.faces.Finite)
    (hdim : ∀ s ∈ K.faces, s.card ≤ 2) :
    (K.coneAtZero hlin hinj).surfaceEulerCount = 1 := by
  have hEmpty : IsEmpty (K.FaceOfCard 3) := ⟨fun s => by
    have h := hdim s.val s.property.1
    omega⟩
  have h2 := congrArg (fun n : ℕ => (n : ℤ))
    (K.card_cone_faces hlin hinj (n := 1) (by omega) hK)
  have h3 := congrArg (fun n : ℕ => (n : ℤ))
    (K.card_cone_faces hlin hinj (n := 2) (by omega) hK)
  have h1 := congrArg (fun n : ℕ => (n : ℤ)) (K.card_cone_vertices hlin hinj hK)
  norm_num at h1 h2 h3
  simp only [surfaceEulerCount, card_faceOfCard_one] at h2 h3 ⊢
  simp only [Nat.card_coe_set_eq] at h1 h2 h3 ⊢
  omega

end Geometry.SimplicialComplex
