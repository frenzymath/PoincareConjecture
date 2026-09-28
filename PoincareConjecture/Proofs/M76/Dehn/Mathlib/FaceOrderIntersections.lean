import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarProjectionCoverage
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem disjoint_intrinsicInterior_face_prefix
    {K : SimplicialComplex ℝ E} {n : ℕ} (order : Fin n → K.faces)
    (hinj : Function.Injective order)
    (hbefore : ∀ i k, (order k).val ⊂ (order i).val → k < i)
    (P : ℕ → SimplicialComplex ℝ E)
    (hP : ∀ k, (P k).faces = {a | ∃ i : Fin n, i.val < k ∧ (order i).val = a})
    (i : Fin n) :
    Disjoint (P i.val).space
      (intrinsicInterior ℝ (convexHull ℝ ((order i).val : Set E))) := by
  classical
  apply disjoint_left.mpr
  intro x hx hxint
  obtain ⟨a, ha, hxa⟩ := mem_space_iff.mp hx
  obtain ⟨k, hk, hka⟩ := (hP i.val).subset ha
  have hxk : x ∈ convexHull ℝ ((order k).val : Set E) := by
    rw [hka]
    exact hxa
  have hsub := K.subset_of_mem_intrinsicInterior_face
    (order i).property (order k).property hxint hxk
  have hne : (order i).val ≠ (order k).val := by
    intro heq
    have hik : i = k := hinj (Subtype.ext heq)
    exact (Nat.lt_irrefl i.val) (hik.symm ▸ hk)
  have hik := hbefore k i (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  exact (not_lt_of_ge hik.le) hk





theorem exists_ordered_faces_of_double_pair
    {K : SimplicialComplex ℝ E} (hK : K.faces.Finite)
    {n : ℕ} (order : Fin n → K.faces) (horder : Function.Bijective order)
    (hbefore : ∀ i k, (order k).val ⊂ (order i).val → k < i)
    (P : ℕ → SimplicialComplex ℝ E)
    (hP : ∀ k, (P k).faces = {a | ∃ i : Fin n, i.val < k ∧ (order i).val = a})
    {Y : Type*} {p : E → Y}
    (hcell : ∀ a : K.faces, InjOn p (convexHull ℝ (a.val : Set E)))
    {x y : E} (hx : x ∈ K.space) (hy : y ∈ K.space)
    (hne : x ≠ y) (hxy : p x = p y) :
    ∃ (i k : Fin n) (x' y' : E), k < i ∧
      ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x)) ∧
      x' ∈ intrinsicInterior ℝ (convexHull ℝ ((order i).val : Set E)) ∧
      y' ∈ intrinsicInterior ℝ (convexHull ℝ ((order k).val : Set E)) ∧
      x' ∉ (P i.val).space ∧ (order k).val ∈ (P i.val).faces ∧ p x' = p y' := by
  obtain ⟨a, ha, hxa⟩ := K.exists_face_intrinsicInterior_of_finite hK hx
  obtain ⟨b, hb, hyb⟩ := K.exists_face_intrinsicInterior_of_finite hK hy
  obtain ⟨i, hi⟩ := horder.surjective ⟨a, ha⟩
  obtain ⟨k, hk⟩ := horder.surjective ⟨b, hb⟩
  have hxi : x ∈ intrinsicInterior ℝ (convexHull ℝ ((order i).val : Set E)) := by
    simpa only [hi] using hxa
  have hyk : y ∈ intrinsicInterior ℝ (convexHull ℝ ((order k).val : Set E)) := by
    simpa only [hk] using hyb
  have hik : i ≠ k := by
    intro heq
    have hyi : y ∈ convexHull ℝ ((order i).val : Set E) := by
      rw [heq]
      exact intrinsicInterior_subset hyk
    exact hne (hcell (order i) (intrinsicInterior_subset hxi) hyi hxy)
  have hfree (q : Fin n) {z : E}
      (hz : z ∈ intrinsicInterior ℝ (convexHull ℝ ((order q).val : Set E))) :
      z ∉ (P q.val).space := fun hzP =>
    disjoint_left.mp
      (disjoint_intrinsicInterior_face_prefix order horder.injective hbefore P hP q) hzP hz
  rcases lt_or_gt_of_ne hik with hik | hki
  · exact ⟨k, i, y, x, hik, Or.inr ⟨rfl, rfl⟩, hyk, hxi, hfree k hyk,
      (hP k.val).symm.subset ⟨i, hik, rfl⟩, hxy.symm⟩
  · exact ⟨i, k, x, y, hki, Or.inl ⟨rfl, rfl⟩, hxi, hyk, hfree i hxi,
      (hP i.val).symm.subset ⟨k, hki, rfl⟩, hxy⟩

end Geometry.SimplicialComplex
