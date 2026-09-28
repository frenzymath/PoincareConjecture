import PoincareConjecture.Proofs.M76.Wall.Mathlib.BinaryFaceCenters
import PoincareConjecture.Proofs.M76.Mathlib.AffineVertexExtension










set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : SimplicialComplex ℝ E} {f : E → ℝ}

private theorem binaryFaceCenter_value (hf : K.AffineOnFaces f)
    {s : Finset E} (hs : s ∈ K.faces) (A : Set E) :
    f (s.binaryFaceCenter A) = ∑ v ∈ s, s.binaryFaceWeights A v * f v := by
  have hne := K.nonempty_of_mem_faces hs
  have hsum := s.sum_binaryFaceWeights hne A
  have hx : s.binaryFaceCenter A ∈ convexHull ℝ (s : Set E) :=
    Finset.mem_convexHull'.mpr ⟨s.binaryFaceWeights A,
      fun v _ => (s.binaryFaceWeights_pos hne A v).le, hsum, rfl⟩
  obtain ⟨a, ha⟩ := hf s hs
  have hmap := s.map_affineCombination id (s.binaryFaceWeights A) hsum a.toAffineMap
  simp only [Finset.affineCombination_eq_linear_combination _ _ _ hsum,
    id_eq, Function.comp_apply, smul_eq_mul] at hmap
  change a (s.binaryFaceCenter A) = ∑ v ∈ s, s.binaryFaceWeights A v * a v at hmap
  rw [ha hx, hmap]
  apply Finset.sum_congr rfl
  intro v hv
  rw [ha (subset_convexHull ℝ _ hv)]




theorem AffineOnFaces.binaryFaceCenter_const (hf : K.AffineOnFaces f)
    {s : Finset E} (hs : s ∈ K.faces) (A : Set E) (b : ℝ)
    (hb : ∀ v ∈ s, f v = b) : f (s.binaryFaceCenter A) = b := by
  rw [binaryFaceCenter_value hf hs A]
  calc
    _ = ∑ v ∈ s, s.binaryFaceWeights A v * b :=
      Finset.sum_congr rfl (fun v hv => congrArg (s.binaryFaceWeights A v * ·) (hb v hv))
    _ = b := by
      rw [← Finset.sum_mul, s.sum_binaryFaceWeights (K.nonempty_of_mem_faces hs) A, one_mul]




theorem AffineOnFaces.binaryFaceCenter_mixed (hf : K.AffineOnFaces f)
    {s : Finset E} (hs : s ∈ K.faces) (A : Set E) :
    letI : DecidablePred (fun x : E => x ∈ A) := fun _ => Classical.propDecidable _
    (s.filter (fun x => x ∈ A)).Nonempty ∧
      (s.filter (fun x => x ∉ A)).Nonempty →
    (∀ v ∈ s, (v ∈ A → f v = 1) ∧ (v ∉ A → f v = 0)) →
    f (s.binaryFaceCenter A) = (1 / 2 : ℝ) := by
  classical
  intro hm hvalues
  rw [binaryFaceCenter_value hf hs A]
  have hp : ((s.filter (fun x => x ∈ A)).card : ℝ) ≠ 0 := by
    exact_mod_cast hm.1.card_pos.ne'
  calc
    _ = ∑ v ∈ s, if v ∈ A then
        (1 / 2 : ℝ) * ((s.filter (fun x => x ∈ A)).card : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hA : v ∈ A
      · rw [(hvalues v hv).1 hA]
        simp only [Finset.binaryFaceWeights, if_pos hm, if_pos hA, mul_one]
      · rw [(hvalues v hv).2 hA]
        simp only [if_neg hA, mul_zero]
    _ = (1 / 2 : ℝ) := by
      simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
      calc
        _ = (1 / 2 : ℝ) * (((s.filter (fun x => x ∈ A)).card : ℝ) *
            ((s.filter (fun x => x ∈ A)).card : ℝ)⁻¹) := by ring
        _ = (1 / 2 : ℝ) := by rw [mul_inv_cancel₀ hp, mul_one]




theorem exists_binary_face_height [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (A : Set E) :
    ∃ f : E → ℝ, K.AffineOnFaces f ∧
      (∀ v ∈ K.vertices, (v ∈ A → f v = 1) ∧ (v ∉ A → f v = 0)) ∧
      MapsTo f K.space (Icc (0 : ℝ) 1) := by
  classical
  let b : E → ℝ := fun v => if v ∈ A then 1 else 0
  obtain ⟨f, hf, hv⟩ := K.exists_affineOnFaces_eqOn_vertices b
  have hvalues (v : E) (hvK : v ∈ K.vertices) :
      (v ∈ A → f v = 1) ∧ (v ∉ A → f v = 0) := by
    rw [hv hvK]
    exact ⟨fun h => if_pos h, fun h => if_neg h⟩
  refine ⟨f, hf, hvalues, ?_⟩
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨a, ha⟩ := hf s hs
  have hverts : (s : Set E) ⊆ a ⁻¹' Icc (0 : ℝ) 1 := by
    intro v hv
    have hvK : v ∈ K.vertices := K.down_closed hs
      (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    change a v ∈ Icc (0 : ℝ) 1
    rw [← ha (subset_convexHull ℝ _ hv)]
    by_cases hA : v ∈ A
    · rw [(hvalues v hvK).1 hA]
      exact ⟨zero_le_one, le_rfl⟩
    · rw [(hvalues v hvK).2 hA]
      exact ⟨le_rfl, zero_le_one⟩
  have hax : a x ∈ Icc (0 : ℝ) 1 :=
    convexHull_min hverts ((convex_Icc (0 : ℝ) 1).affine_preimage a.toAffineMap) hxs
  rwa [← ha hxs] at hax

end Geometry.SimplicialComplex
