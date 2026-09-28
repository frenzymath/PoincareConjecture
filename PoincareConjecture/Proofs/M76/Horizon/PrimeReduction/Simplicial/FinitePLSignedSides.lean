import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.AffineFaceCarrier
import PoincareConjecture.Proofs.M76.Mathlib.AffineHalfspaceSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes

set_option autoImplicit false
open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FinitePiecewiseAffineOn.exists_finite_sublevel_complex
    {f : E → ℝ} {S : Set E} (hf : FinitePiecewiseAffineOn f S) (c : ℝ) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = S ∩ {x | f x ≤ c} := by
  classical
  obtain ⟨K, hK, rfl, hf⟩ := hf
  let : Finite K.faces := hK.to_subtype
  choose A hA using fun s : K.faces => hf s.val s.property
  have hcuts (s : K.faces) : ∃ J : SimplicialComplex ℝ E,
      J.faces.Finite ∧ J.space = convexHull ℝ (s.val : Set E) ∩ {x | f x ≤ c} := by
    obtain ⟨T, hT, hTs⟩ := K.exists_finite_affine_face_carrier s.property
      (ContinuousAffineMap.id ℝ E)
    have hTs' : T.space = convexHull ℝ (s.val : Set E) := by simpa using hTs
    let B : E →ᵃ[ℝ] ℝ := (A s).toAffineMap - AffineMap.const ℝ E c
    obtain ⟨J, hJ, hJs⟩ := T.exists_finite_triangulation_inter_halfspaces hT {B}
    refine ⟨J, hJ, hJs.trans ?_⟩
    rw [hTs']
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_singleton, forall_eq]
    constructor
    · rintro ⟨hx, hle⟩
      exact ⟨hx, (hA s hx) ▸ (sub_nonpos.mp hle)⟩
    · rintro ⟨hx, hle⟩
      change _ ∧ A s x - c ≤ 0
      exact ⟨hx, sub_nonpos.mpr ((hA s hx) ▸ hle)⟩
  choose J hJ hJs using hcuts
  obtain ⟨L, hL, hLs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion J hJ
  refine ⟨L, hL, hLs.trans ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨s, hxs⟩ := mem_iUnion.mp hx
    have hx' := (hJs s).subset hxs
    exact ⟨K.convexHull_subset_space s.property hx'.1, hx'.2⟩
  · rintro ⟨hx, hle⟩
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    exact mem_iUnion.mpr ⟨⟨s, hs⟩, (hJs ⟨s, hs⟩).symm.subset ⟨hxs, hle⟩⟩

theorem FinitePiecewiseAffineOn.exists_finite_superlevel_complex
    {f : E → ℝ} {S : Set E} (hf : FinitePiecewiseAffineOn f S) (c : ℝ) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = S ∩ {x | c ≤ f x} := by
  have hn := hf.postcomp (-ContinuousAffineMap.id ℝ ℝ)
  obtain ⟨L, hL, hLs⟩ := hn.exists_finite_sublevel_complex (-c)
  exact ⟨L, hL, by simpa using hLs⟩

namespace SimplicialComplex

theorem exists_subdivision_with_finitePL_signed_sides
    {ι : Type*} [Finite ι]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (U : ι → Set E) (f : ι → E → ℝ)
    (hf : ∀ i, FinitePiecewiseAffineOn (f i) (U i)) (hUK : ∀ i, U i ⊆ K.space) :
    ∃ (R : SimplicialComplex ℝ E) (P N : ι → SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧ R.space = K.space ∧
      ∀ i, P i ≤ R ∧ N i ≤ R ∧ (P i).faces.Finite ∧ (N i).faces.Finite ∧
        (P i).space = U i ∩ {x | 0 ≤ f i x} ∧
        (N i).space = U i ∩ {x | f i x ≤ 0} ∧
        (P i).space ∪ (N i).space = U i ∧
        (P i).space ∩ (N i).space = U i ∩ {x | f i x = 0} ∧
        (∀ s ∈ R.faces, (∀ v ∈ s, v ∈ (P i).vertices) → s ∈ (P i).faces) ∧
        (∀ s ∈ R.faces, (∀ v ∈ s, v ∈ (N i).vertices) → s ∈ (N i).faces) := by
  classical
  choose P₀ hP₀ hPspace using fun i => (hf i).exists_finite_superlevel_complex 0
  choose N₀ hN₀ hNspace using fun i => (hf i).exists_finite_sublevel_complex 0
  let C : ι × Bool → SimplicialComplex ℝ E := fun j => if j.2 then P₀ j.1 else N₀ j.1
  have hC (j : ι × Bool) : (C j).faces.Finite := by
    rcases j with ⟨i, b⟩
    cases b
    · exact hN₀ i
    · exact hP₀ i
  have hCK (j : ι × Bool) : (C j).space ⊆ K.space := by
    rcases j with ⟨i, b⟩
    cases b
    · exact (hNspace i).subset.trans (inter_subset_left.trans (hUK i))
    · exact (hPspace i).subset.trans (inter_subset_left.trans (hUK i))
  obtain ⟨R, L, hR, hRK, hL⟩ :=
    K.exists_subdivision_with_finite_full_polyhedra hK C hC hCK
  refine ⟨R, (fun i => L (i, true)), (fun i => L (i, false)), hR, hRK,
    hRK.space_eq, ?_⟩
  intro i
  have hP : (L (i, true)).space = U i ∩ {x | 0 ≤ f i x} :=
    (hL (i, true)).2.1.trans (hPspace i)
  have hN : (L (i, false)).space = U i ∩ {x | f i x ≤ 0} :=
    (hL (i, false)).2.1.trans (hNspace i)
  refine ⟨(hL (i, true)).1, (hL (i, false)).1,
    hR.subset (hL (i, true)).1, hR.subset (hL (i, false)).1, hP, hN,
    ?_, ?_, (hL (i, true)).2.2, (hL (i, false)).2.2⟩
  · rw [hP, hN]
    ext x
    simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      exact (le_total 0 (f i x)).elim (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)
  · rw [hP, hN]
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hx, hp⟩, _, hn⟩
      exact ⟨hx, le_antisymm hn hp⟩
    · rintro ⟨hx, heq⟩
      exact ⟨⟨hx, heq.ge⟩, hx, heq.le⟩

end SimplicialComplex
end Geometry
