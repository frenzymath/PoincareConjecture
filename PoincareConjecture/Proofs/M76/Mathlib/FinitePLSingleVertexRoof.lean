import PoincareConjecture.Proofs.M76.Mathlib.FinitePLAffineLevelPasting
import PoincareConjecture.Proofs.M76.Mathlib.SingleVertexRoofOverlap

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_finitePL_singleVertex_source_roof_with_pieces (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (A : E →ᵃ[ℝ] ℝ) {q : E}
    (hqK : q ∈ K.vertices) (hAq : A q = 0) {β : ℝ} (hβ : 0 < β)
    (hreg : ∀ z ∈ K.vertices, A z ∈ Icc 0 β → z = q)
    {ι : Type*} [Finite ι] (T : ι → Finset E)
    (hT : ∀ i, T i ∈ K.faces) (hTc : ∀ i, (T i).card = 3)
    (hTi : Function.Injective T) (S : ι → Set (E × ℝ))
    (hcover : (⋃ i, convexHull ℝ (T i : Set E) ∩ {x | A x = 0}) =
      K.space ∩ {x | A x = 0})
    (hsource : ∀ i, (q ∉ T i ∧
        S i = (convexHull ℝ (T i : Set E) ∩ {x | A x = 0}) ×ˢ Icc 0 β) ∨
      ∃ w : E, q ∈ T i ∧ q ≠ w ∧ w ∈ convexHull ℝ ((T i : Set E) \ {q}) ∧
        (convexHull ℝ (T i : Set E) ∩ {x | A x = 0} = segment ℝ q w) ∧
        S i = TaperedStrip.segmentDomain q w β) :
    ∃ upper : E → ℝ, FinitePiecewiseAffineOn upper (K.space ∩ {x | A x = 0}) ∧
      (∀ x ∈ K.space ∩ {x | A x = 0}, upper x ∈ Icc 0 β) ∧
      ((⋃ i, S i) = {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (upper p.1)}) ∧
      ∀ i, ∃ a : E →ᴬ[ℝ] ℝ,
        (∀ x ∈ convexHull ℝ (T i : Set E) ∩ {x | A x = 0}, a x ∈ Icc 0 β) ∧
        S i = {p : E × ℝ | p.1 ∈ convexHull ℝ (T i : Set E) ∩ {x | A x = 0} ∧
          p.2 ∈ Icc 0 (a p.1)} ∧
        EqOn upper a (convexHull ℝ (T i : Set E) ∩ {x | A x = 0}) := by
  classical
  choose a habound haband haroof using fun i => A.exists_singleVertex_source_roof hβ (hsource i)
  have hagree (i j : ι) (x : E)
      (hi : x ∈ convexHull ℝ (T i : Set E) ∩ {x | A x = 0})
      (hj : x ∈ convexHull ℝ (T j : Set E) ∩ {x | A x = 0}) : a i x = a j x := by
    by_cases hij : i = j
    · subst j
      rfl
    · have hneq := fun h => hij (hTi h)
      exact (K.singleVertex_roof_value_at_overlap A hqK hAq hβ.le hreg
        (hT i) (hT j) (hTc i) (hTc j) hneq (a i) (haroof i) hi hj).trans
        (K.singleVertex_roof_value_at_overlap A hqK hAq hβ.le hreg
          (hT j) (hT i) (hTc j) (hTc i) (Ne.symm hneq) (a j) (haroof j) hj hi).symm
  obtain ⟨upper, hPL, hval⟩ := K.exists_finitePL_affineLevel_pasting hK A 0 T
    (fun i => K.indep (hT i)) hcover a hagree
  refine ⟨upper, hPL, ?_, ?_, fun i => ⟨a i, habound i, haband i, hval i⟩⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ hx)
    rw [hval i hi]
    exact habound i x hi
  · ext p
    constructor
    · intro hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      rw [haband i] at hi
      refine ⟨hcover ▸ mem_iUnion.mpr ⟨i, hi.1⟩, ?_⟩
      rw [hval i hi.1]
      exact hi.2
    · intro hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ hp.1)
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      rw [haband i]
      exact ⟨hi, (hval i hi) ▸ hp.2⟩

theorem exists_finitePL_singleVertex_source_roof (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (A : E →ᵃ[ℝ] ℝ) {q : E}
    (hqK : q ∈ K.vertices) (hAq : A q = 0) {β : ℝ} (hβ : 0 < β)
    (hreg : ∀ z ∈ K.vertices, A z ∈ Icc 0 β → z = q)
    {ι : Type*} [Finite ι] (T : ι → Finset E)
    (hT : ∀ i, T i ∈ K.faces) (hTc : ∀ i, (T i).card = 3)
    (hTi : Function.Injective T) (S : ι → Set (E × ℝ))
    (hcover : (⋃ i, convexHull ℝ (T i : Set E) ∩ {x | A x = 0}) =
      K.space ∩ {x | A x = 0})
    (hsource : ∀ i, (q ∉ T i ∧
        S i = (convexHull ℝ (T i : Set E) ∩ {x | A x = 0}) ×ˢ Icc 0 β) ∨
      ∃ w : E, q ∈ T i ∧ q ≠ w ∧ w ∈ convexHull ℝ ((T i : Set E) \ {q}) ∧
        (convexHull ℝ (T i : Set E) ∩ {x | A x = 0} = segment ℝ q w) ∧
        S i = TaperedStrip.segmentDomain q w β) :
    ∃ upper : E → ℝ, FinitePiecewiseAffineOn upper (K.space ∩ {x | A x = 0}) ∧
      (∀ x ∈ K.space ∩ {x | A x = 0}, upper x ∈ Icc 0 β) ∧
      (⋃ i, S i) = {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (upper p.1)} := by
  obtain ⟨upper, hPL, hbound, hband, _⟩ :=
    K.exists_finitePL_singleVertex_source_roof_with_pieces hK A hqK hAq hβ hreg
      T hT hTc hTi S hcover hsource
  exact ⟨upper, hPL, hbound, hband⟩

end Geometry.SimplicialComplex
