import PoincareConjecture.Proofs.M76.PrimeReduction.ProtectedGraphImages
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTerminalPair
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes
import PoincareConjecture.Proofs.M76.RelativeApproximation.InteriorSourceModel











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]




theorem exists_protected_finite_domain_triangulation
    {e : ι → OpenPartialHomeomorph X V3} {R D : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hDR : D ⊆ R)
    (b : ChartwisePLBall e D (frontier D)) :
    ∃ (s : Finset R) (F : X → (s → ℝ × V3))
      (K : SimplicialComplex ℝ (s → ℝ × V3))
      (A : Fin 3 → SimplicialComplex ℝ (s → ℝ × V3)) (H : R ≃ₜ K.space),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧
      (∀ i, A i ≤ K ∧ (A i).faces.Finite ∧
        ∀ t ∈ K.faces, (∀ v ∈ t, v ∈ (A i).vertices) → t ∈ (A i).faces) ∧
      K.space = F '' R ∧ (A 0).space = F '' frontier R ∧
      (A 1).space = F '' D ∧ (A 2).space = F '' frontier D ∧
      (∀ x : R, (H x : s → ℝ × V3) = F x) ∧
      (∀ x : R,
        ((H x : s → ℝ × V3) ∈ (A 0).space ↔ (x : X) ∈ frontier R) ∧
        ((H x : s → ℝ × V3) ∈ (A 1).space ↔ (x : X) ∈ D) ∧
        ((H x : s → ℝ × V3) ∈ (A 2).space ↔ (x : X) ∈ frontier D)) ∧
      ∀ x ∈ R, ∃ (i : ι) (V : Set X) (a : (s → ℝ × V3) →ᴬ[ℝ] V3),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V := by
  classical
  let : LocallyCompactSpace X := he.locallyCompactSpace
  obtain ⟨s, F, K0, B0, H0, hFc, hF, hK0, _, hB0, hK0s, hB0s, hH0, _, hproj⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_domain_finite_pair
      e he.compatible he.cover hR he.halfspace
  obtain ⟨P0, Q0, hP0, hQ0, hP0s, hQ0s⟩ := b.exists_finite_graph_images F hF
  let J : Fin 3 → SimplicialComplex ℝ (s → ℝ × V3) := ![B0, P0, Q0]
  have hJ : ∀ i, (J i).faces.Finite := by
    intro i
    fin_cases i
    · exact hB0
    · exact hP0
    · exact hQ0
  have hJK : ∀ i, (J i).space ⊆ K0.space := by
    intro i
    fin_cases i
    · change B0.space ⊆ K0.space
      rw [hB0s, hK0s]
      exact image_mono he.closed.frontier_subset
    · change P0.space ⊆ K0.space
      rw [hP0s, hK0s]
      exact image_mono hDR
    · change Q0.space ⊆ K0.space
      rw [hQ0s, hK0s]
      exact image_mono (b.boundary_subset.trans hDR)
  obtain ⟨K, A, hK, hKK0, hA⟩ :=
    K0.exists_subdivision_with_finite_full_polyhedra hK0 J hJ hJK
  let H : R ≃ₜ K.space := H0.trans (Homeomorph.setCongr hKK0.space_eq.symm)
  have hHF (x : R) : (H x : s → ℝ × V3) = F x := hH0 x
  have hB : (A 0).space = F '' frontier R := (hA 0).2.1.trans hB0s
  have hP : (A 1).space = F '' D := (hA 1).2.1.trans hP0s
  have hQ : (A 2).space = F '' frontier D := (hA 2).2.1.trans hQ0s
  have hinj : InjOn F R := by
    intro x hx y hy hxy
    have hz : H0 ⟨x, hx⟩ = H0 ⟨y, hy⟩ := Subtype.ext
      ((hH0 ⟨x, hx⟩).trans (hxy.trans (hH0 ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H0.injective hz)
  have hmem (T : Set X) (hTR : T ⊆ R) (x : R) :
      F x ∈ F '' T ↔ (x : X) ∈ T := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact hinj (hTR hy) x.property hyx ▸ hy
    · exact fun hx => mem_image_of_mem F hx
  refine ⟨s, F, K, A, H, hFc, hF, hK, ?_, hKK0.space_eq.trans hK0s,
    hB, hP, hQ, hHF, ?_, hproj⟩
  · exact fun i => ⟨(hA i).1, hK.subset (hA i).1, (hA i).2.2⟩
  · intro x
    rw [hHF, hB, hP, hQ]
    exact ⟨hmem _ he.closed.frontier_subset x, hmem _ hDR x,
      hmem _ (b.boundary_subset.trans hDR) x⟩

end PoincareConjecture.M76
