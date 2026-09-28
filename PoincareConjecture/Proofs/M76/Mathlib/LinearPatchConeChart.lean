import PoincareConjecture.Proofs.M76.Mathlib.RelativeHeightPlaneConeChart
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions












set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {M E F ι : Type*} [Finite ι]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]







theorem IsFinitePL.exists_height_plane_cone_chart_linear_patches
    {S P : Set E} {D : Set F} {H : frontier S ≃ₜ frontier D} (hH : H.IsFinitePL)
    (hS : IsCompact S) (hScv : Convex ℝ S) (hSzero : (0 : E) ∈ interior S)
    (hDcv : Convex ℝ D) (hDzero : (0 : F) ∈ interior D)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (A : E →ₗ[ℝ] ℝ) (B C : F →ₗ[ℝ] ℝ)
    (hpos : ∀ x : frontier S, 0 ≤ A x ↔ 0 ≤ B (H x))
    (hneg : ∀ x : frontier S, A x ≤ 0 ↔ B (H x) ≤ 0)
    (hPC : P ⊆ frontier S) (hPne : P.Nonempty)
    (hplane : ∀ x : frontier S, (x : E) ∈ P ↔ C (H x) = 0)
    (Q q : ι → Set E) (hQ : ∀ i, IsFinitePLBallPair M (Q i) (q i))
    (hQS : ∀ i, Q i ⊆ frontier S) (L : ι → E ≃L[ℝ] F)
    (hHL : ∀ i (x : frontier S), (x : E) ∈ Q i → (H x : F) = L i x)
    (hLheight : ∀ i x, x ∈ Q i → B (L i x) = A x) :
    ∃ (T : SimplicialComplex ℝ F) (e : S ≃ₜ T.space),
      T.faces.Finite ∧ e.IsFinitePL ∧ (0 : F) ∈ interior T.space ∧
      (e ⟨0, interior_subset hSzero⟩ : F) = 0 ∧
      (∀ x : S, B (e x) = A x) ∧
      (∀ x : S, C (e x) = 0 ↔ (x : E) ∈ convexJoin ℝ {0} P) ∧
      ∀ i (x : S), (x : E) ∈ convexJoin ℝ {0} (Q i) → (e x : F) = L i x := by
  classical
  have hchoose (i : ι) : ∃ K : SimplicialComplex ℝ F,
      K.faces.Finite ∧ K.space = L i '' Q i := by
    have hi := (hQ i).affine_image
      (L i).toContinuousAffineEquiv.toContinuousAffineMap (L i).injective.injOn
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hi
    exact ⟨K, hK, hKs⟩
  choose K hK hKs using hchoose
  obtain ⟨J, hJ, hJs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion K hK
  have hJimage : J.space = ⋃ i, L i '' Q i := by
    simpa only [hKs] using hJs
  have hJD : J.space ⊆ frontier D := by
    intro y hy
    rw [hJimage] at hy
    obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp hy
    have heq := hHL i ⟨x, hQS i hx⟩ hx
    exact heq ▸ (H ⟨x, hQS i hx⟩).property
  have hJheight (y : frontier D) (hy : (y : F) ∈ J.space) :
      A (H.symm y) = B y := by
    rw [hJimage] at hy
    obtain ⟨i, x, hx, hxy⟩ := mem_iUnion.mp hy
    let z : frontier S := ⟨x, hQS i hx⟩
    have hHzy : H z = y := Subtype.ext ((hHL i z hx).trans hxy)
    have hInv : H.symm y = z := by rw [← hHzy, H.symm_apply_apply]
    calc
      A (H.symm y) = A x := congrArg (fun w : frontier S => A (w : E)) hInv
      _ = B (L i x) := (hLheight i x hx).symm
      _ = B y := congrArg B hxy
  obtain ⟨T, e, hT, he, hTzero, he0, heheight, heplane, hkeep⟩ :=
    hH.exists_height_plane_cone_chart_relative hS hScv hSzero hDcv hDzero hdim
      A B C hpos hneg hPC hPne hplane J hJ hJD hJheight
  refine ⟨T, e, hT, he, hTzero, he0, heheight, heplane, ?_⟩
  intro i
  apply hkeep (L i).toLinearMap (Q i) (hQS i) (hHL i)
  intro x hx
  rw [hJimage]
  exact mem_iUnion.mpr ⟨i, x, hx, (hHL i x hx).symm⟩

end Homeomorph
