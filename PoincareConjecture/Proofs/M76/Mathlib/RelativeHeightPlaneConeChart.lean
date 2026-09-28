import PoincareConjecture.Proofs.M76.Mathlib.RadialFrontierHeightCorrection
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInterior












set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]







theorem IsFinitePL.exists_height_plane_cone_chart_relative
    {S P : Set E} {D : Set F} {H : frontier S ≃ₜ frontier D} (hH : H.IsFinitePL)
    (hS : IsCompact S) (hScv : Convex ℝ S) (hSzero : (0 : E) ∈ interior S)
    (hDcv : Convex ℝ D) (hDzero : (0 : F) ∈ interior D)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (A : E →ₗ[ℝ] ℝ) (B C : F →ₗ[ℝ] ℝ)
    (hpos : ∀ x : frontier S, 0 ≤ A x ↔ 0 ≤ B (H x))
    (hneg : ∀ x : frontier S, A x ≤ 0 ↔ B (H x) ≤ 0)
    (hPC : P ⊆ frontier S) (hPne : P.Nonempty)
    (hplane : ∀ x : frontier S, (x : E) ∈ P ↔ C (H x) = 0)
    (J : SimplicialComplex ℝ F) (hJ : J.faces.Finite)
    (hJD : J.space ⊆ frontier D)
    (hJheight : ∀ y : frontier D, (y : F) ∈ J.space → A (H.symm y) = B y) :
    ∃ (T : SimplicialComplex ℝ F) (e : S ≃ₜ T.space),
      T.faces.Finite ∧ e.IsFinitePL ∧ (0 : F) ∈ interior T.space ∧
      (e ⟨0, interior_subset hSzero⟩ : F) = 0 ∧
      (∀ x : S, B (e x) = A x) ∧
      (∀ x : S, C (e x) = 0 ↔ (x : E) ∈ convexJoin ℝ {0} P) ∧
      ∀ (L : E →ₗ[ℝ] F) (Q : Set E), Q ⊆ frontier S →
        (∀ x : frontier S, (x : E) ∈ Q → (H x : F) = L x) →
        (∀ x : frontier S, (x : E) ∈ Q → (H x : F) ∈ J.space) →
        ∀ x : S, (x : E) ∈ convexJoin ℝ {0} Q → (e x : F) = L x := by
  classical
  obtain ⟨K, f, hf, hinj, hK, hKs, hlinR, hradR, _, G, _, hGf,
      hheight, hplaneG, hfix⟩ :=
    hH.exists_radial_height_corrected_frontier_relative hDcv hDzero A B C
      hpos hneg hplane J hJ hJD hJheight
  have hlinK := K.linearIndependent_faces_of_space_subset_frontier hScv hSzero hKs.subset
  have hradK : InjOn (NormedSpace.normalize : E → E) K.space :=
    (hScv.injOn_normalize_frontier hSzero).mono hKs.subset
  have hfheight (x : E) (hx : x ∈ K.space) : B (f x) = A x := by
    rw [← hGf ⟨x, hKs ▸ hx⟩]
    exact hheight ⟨x, hKs ▸ hx⟩
  have hfplane (x : E) (hx : x ∈ K.space) : C (f x) = 0 ↔ x ∈ P := by
    rw [← hGf ⟨x, hKs ▸ hx⟩]
    exact hplaneG ⟨x, hKs ▸ hx⟩
  obtain ⟨e, he, he0, heheight, heplane, _, g, hg, hg0, hgbase, heg⟩ :=
    hf.exists_height_plane_preserving_cone_extension_affine hinj hK hlinK hradK
      hlinR hradR A B C hfheight (hPC.trans hKs.symm.subset) hPne hfplane
  have hsource := K.coneAtZero_space_of_frontier hlinK hradK hS hScv hSzero hKs
  let T := (hf.embeddedImage hinj).coneAtZero hlinR hradR
  let e' := (Homeomorph.setCongr hsource.symm).trans e
  have he' : e'.IsFinitePL := he.setCongr hsource rfl
  have he'0 : (e' ⟨0, interior_subset hSzero⟩ : F) = 0 := he0
  have hTzero : (0 : F) ∈ interior T.space := by
    have h := he'.mem_interior hdim (x := ⟨0, interior_subset hSzero⟩) hSzero
    rwa [he'0] at h
  refine ⟨T, e', SimplicialComplex.finite_coneAtZero_faces
    (hf.embeddedImage_finite hinj hK) hlinR hradR,
    he', hTzero, he'0, ?_, ?_, ?_⟩
  · intro x
    exact heheight ⟨x, hsource.symm ▸ x.property⟩
  · intro x
    exact heplane ⟨x, hsource.symm ▸ x.property⟩
  · intro L Q hQ hHL hHJ x hx
    have hQK : Q ⊆ K.space := hQ.trans hKs.symm.subset
    have hfL : EqOn f L Q := by
      intro y hy
      let z : frontier S := ⟨y, hQ hy⟩
      exact (hGf z).symm.trans ((hfix z (hHJ z hy)).trans (hHL z hy))
    have hgL : EqOn g L Q := (hgbase.mono hQK).trans hfL
    have hcone := hg.eqOn_linear_on_convexJoin_of_eqOn_base hg0 L hQK hgL
    exact (heg ⟨x, hsource.symm ▸ x.property⟩).trans (hcone hx)

end Homeomorph
