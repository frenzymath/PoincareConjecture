import PoincareConjecture.Proofs.M76.Mathlib.CompactPLRelativeDeformationNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLScalarNeighborhoodModel
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInCharts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation

set_option autoImplicit false

open Set Geometry unitInterval

namespace OpenPartialHomeomorph

theorem exists_polyhedral_image_relative_deformation_neighborhood
    {M E D ι : Type*} [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    (S : SimplicialComplex ℝ D) (hS : S.faces.Finite)
    {f : D → M} (hf : PolyhedralPLInCharts e f S.space)
    {W R : Set M} (hW : IsOpen W) (hfW : MapsTo f S.space W)
    (hfR : MapsTo f S.space R) (hR : IsClosed R)
    {r : M → ℝ} (hr : Continuous r)
    (hrPL : ∀ i, LocallyPiecewiseAffineOn (r ∘ (e i).symm) (e i).target)
    (hcut : ∀ x ∈ W, x ∈ R ↔ 0 ≤ r x)
    (hzero : ∀ x ∈ W, x ∈ frontier R ↔ r x = 0)
    (hboundary : ∀ x ∈ frontier R,
      ∃ (psi : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        psi.contLinear v = 1 ∧ x ∈ B.source ∧ psi (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ psi (B y)) :
    ∃ (z : M → ℝ) (t : ℝ), t ∈ Ioo (1 / 3 : ℝ) (2 / 3 : ℝ) ∧
      Continuous z ∧ (∀ x ∈ f '' S.space, z x = 1) ∧
      let P : Set M := {x | t ≤ z x}
      let N : Set M := {x | x ∈ R ∧ t ≤ z x}
      IsCompact P ∧ IsCompact N ∧ f '' S.space ⊆ interior P ∧
        f '' S.space ⊆ N ∧ N ⊆ W ∧
        (∃ T : C(I × N, M), (∀ p, T p ∈ N) ∧
          (∀ x : N, T (0, x) = (x : M)) ∧
          (∀ x : N, T (1, x) ∈ f '' S.space) ∧
          (∀ (tau : I) (x : N), (x : M) ∈ f '' S.space → T (tau, x) = (x : M)) ∧
          ∀ (tau : I) (x : N), (x : M) ∈ frontier R → T (tau, x) ∈ frontier R) ∧
        (∀ x ∈ frontier N,
          ∃ (psi : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
            psi.contLinear v = 1 ∧ x ∈ B.source ∧ psi (B x) = 0 ∧
            (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
            ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ psi (B y)) ∧
        ∀ x ∈ frontier R, z x = t →
          ∃ (psi eta : E →ᴬ[ℝ] ℝ) (u v : E) (B : OpenPartialHomeomorph M E),
            psi.contLinear u = 1 ∧ psi.contLinear v = 0 ∧ eta.contLinear v = 1 ∧
            x ∈ B.source ∧ psi (B x) = 0 ∧ eta (B x) = 0 ∧
            (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
            (∀ y ∈ B.source, y ∈ N ↔ 0 ≤ psi (B y)) ∧
            (∀ y ∈ B.source,
              (y ∈ frontier R ∧ t ≤ z y) ↔ (psi (B y) = 0 ∧ 0 ≤ eta (B y))) ∧
            ∀ y ∈ B.source,
              (z y = t ∧ y ∈ R) ↔ (psi (B y) = 0 ∧ eta (B y) ≤ 0) := by
  classical
  let A : Set M := f '' S.space
  have hA : IsCompact A := (S.isCompact_space_of_finite hS).image_of_continuousOn hf.continuousOn
  have hAW : A ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hfW hx
  have hAR : A ⊆ R := by
    rintro _ ⟨x, hx, rfl⟩
    exact hfR hx
  obtain ⟨s, G, C, K, H, hC, hAC, hCW, hK, hG, hGPL, hGr, _, hHG, _⟩ :=
    exists_compact_PL_scalar_neighborhood_model e hcompat hcover hr hrPL hA hW hAW
  let ell : ((s → ℝ × E) × ℝ) →ᵃ[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (s → ℝ × E) ℝ).toContinuousAffineMap.toAffineMap
  have hellG (x : M) : ell (G x) = r x := hGr x
  let n := hK.toFinset.sup Finset.card
  have hn (b : Finset ((s → ℝ × E) × ℝ)) (hb : b ∈ K.faces) : b.card ≤ n + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hb)).trans (Nat.le_succ n)
  obtain ⟨L, hL, hLK, _, hLell⟩ := K.exists_subdivision_respectsAffineHyperplane hK hn ell
  let H' : C ≃ₜ L.space := H.trans (Homeomorph.setCongr hLK.space_eq.symm)
  have hHG' (x : C) : (H' x : (s → ℝ × E) × ℝ) = G x := hHG x
  have hGf : FinitePiecewiseAffineOn (G ∘ f) S.space :=
    hf.finitePiecewiseAffineOn_comp S hS hGPL
  obtain ⟨J, hJ, hJs⟩ := hGf.exists_finite_triangulation_image
  have hJA : J.space = G '' A := hJs.trans (image_image G f S.space).symm
  have hcutC (x : M) (hx : x ∈ C) : x ∈ R ↔ 0 ≤ ell (G x) := by
    rw [hellG]
    exact hcut x (hCW hx)
  have hzeroC (x : M) (hx : x ∈ C) : x ∈ frontier R ↔ ell (G x) = 0 := by
    rw [hellG]
    exact hzero x (hCW hx)
  obtain ⟨z, t, ht, hz, hzA, hP, hN, hAP, hAN, hNC, hT, hfront, hcorner⟩ :=
    exists_compact_PL_relative_deformation_neighborhood e hcompat hcover hC hAC hAR
      L J hL hJ H' G hG hGPL hHG' hJA ell hLell hR hcutC hzeroC hboundary
  exact ⟨z, t, ht, hz, hzA, hP, hN, hAP, hAN,
    hNC.trans (interior_subset.trans hCW), hT, hfront, hcorner⟩

end OpenPartialHomeomorph
