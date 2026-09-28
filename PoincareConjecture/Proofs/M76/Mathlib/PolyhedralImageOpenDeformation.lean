import PoincareConjecture.Proofs.M76.Mathlib.OpenPLCutDeformationFamily
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLScalarNeighborhoodModel
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInCharts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation











set_option autoImplicit false

open Set Geometry unitInterval

namespace OpenPartialHomeomorph






theorem exists_polyhedral_image_open_cut_deformation
    {M E D ι : Type*} [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    (S : SimplicialComplex ℝ D) (hS : S.faces.Finite)
    {f : D → M} (hf : PolyhedralPLInCharts e f S.space)
    {W : Set M} (hW : IsOpen W) (hfW : MapsTo f S.space W)
    {r : M → ℝ} (hr : Continuous r)
    (hrPL : ∀ i, LocallyPiecewiseAffineOn (r ∘ (e i).symm) (e i).target) :
    ∃ (z : M → ℝ) (Q : Set M), IsCompact Q ∧ Q ⊆ W ∧
      Continuous z ∧ (∀ x, x ∉ Q → z x = 0) ∧
      (∀ i, LocallyPiecewiseAffineOn (z ∘ (e i).symm) (e i).target) ∧
      (∀ x ∈ f '' S.space, z x = 1) ∧
      ∀ c : ℝ, 0 < c → c < 1 →
        let P : Set M := {x | c ≤ z x}
        let O : Set M := {x | c < z x}
        IsCompact P ∧ IsOpen O ∧ f '' S.space ⊆ O ∧ O ⊆ P ∧ P ⊆ W ∧
          ∃ (a : C(O, O))
            (H : (ContinuousMap.id O).HomotopyRel a {x : O | (x : M) ∈ f '' S.space}),
            range a = {x : O | (x : M) ∈ f '' S.space} ∧
            (∀ (t : I) (x : O), 0 ≤ r x → 0 ≤ r (H (t, x))) ∧
            (∀ (t : I) (x : O), r x = 0 → r (H (t, x)) = 0) ∧
            ∀ (t : I) (x : O), z (H (t, x)) =
              (1 - (t : ℝ)) * z x + (t : ℝ) := by
  classical
  let A : Set M := f '' S.space
  have hA : IsCompact A :=
    (S.isCompact_space_of_finite hS).image_of_continuousOn hf.continuousOn
  have hAW : A ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hfW hx
  obtain ⟨s, G, C, K, B, hC, hAC, hCW, hK, hG, hGPL, hGr, _, hBG, _⟩ :=
    exists_compact_PL_scalar_neighborhood_model e hcompat hcover hr hrPL hA hW hAW
  let ell : ((s → ℝ × E) × ℝ) →ᵃ[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (s → ℝ × E) ℝ).toContinuousAffineMap.toAffineMap
  have hellG (x : M) : ell (G x) = r x := hGr x
  let n := hK.toFinset.sup Finset.card
  have hn (b : Finset ((s → ℝ × E) × ℝ)) (hb : b ∈ K.faces) : b.card ≤ n + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hb)).trans (Nat.le_succ n)
  obtain ⟨L, hL, hLK, _, hLell⟩ := K.exists_subdivision_respectsAffineHyperplane hK hn ell
  let B' : C ≃ₜ L.space := B.trans (Homeomorph.setCongr hLK.space_eq.symm)
  have hBG' (x : C) : (B' x : (s → ℝ × E) × ℝ) = G x := hBG x
  have hGf : FinitePiecewiseAffineOn (G ∘ f) S.space :=
    hf.finitePiecewiseAffineOn_comp S hS hGPL
  obtain ⟨J, hJ, hJs⟩ := hGf.exists_finite_triangulation_image
  have hJA : J.space = G '' A := hJs.trans (image_image G f S.space).symm
  obtain ⟨z, Q, hQ, hQC, hz, hzoff, hzPL, hzA, hlevel⟩ :=
    exists_open_PL_cut_deformation_family e hC hAC L J hL hJ B' G hG hGPL
      hBG' hJA ell hLell
  refine ⟨z, Q, hQ, hQC.trans (interior_subset.trans hCW), hz, hzoff, hzPL, hzA, ?_⟩
  intro c hc hc1
  obtain ⟨hP, hO, hAO, hOP, hPC, a, H, ha, hpos, hzero, hmass⟩ := hlevel c hc hc1
  have harange : range a = {x : {y : M | c < z y} | (x : M) ∈ A} := by
    change Subtype.val '' range a = A at ha
    ext x
    constructor
    · intro hx
      exact ha.subset (mem_image_of_mem Subtype.val hx)
    · intro hx
      obtain ⟨y, hy, hyx⟩ := ha.superset hx
      exact (Subtype.ext hyx : y = x) ▸ hy
  refine ⟨hP, hO, hAO, hOP, hPC.trans (interior_subset.trans hCW),
    a, H, harange, ?_, ?_, hmass⟩
  · intro t x hx
    simpa only [hellG] using hpos t x (by simpa only [hellG] using hx)
  · intro t x hx
    simpa only [hellG] using hzero t x (by simpa only [hellG] using hx)

end OpenPartialHomeomorph
