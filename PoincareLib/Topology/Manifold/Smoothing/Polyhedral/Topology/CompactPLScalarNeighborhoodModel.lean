import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Topology.CompactPLNeighborhoodModel
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PiecewiseAffineProd

/-!

# A compact original graph model retaining its cutting scalar

Append an actual original PL scalar to the existing compact
graph coordinates, then take a smaller finite image model.
The same scalar is literally the last affine coordinate, and
all original local chart projections are retained through
the first projection. See Hatcher, Theorem 3.1, pp. 45--46,
Hamilton 1976, p. 69 and M76 derivation 270.
-/

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

/-- A compact original PL neighborhood has a finite graph
model whose last coordinate is the entire supplied scalar.
The same graph map retains original chart-coordinate
projections around every modelled point. No sign or frontier
claim is made for an arbitrary scalar. See Hatcher Theorem
3.1, pp. 45--46, Hamilton p. 69 and M76 derivation 270. -/
theorem exists_compact_PL_scalar_neighborhood_model
    {M E ι : Type*} [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {r : M → ℝ} (hr : Continuous r)
    (hrPL : ∀ i, LocallyPiecewiseAffineOn (r ∘ (e i).symm) (e i).target)
    {A W : Set M} (hA : IsCompact A) (hW : IsOpen W) (hAW : A ⊆ W) :
    ∃ (s : Finset A) (G : M → (s → ℝ × E) × ℝ) (D : Set M)
      (K : SimplicialComplex ℝ ((s → ℝ × E) × ℝ)) (H : D ≃ₜ K.space),
      IsCompact D ∧ A ⊆ interior D ∧ D ⊆ W ∧ K.faces.Finite ∧
      Continuous G ∧ (∀ i, LocallyPiecewiseAffineOn (G ∘ (e i).symm) (e i).target) ∧
      (∀ x : M, (G x).2 = r x) ∧ K.space = G '' D ∧
      (∀ x : D, (H x : (s → ℝ × E) × ℝ) = G x) ∧
      ∀ x ∈ D, ∃ (i : ι) (V : Set M) (a : ((s → ℝ × E) × ℝ) →ᴬ[ℝ] E),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ G) (e i) V := by
  classical
  obtain ⟨s, F, C, J, H, hC, hAC, hCW, hJ, hF, hFPL, hHF, hproj⟩ :=
    exists_compact_PL_neighborhood_model e hcompat hcover hA hW hAW
  have hFinj : InjOn F C := by
    intro x hx y hy hxy
    have he : H ⟨x, hx⟩ = H ⟨y, hy⟩ := Subtype.ext
      ((hHF ⟨x, hx⟩).trans (hxy.trans (hHF ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective he)
  let G : M → (s → ℝ × E) × ℝ := fun x => (F x, r x)
  have hG : Continuous G := hF.prodMk hr
  have hGPL (i : ι) : LocallyPiecewiseAffineOn (G ∘ (e i).symm) (e i).target :=
    (hFPL i).prod_mk (hrPL i)
  have hGinj : InjOn G (interior C) := by
    intro x hx y hy hxy
    exact hFinj (interior_subset hx) (interior_subset hy) (congrArg Prod.fst hxy)
  obtain ⟨D, K, H', hD, hAD, hDC, hK, hKG, hHG⟩ :=
    exists_compact_finitePL_image_neighborhood e G hG hcover hGPL
      hA isOpen_interior hAC hGinj
  refine ⟨s, G, D, K, H', hD, hAD, hDC.trans (interior_subset.trans hCW),
    hK, hG, hGPL, fun _ => rfl, hKG, hHG, ?_⟩
  intro x hx
  obtain ⟨i, V, a, hV, hxV, hVe, hVa⟩ := hproj x (interior_subset (hDC hx))
  let b : ((s → ℝ × E) × ℝ) →ᴬ[ℝ] E :=
    a.comp (ContinuousLinearMap.fst ℝ (s → ℝ × E) ℝ).toContinuousAffineMap
  exact ⟨i, V, b, hV, hxV, hVe, fun _ hy => hVa hy⟩

end OpenPartialHomeomorph
