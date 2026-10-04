import PoincareLib.Topology.Manifold.Schoenflies.Plane.Rounding.Isotopy
import PoincareLib.Topology.Manifold.Schoenflies.Plane.Polygon.Reduction.PushIn

/-!
# Ambient realization of an admissible vertex push

The simple polygon motion pushing an admissible vertex to the midpoint of
its neighbors has a coherent smooth rounding realized by an ambient
diffeomorphism. This is the smooth version of the vertex move in Munkres,
Differentiable isotopies on the 2-sphere, Lemma 2.6, printed p. 196.
-/

set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] {n : ℕ} [NeZero n]

omit [Fact (Module.finrank ℝ E = 2)] [NeZero n] in
theorem IsSimplePolygon.polygonPushVertex_one_midpoint {p : Polygon E n}
    (hp : IsSimplePolygon p) (k : Fin n) :
    polygonPushVertex p k 1 k = midpoint ℝ
      (polygonPushVertex p k 1 ((finRotate n).symm k))
      (polygonPushVertex p k 1 (finRotate n k)) := by
  have hprev : (finRotate n).symm k ≠ k := by
    intro heq
    have hne := hp.hasNondegenerateEdges ((finRotate n).symm k)
    rw [Equiv.apply_symm_apply, heq] at hne
    exact hne rfl
  have hnext : finRotate n k ≠ k := by
    intro heq
    exact hp.hasNondegenerateEdges k (congrArg p heq.symm)
  rw [polygonPushVertex_one_vertex]
  simp only [polygonPushVertex, polygonReplaceVertex_apply_of_ne _ _ _ hprev,
    polygonReplaceVertex_apply_of_ne _ _ _ hnext]

/-- An admissible vertex push gives an actual supported ambient map of a
common coherent rounding of the initial and final polygons. -/
theorem exists_ambient_rounded_vertex_push
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2))
    {p : Polygon E n} (hp : IsSimplePolygon p) (k : Fin n)
    (had : IsAdmissibleVertex p k) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ ∃ ρ : ℝ → ℝ,
      ContDiff ℝ ∞ ρ ∧ (∀ s, δ ≤ |s| → ρ s = |s|) ∧
      (∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) ∧ (∀ s, |deriv ρ s| ≤ 1) ∧
      ∃ F : E ≃ₘ[ℝ] E,
        (∃ K : Set E, IsCompact K ∧ ∀ x ∉ K, F x = x) ∧
        F '' range (roundedPolygonParameter ρ p) =
          range (roundedPolygonParameter ρ (polygonPushVertex p k 1)) := by
  obtain ⟨δ, hδ, hδsmall, ρ, hρ, htail, hbound, hder, Phi, _, _, ⟨K, hK, hfix⟩,
      hPhi⟩ := exists_ambient_isotopy_of_polygon_family e o (polygonPushVertex p k)
      (fun i => contDiff_polygonPushVertex_apply k i (fun _ => contDiff_const) contDiff_id)
      (a := 0) (b := 1) zero_le_one (fun t ht => hp.isSimple_polygonPushVertex k had ht)
  refine ⟨δ, hδ, hδsmall, ρ, hρ, htail, hbound, hder, Phi 1,
    ⟨K, hK, hfix 1⟩, ?_⟩
  simpa only [polygonPushVertex_zero] using hPhi 1 (by simp)

/-- Every sufficiently small coherent profile realizes the same admissible push. -/
theorem exists_uniform_ambient_rounded_vertex_push
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2))
    {p : Polygon E n} (hp : IsSimplePolygon p) (k : Fin n)
    (had : IsAdmissibleVertex p k) :
    ∃ d : ℝ, 0 < d ∧ d < 1 / 4 ∧
      ∀ δ : ℝ, 0 < δ → δ < d → ∀ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ →
        (∀ s, δ ≤ |s| → ρ s = |s|) →
        (∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) → (∀ s, |deriv ρ s| ≤ 1) →
        ∃ F : E ≃ₘ[ℝ] E,
          (∃ K : Set E, IsCompact K ∧ ∀ x ∉ K, F x = x) ∧
          F '' range (roundedPolygonParameter ρ p) =
            range (roundedPolygonParameter ρ (polygonPushVertex p k 1)) := by
  obtain ⟨d, hd, hdsmall, hmotion⟩ := exists_uniform_ambient_isotopy_of_polygon_family e o
    (polygonPushVertex p k)
    (fun i => contDiff_polygonPushVertex_apply k i (fun _ => contDiff_const) contDiff_id)
    (a := 0) (b := 1) zero_le_one (fun t ht => hp.isSimple_polygonPushVertex k had ht)
  refine ⟨d, hd, hdsmall, ?_⟩
  intro δ hδ hδd ρ hρ htail hbound hder
  obtain ⟨Phi, _, _, ⟨K, hK, hfix⟩, hPhi⟩ := hmotion δ hδ hδd ρ hρ htail hbound hder
  refine ⟨Phi 1, ⟨K, hK, hfix 1⟩, ?_⟩
  simpa only [polygonPushVertex_zero] using hPhi 1 (by simp)

end Poincare.Manifold.Schoenflies.Plane
