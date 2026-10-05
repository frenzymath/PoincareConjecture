import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.UnitCover

/-!
# The static two-sheeted Ricci-null cover

Local smooth unit sections of the actual one-dimensional Ricci kernel
trivialize its intrinsic orientation cover. The construction uses the
unit tangent-bundle subtype and its existing topology. This isolates
the covering step of Morgan--Tian Claim 9.45, pp. 208-209, for the
finite-window null branch of Claim 11.7, pp. 270-271.
-/

set_option autoImplicit false

open Set PoincareMT.RicciFlow.Splitting
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M30

/-- Local smooth unit null sections construct the actual two-sheeted
Ricci-kernel cover (Claims 9.45 and 11.7, pp. 208-209 and 270-271).
No common Ricci-flow interval or local parallelism is needed. -/
theorem unitRicciKernel_doubleCover_of_local_unit_sections
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hdim : ∀ x : M, ricciNullity D x = 1)
    (hsections : ∀ x : M,
      ∃ (U : Set M) (V : (y : M) → TangentSpace (𝓡 n) y),
        IsOpen U ∧ x ∈ U ∧
        ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) U ∧
        ∀ y ∈ U, g.inner y (V y) (V y) = 1 ∧
          ∀ w : TangentSpace (𝓡 n) y, D.ricci y (V y) w = 0) :
    IsCoveringMap (unitRicciKernelProjection D) ∧
      ∀ x : M, Nat.card (unitRicciKernelProjection D ⁻¹' {x}) = 2 := by
  have heven (x : M) : IsEvenlyCovered (unitRicciKernelProjection D) x LineSign := by
    obtain ⟨U, V, hU, hx, hV, hn⟩ := hsections x
    exact ⟨inferInstance, U, hx, hU,
      hU.preimage (continuous_unitRicciKernelProjection D),
      unitRicciKernelLocalHomeomorph D V hV (fun y _ => hdim y)
        (fun y hy => (hn y hy).1) (fun y hy => (hn y hy).2), fun _ => rfl⟩
  refine ⟨fun x => (heven x).to_isEvenlyCovered_preimage, ?_⟩
  intro x
  rw [← Nat.card_congr (heven x).fiberHomeomorph.toEquiv]
  exact Set.ncard_pair (by norm_num : (1 : ℝ) ≠ -1)

end PoincareMT.M30
