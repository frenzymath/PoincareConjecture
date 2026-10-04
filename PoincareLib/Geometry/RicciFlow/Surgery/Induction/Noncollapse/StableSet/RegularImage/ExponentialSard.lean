import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.RegularImage.SurvivalSlice
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.RegularImage.LocalNullity

/-!
# Null critical values of the actual exponential survival map

Morgan--Tian Corollary 6.67, printed p. 140. The initial horizontal
fiber is identified with Euclidean space using the actual base-slice
tangent equivalence. Sard's theorem is applied only on the survival
domain, and the actual slice differential is identified with the frozen
horizontal exponential differential. The stable endpoint map is not used.
-/

set_option autoImplicit false
-- The supplied slice tangent equivalences retain their chosen norm instances.
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T tau : ℝ} {x : G.Point}

/-- The image of the noninvertible actual exponential differentials on
the whole survival domain is null in the selected slice metric,
Corollary 6.67, p. 140. -/
theorem exponential_survival_criticalValues_null
    (E : M14ExponentialFamily G T x) (htau : 0 ≤ tau)
    (q0 : (G.slices (T - tau)).Point) :
    calibratedMetricVolume (G.slices (T - tau)).metricOnPoints
      (survivalSliceMap E tau htau q0 ''
        {Z | ∃ hZ : (Z, Real.sqrt tau) ∈ E.domain,
          ¬ Function.Bijective (E.differential Z (Real.sqrt tau) hZ)}) = 0 := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] G.Horizontal x :=
    (G.slices T).tangentEquiv ⟨x, E.base_time⟩
  let f := survivalSliceMap E tau htau q0
  let D : Set (EuclideanSpace ℝ (Fin n)) :=
    {v | (e v, Real.sqrt tau) ∈ E.domain}
  have hf (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ D) :
      MDifferentiableAt (𝓘(ℝ, G.Horizontal x)) (𝓡 n) f (e v) :=
    (survivalSliceMap_smooth E htau q0 hv).mdifferentiableAt (by simp)
  have hcomp (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ D) :
      MDifferentiableAt (𝓡 n) (𝓡 n) (f ∘ e) v :=
    (hf v hv).comp v e.mdifferentiableAt
  have hnull := survival_criticalValues_null (G.slices (T - tau)).metricOnPoints D hcomp
  apply measure_mono_null _ hnull
  rintro q ⟨Z, ⟨hZ, hcritical⟩, rfl⟩
  have hv : e.symm Z ∈ D := by simpa only [D, mem_ofPred_eq, e.apply_symm_apply] using hZ
  refine ⟨e.symm Z, ⟨hv, ?_⟩, by simp only [Function.comp_apply, e.apply_symm_apply, f]⟩
  intro hbij
  apply hcritical
  apply (survivalSliceMap_differential_bijective_iff E htau q0 hZ).mp
  have hchain := mfderiv_comp (e.symm Z) (hf (e.symm Z) hv) e.mdifferentiableAt
  rw [ContinuousLinearEquiv.mfderiv_eq, e.apply_symm_apply] at hchain
  rw [hchain] at hbij
  exact (Function.Bijective.of_comp_iff _ e.bijective).mp hbij

end PoincareMT.Proofs.M46
