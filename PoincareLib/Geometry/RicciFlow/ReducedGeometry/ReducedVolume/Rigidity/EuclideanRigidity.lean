import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Rigidity.Equality.RadialVelocity
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Rigidity.Exponential.RescaledMetric
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Rigidity.Exponential.DiffeomorphMetric
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Rigidity.StaticEndpoints

/-!
# One static Euclidean identification from maximal reduced volume

Morgan-Tian Proposition 7.27. Fix the rescaled exponential map at half
the equality time. Its actual radial velocity makes that single map
stationary throughout the interior interval; continuity retains it at
both endpoints.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.ReducedVolume

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in
/-- Maximal actual reduced volume produces one Euclidean identification on the closed interval. -/
theorem staticEuclideanFlowOn_of_reducedVolume_eq
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {b : ℝ} (hb : 0 < b) (hbmax : b < τmax)
    (heq : reducedVolume F T p b = euclideanReducedVolume n) :
    IsStaticEuclideanFlowOn F (Icc (T - b) T) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let c := b / 2
  have hc : c ∈ Ioo 0 b := ⟨by dsimp [c]; linarith, by dsimp [c]; linarith⟩
  have hglobal (s : ℝ) (hs : s ∈ Ioo 0 b) :=
    exponentialSliceChart_global_of_volume_eq hL hDifferential G hmax hT hwindow hcurvature
      hs.1 (hs.2.trans hbmax)
      (reducedVolume_eq_euclidean_of_le hL hDifferential G hmax hT hwindow hcurvature
        hb hbmax hs.1 hs.2.le heq)
  let f := rescaledExponentialDiffeomorph G c hc.1 (hglobal c hc).1 (hglobal c hc).2
  have hf : (f : EuclideanSpace ℝ (Fin n) → M) = rescaledExponential G c := by
    funext y
    exact rescaledExponentialDiffeomorph_apply G c hc.1 (hglobal c hc).1 (hglobal c hc).2 y
  have hv (s : ℝ) (hs : s ∈ Ioo 0 b) (Z : TangentSpace (𝓡 n) p) :
      curveVelocity (G.gamma Z) s =
        G.toLExponentialFamily.sliceDifferential Z s ((2 * s)⁻¹ • Z) := by
    obtain ⟨x, rfl⟩ := (metricCoordinates (F.metric T) p).surjective Z
    exact exponential_velocity_eq_radial_of_volume_eq hL hDifferential G hmax hT hwindow
      hcurvature hb hbmax heq x hs.1 hs.2
  have hsame (s : ℝ) (hs : s ∈ Ioo 0 b) :
      rescaledExponential G s = (f : EuclideanSpace ℝ (Fin n) → M) := by
    rw [hf]
    funext y
    exact rescaledExponential_eq_of_radial_velocity G hbmax.le f.symm hv y hs hc
  apply staticEuclideanFlowOn_of_interior_metric_eq hb
    (fun t ht ↦ hwindow ⟨by linarith [ht.1], ht.2⟩) f.symm
  intro s hs q v w
  apply metric_eq_of_diffeomorph_pullback (F.metric (T - s)) f _ q v w
  intro x u v
  rw [← hsame s hs]
  exact rescaledExponential_pairing G hs.1 (hglobal s hs).1 (hglobal s hs).2
    (fun x u v ↦ exponential_pairing_eq_of_volume_eq hL hDifferential G hmax hT hwindow
      hcurvature hb hbmax heq x u v hs.1 hs.2) x u v

end PoincareMT.ReducedVolume
