import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.CoverCoordinate

/-!
# The actual parallel unit field on the null-line orientation cover

The vector at an oriented unit-null lift is the inverse projection
differential of its literal tangent vector. Actual local parallel
sections identify its smooth germ and its covariant derivative.
Source: MT static cover discussion preceding Corollary 4.20, pp. 72-73;
derivations/terminal-curvature-parallel-flow.md, Stage C6a.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M47

open RicciFlow.Splitting

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The actual oriented unit-null vector lifted through the actual
projection differential of the intrinsic orientation cover. -/
noncomputable def terminalCurvatureOrientedField
    (D : LeviCivitaData g) (hc : IsCoveringMap (unitRicciKernelProjection D)) :
    letI := unitRicciKernelChartedSpace D hc
    (p : UnitRicciKernel D) → TangentSpace (𝓡 n) p := by
  letI := unitRicciKernelChartedSpace D hc
  exact fun p => (mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelProjection D) p).inverse p.val.snd

/-- Actual prescribed parallel sections prove that the intrinsic field
on the orientation cover is smooth, unit length and parallel. -/
theorem terminalCurvature_oriented_field_geometry
    (D : LeviCivitaData g) (hc : IsCoveringMap (unitRicciKernelProjection D))
    (hrank : ∀ y, ricciNullity D y = 1)
    (hsections : ∀ p : UnitRicciKernel D,
      ∃ (U : Set M) (V : (y : M) → TangentSpace (𝓡 n) y),
        IsOpen U ∧ p.val.proj ∈ U ∧
        ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) U ∧ V p.val.proj = p.val.snd ∧
        ∀ y ∈ U, g.inner y (V y) (V y) = 1 ∧
          (∀ w, D.ricci y (V y) w = 0) ∧ ∀ w, D.connection V y w = 0) :
    letI := unitRicciKernelChartedSpace D hc
    letI := unitRicciKernelIsManifold D hc
    let g' := unitRicciKernelMetric D hc
    let W := terminalCurvatureOrientedField D hc
    ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% W) ∧
      ∀ p, g'.inner p (W p) (W p) = 1 ∧
        ∀ v, g'.leviCivitaData.connection W p v = 0 := by
  let := unitRicciKernelChartedSpace D hc
  let := unitRicciKernelIsManifold D hc
  let g' := unitRicciKernelMetric D hc
  let D' := g'.leviCivitaData
  let proj := unitRicciKernelProjection D
  let W := terminalCurvatureOrientedField D hc
  have hproj := unitRicciKernelProjection_isLocalDiffeomorph D hc
  have hinv (p : UnitRicciKernel D) : (mfderiv (𝓡 n) (𝓡 n) proj p).IsInvertible :=
    ⟨hproj.mfderivToContinuousLinearEquiv (by simp) p, rfl⟩
  have hmetric (p : UnitRicciKernel D) (v w : TangentSpace (𝓡 n) p) :
      g'.inner p v w = g.inner (proj p)
        (mfderiv (𝓡 n) (𝓡 n) proj p v) (mfderiv (𝓡 n) (𝓡 n) proj p w) := rfl
  have hlocal (p : UnitRicciKernel D) :
      ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% W) p ∧
      g'.inner p (W p) (W p) = 1 ∧ ∀ v, D'.connection W p v = 0 := by
    obtain ⟨U, V, hU, hp, hV, hVp, hn⟩ := hsections p
    have heq : W =ᶠ[𝓝 p] mpullback (𝓡 n) (𝓡 n) proj V := by
      filter_upwards [unitRicciKernel_eventually_eq_section D hU V hV
        (fun y _ => hrank y) (fun y hy => (hn y hy).1)
        (fun y hy => (hn y hy).2.1) p hp hVp] with q hq
      change (mfderiv (𝓡 n) (𝓡 n) proj q).inverse q.val.snd =
        (mfderiv (𝓡 n) (𝓡 n) proj q).inverse (V (proj q))
      rw [hq]
      rfl
    have hVs : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) (proj p) :=
      hV.contMDiffAt (hU.mem_nhds hp)
    have hWs : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
        (T% (mpullback (𝓡 n) (𝓡 n) proj V)) p :=
      hVs.mpullback_vectorField_preimage (m := ∞) (n := ∞) (f := proj) (x₀ := p)
        (show ContMDiffAt (𝓡 n) (𝓡 n) ∞ proj p from hproj.contMDiff p)
        (hinv p) (by simp)
    have heqT : (T% W) =ᶠ[𝓝 p] (T% (mpullback (𝓡 n) (𝓡 n) proj V)) := by
      filter_upwards [heq] with q hq
      exact congrArg (fun v => (⟨q, v⟩ : TangentBundle (𝓡 n) (UnitRicciKernel D))) hq
    refine ⟨hWs.congr_of_eventuallyEq heqT, ?_, ?_⟩
    · change g.inner (proj p)
        ((mfderiv (𝓡 n) (𝓡 n) proj p)
          ((mfderiv (𝓡 n) (𝓡 n) proj p).inverse p.val.snd))
        ((mfderiv (𝓡 n) (𝓡 n) proj p)
          ((mfderiv (𝓡 n) (𝓡 n) proj p).inverse p.val.snd)) = 1
      rw [(hinv p).self_apply_inverse]
      exact p.property.1
    · intro v
      have hconn := D'.connection_mpullback_of_metric_pullback D (hproj.contMDiff p)
        (Eventually.of_forall hinv) (Eventually.of_forall hmetric)
        (hVs.mdifferentiableAt (by simp)) v
      have hz : D.connection V (unitRicciKernelProjection D p)
          (mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelProjection D) p v) = 0 :=
        (hn _ hp).2.2 _
      rw [hz, map_zero] at hconn
      have hsame := D'.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        ((hWs.congr_of_eventuallyEq heqT).mdifferentiableAt (by simp))
        (hWs.mdifferentiableAt (by simp)) Filter.univ_mem heq
      exact (congrArg (fun A => A v) hsame).trans hconn
  exact ⟨fun p => (hlocal p).1, fun p => (hlocal p).2⟩

end PoincareMT.M47
