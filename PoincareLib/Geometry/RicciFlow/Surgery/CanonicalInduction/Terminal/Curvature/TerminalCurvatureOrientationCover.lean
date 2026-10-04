import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Orientation
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Completeness

/-!
# The actual complete orientation cover of the terminal null line

Smooth local sections of the ambient Ricci kernel trivialize its two unit
directions. The metric upstairs is the literal projection pullback.
Source: MT static cover discussion preceding Corollary 4.20, pp. 72-73;
derivations/terminal-curvature-nullity.md, Stage C5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M47

open RicciFlow.Splitting

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

/-- The intrinsic unit Ricci kernel is a genuine two-sheeted cover when
its ambient rank-one line has actual local smooth unit sections. -/
theorem terminalCurvature_orientation_cover
    (D : LeviCivitaData g) (hrank : ∀ y, ricciNullity D y = 1)
    (hsections : ∀ x : M,
      ∃ (U : Set M) (V : (y : M) → TangentSpace (𝓡 3) y),
        IsOpen U ∧ x ∈ U ∧
        ContMDiffOn (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% V) U ∧
        ∀ y ∈ U, g.inner y (V y) (V y) = 1 ∧ ∀ w, D.ricci y (V y) w = 0) :
    Nonempty (NullOrientationCover D) := by
  have heven (x : M) : IsEvenlyCovered (unitRicciKernelProjection D) x LineSign := by
    obtain ⟨U, V, hU, hx, hV, hnull⟩ := hsections x
    exact ⟨inferInstance, U, hx, hU,
      hU.preimage (continuous_unitRicciKernelProjection D),
      unitRicciKernelLocalHomeomorph D V hV (fun y _ => hrank y)
        (fun y hy => (hnull y hy).1) (fun y hy => (hnull y hy).2), fun _ => rfl⟩
  have hcover : IsCoveringMap (unitRicciKernelProjection D) :=
    fun x => (heven x).to_isEvenlyCovered_preimage
  have hcard (x : M) : Nat.card (unitRicciKernelProjection D ⁻¹' {x}) = 2 := by
    rw [← Nat.card_congr (heven x).fiberHomeomorph.toEquiv]
    exact Set.ncard_pair (by norm_num : (1 : ℝ) ≠ -1)
  exact ⟨{
    covering := hcover
    fiber_card := hcard
    deck := unitRicciKernelDeckHomeomorph D
    deck_involutive := unitRicciKernelReverse_involutive D
    deck_projection := fun p => unitRicciKernelProjection_reverse D p
    deck_free := unitRicciKernelReverse_fixedPointFree D
  }⟩

/-- The complete ambient terminal metric gives the actual orientation
cover its complete projection-pullback metric, with the original map. -/
theorem terminalCurvature_orientation_cover_geometry [T3Space M]
    (D : LeviCivitaData g) (C : NullOrientationCover D) (hcomplete : MetricComplete g) :
    letI := unitRicciKernelChartedSpace D C.covering
    letI := unitRicciKernelIsManifold D C.covering
    letI := unitRicciKernelT3Space D C.covering
    MetricComplete (unitRicciKernelMetric D C.covering) ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (unitRicciKernelProjection D) ∧
      ∀ (p : UnitRicciKernel D) (v w : TangentSpace (𝓡 3) p),
        (unitRicciKernelMetric D C.covering).inner p v w =
          g.inner (unitRicciKernelProjection D p)
            (mfderiv (𝓡 3) (𝓡 3) (unitRicciKernelProjection D) p v)
            (mfderiv (𝓡 3) (𝓡 3) (unitRicciKernelProjection D) p w) := by
  let := unitRicciKernelChartedSpace D C.covering
  let := unitRicciKernelIsManifold D C.covering
  let := unitRicciKernelT3Space D C.covering
  exact ⟨unitRicciKernelMetric_complete D C.covering C.fiber_card hcomplete,
    unitRicciKernelProjection_isLocalDiffeomorph D C.covering, fun _ _ _ => rfl⟩

end PoincareMT.M47
