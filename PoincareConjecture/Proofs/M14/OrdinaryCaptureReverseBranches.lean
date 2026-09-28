import PoincareConjecture.Proofs.M14.OrdinaryCaptureBranches
import PoincareConjecture.Proofs.M14.Sec6_3_InitialVector











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  [T3Space C] [ConnectedSpace C] [SecondCountableTopology C]
  [MeasurableSpace C] [BorelSpace C] {K : SpacetimeInterval}
  {e : CompatibleSpacetimeCylinder G.spacetime (G.timeIntervals.interval K) C}
  {g : SpacetimeCylinderMetric e} {F : RicciFlow n C K.domain} {τmax : ℝ}
  (t₀ : (G.timeIntervals.interval K).Point) (c₀ : C)
  (D : M14OrdinaryCaptureData G C K e g F t₀.val τmax)
  (hCoordinates : SpacetimeGaugeTheory.{u, u} G.leafwise G.timeIntervals)

include hCoordinates




theorem ordinaryCapture_unique_branch_lift
    (hPath : M14PathCalculusConclusion G)
    (E : M14ExponentialFamily G t₀.val (e.toSpacetime (t₀, c₀)))
    (A : LExponentialGeometry F t₀.val τmax c₀)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (Z : G.Horizontal (e.toSpacetime (t₀, c₀)))
    (hZ : M14UniqueMinimizingBranch G t₀.val τ (e.toSpacetime (t₀, c₀)) E Z) :
    ∃ W : TangentSpace (𝓡 n) c₀,
      Z = g.spatialTangentEquiv t₀ c₀ W ∧
      A.toLExponentialFamily.uniqueMinimizing W τ ∧
      E.gamma Z (Real.sqrt τ) ∈ range e.toSpacetime ∧
      D.point_map (E.gamma Z (Real.sqrt τ)) = A.gamma W τ := by
  obtain ⟨hZD, p, hpcurve, hp, hunique⟩ := hZ
  have hx : e.toSpacetime (t₀, c₀) ∈ range e.toSpacetime := mem_range_self _
  let hc := D.capture_from_start 0 τ _ _ hmax.le hx p
  let q := D.path_map 0 τ _ _ p hc
  have hqmin := (ordinaryCapture_minimizing_transport D hCoordinates hmax.le hx p hc).mp hp
  have hqstart : q.curve 0 = c₀ :=
    (D.path_start_eq 0 τ _ _ p hc).trans (D.point_map_on_cylinder t₀ c₀)
  obtain ⟨W, hW, _⟩ := A.minimizers_lift τ hτ hmax q hqstart hqmin
  obtain ⟨hWD, hbranch⟩ := ordinaryCapture_minimizing_branch_identification t₀ c₀ D
    hPath E A.toLExponentialFamily W p hp hmax hc hW
  have hZW : Z = g.spatialTangentEquiv t₀ c₀ W := by
    apply initialVector_eq_of_backward_branches_eqOn E hZD hWD (Real.sqrt_pos.mpr hτ)
    simpa only [Real.sq_sqrt hτ.le] using hpcurve.symm.trans hbranch
  have hy : E.gamma Z (Real.sqrt τ) ∈ range e.toSpacetime := by
    simpa only [p.curve_end] using hc τ ⟨hτ.le, le_rfl⟩
  have hpoint : D.point_map (E.gamma Z (Real.sqrt τ)) = A.gamma W τ :=
    (D.path_end_eq 0 τ _ _ p hc).symm.trans (hW ⟨hτ.le, le_rfl⟩)
  refine ⟨W, hZW, ⟨hτ, hmax, ?_, ?_⟩, hy, hpoint⟩
  · apply M10.minimizing_of_eqOn hqmin
    simpa only [A.path_eq] using hW
  · intro r hrstart hrend hrmin
    obtain ⟨r', hrc, hrq⟩ := ordinaryCapture_exists_mapped_lift D hx hy
      p.base_time p.endpoint_time r
      (hrstart.trans (D.point_map_on_cylinder t₀ c₀).symm) (hrend.trans hpoint.symm)
    have hr'min := (ordinaryCapture_minimizing_transport D hCoordinates hmax.le hx r' hrc).mpr
      (M10.minimizing_of_eqOn hrmin hrq.symm)
    have hr'p := hunique r' hr'min
    intro s hs
    exact (hrq hs).symm.trans ((D.path_curve_eq 0 τ _ _ r' hrc s hs).symm.trans
      ((congrArg D.point_map (hr'p hs)).trans
        ((D.path_curve_eq 0 τ _ _ p hc s hs).trans (hW hs))))




theorem ordinaryCapture_unique_branch_transport
    (hPath : M14PathCalculusConclusion G)
    (E : M14ExponentialFamily G t₀.val (e.toSpacetime (t₀, c₀)))
    (A : LExponentialGeometry F t₀.val τmax c₀)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (Z : G.Horizontal (e.toSpacetime (t₀, c₀)))
    (hZ : M14UniqueMinimizingBranch G t₀.val τ (e.toSpacetime (t₀, c₀)) E Z) :
    A.toLExponentialFamily.uniqueMinimizing ((g.spatialTangentEquiv t₀ c₀).symm Z) τ ∧
      E.gamma Z (Real.sqrt τ) ∈ range e.toSpacetime ∧
      D.point_map (E.gamma Z (Real.sqrt τ)) =
        A.gamma ((g.spatialTangentEquiv t₀ c₀).symm Z) τ := by
  obtain ⟨W, hW, huniq, hcapture, hpoint⟩ :=
    ordinaryCapture_unique_branch_lift t₀ c₀ D hCoordinates hPath E A hτ hmax Z hZ
  have hWinv : (g.spatialTangentEquiv t₀ c₀).symm Z = W := by
    rw [hW, ContinuousLinearEquiv.symm_apply_apply]
  rw [hWinv]
  exact ⟨huniq, hcapture, hpoint⟩

end PoincareConjecture.M14
