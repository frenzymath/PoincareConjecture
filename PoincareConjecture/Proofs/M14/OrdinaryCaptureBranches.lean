import PoincareConjecture.Proofs.M14.OrdinaryCaptureInitialPath
import PoincareConjecture.Proofs.M10.MinimizingLifts











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



theorem ordinaryCapture_minimizing_family_lift
    (A : LExponentialFamily F t₀.val τmax c₀) (W : TangentSpace (𝓡 n) c₀)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (hmin : IsMinimizingBackwardLPath F t₀.val 0 τ (A.path W τ hτ hmax)) :
    ∃ y : G.Point, ∃ p : M14BackwardPath G t₀.val 0 τ (e.toSpacetime (t₀, c₀)) y,
      M14IsMinimizing p ∧
      ∃ hc : ∀ s ∈ Icc 0 τ, p.curve s ∈ range e.toSpacetime,
        EqOn (D.path_map 0 τ _ y p hc).curve (A.gamma W) (Icc 0 τ) := by
  let q := A.path W τ hτ hmax
  let t : (G.timeIntervals.interval K).Point := ⟨t₀.val - τ, q.time_mem τ ⟨hτ.le, le_rfl⟩⟩
  let y := e.toSpacetime (t, q.curve τ)
  have hx : e.toSpacetime (t₀, c₀) ∈ range e.toSpacetime := mem_range_self _
  have hy : y ∈ range e.toSpacetime := mem_range_self _
  obtain ⟨p, hc, hpq⟩ := ordinaryCapture_exists_mapped_lift D hx hy
    (by simpa only [sub_zero] using e.time_eq (t₀, c₀)) (e.time_eq (t, q.curve τ)) q
    (by rw [D.point_map_on_cylinder, A.path_eq, A.gamma_at_zero])
    (D.point_map_on_cylinder t (q.curve τ)).symm
  refine ⟨y, p, (ordinaryCapture_minimizing_transport D hCoordinates hmax.le hx p hc).mpr
    (M10.minimizing_of_eqOn hmin hpq.symm), hc, ?_⟩
  simpa only [q, A.path_eq] using hpq



theorem ordinaryCapture_minimizer_unique
    {τ : ℝ} {y : G.Point} (A : LExponentialFamily F t₀.val τmax c₀)
    (W : TangentSpace (𝓡 n) c₀) (huniq : A.uniqueMinimizing W τ)
    (p : M14BackwardPath G t₀.val 0 τ (e.toSpacetime (t₀, c₀)) y)
    (hc : ∀ s ∈ Icc 0 τ, p.curve s ∈ range e.toSpacetime)
    (hcurve : EqOn (D.path_map 0 τ _ y p hc).curve (A.gamma W) (Icc 0 τ))
    (q : M14BackwardPath G t₀.val 0 τ (e.toSpacetime (t₀, c₀)) y)
    (hq : M14IsMinimizing q) : EqOn q.curve p.curve (Icc 0 τ) := by
  obtain ⟨hτ, hmax, _, hunique⟩ := huniq
  have hx : e.toSpacetime (t₀, c₀) ∈ range e.toSpacetime := mem_range_self _
  let hqc := D.capture_from_start 0 τ _ y hmax.le hx q
  have hqmin := (ordinaryCapture_minimizing_transport D hCoordinates hmax.le hx q hqc).mp hq
  have hqstart : (D.path_map 0 τ _ y q hqc).curve 0 = c₀ :=
    (D.path_start_eq 0 τ _ y q hqc).trans (D.point_map_on_cylinder t₀ c₀)
  have hqend : (D.path_map 0 τ _ y q hqc).curve τ = A.gamma W τ :=
    (D.path_end_eq 0 τ _ y q hqc).trans
      ((D.path_end_eq 0 τ _ y p hc).symm.trans (hcurve ⟨hτ.le, le_rfl⟩))
  have hqcurve := hunique (D.path_map 0 τ _ y q hqc) hqstart hqend hqmin
  intro s hs
  apply ordinaryCapture_point_injective D (hqc s hs) (hc s hs)
    ((q.curve_time s hs).trans (p.curve_time s hs).symm)
  exact (D.path_curve_eq 0 τ _ y q hqc s hs).trans
    ((hqcurve hs).trans ((hcurve hs).symm.trans (D.path_curve_eq 0 τ _ y p hc s hs).symm))




theorem ordinaryCapture_unique_family_transport
    (hPath : M14PathCalculusConclusion G)
    (E : M14ExponentialFamily G t₀.val (e.toSpacetime (t₀, c₀)))
    (A : LExponentialFamily F t₀.val τmax c₀) (W : TangentSpace (𝓡 n) c₀)
    {τ : ℝ} (huniq : A.uniqueMinimizing W τ) :
    M14UniqueMinimizingBranch G t₀.val τ (e.toSpacetime (t₀, c₀)) E
        (g.spatialTangentEquiv t₀ c₀ W) ∧
      E.gamma (g.spatialTangentEquiv t₀ c₀ W) (Real.sqrt τ) ∈ range e.toSpacetime ∧
      D.point_map (E.gamma (g.spatialTangentEquiv t₀ c₀ W) (Real.sqrt τ)) = A.gamma W τ := by
  obtain ⟨hτ, hmax, hmin, hunique⟩ := huniq
  obtain ⟨y, p, hp, hc, hcurve⟩ :=
    ordinaryCapture_minimizing_family_lift t₀ c₀ D hCoordinates A W hτ hmax hmin
  obtain ⟨hdom, heq⟩ := ordinaryCapture_minimizing_branch_identification t₀ c₀ D
    hPath E A W p hp hmax hc hcurve
  have hy : y = E.gamma (g.spatialTangentEquiv t₀ c₀ W) (Real.sqrt τ) :=
    p.curve_end.symm.trans (heq ⟨hτ.le, le_rfl⟩)
  have hcapture : y ∈ range e.toSpacetime := by
    simpa only [p.curve_end] using hc τ ⟨hτ.le, le_rfl⟩
  have hpoint : D.point_map y = A.gamma W τ :=
    (D.path_end_eq 0 τ _ y p hc).symm.trans (hcurve ⟨hτ.le, le_rfl⟩)
  cases hy
  refine ⟨⟨hdom, p, heq, hp, ?_⟩, hcapture, hpoint⟩
  exact ordinaryCapture_minimizer_unique t₀ c₀ D hCoordinates A W
    ⟨hτ, hmax, hmin, hunique⟩ p hc hcurve

end PoincareConjecture.M14
