import PoincareConjecture.Proofs.M14.OrdinaryCaptureAction
import PoincareConjecture.Proofs.M08.PathCongruence

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
  {g : SpacetimeCylinderMetric e} {F : RicciFlow n C K.domain} {T τmax : ℝ}
  (D : M14OrdinaryCaptureData G C K e g F T τmax)
  (hCoordinates : SpacetimeGaugeTheory.{u, u} G.leafwise G.timeIntervals)

include hCoordinates

theorem ordinaryCapture_lift_action {τ₁ τ₂ : ℝ} {x y : G.Point}
    (hx : x ∈ range e.toSpacetime) (hy : y ∈ range e.toSpacetime)
    (htx : G.spacetime.timeFunction x = T - τ₁)
    (hty : G.spacetime.timeFunction y = T - τ₂)
    (q : BackwardTimePath F T τ₁ τ₂)
    (hq₁ : q.curve τ₁ = D.point_map x) (hq₂ : q.curve τ₂ = D.point_map y) :
    ∃ p : M14BackwardPath G T τ₁ τ₂ x y,
      backwardLLength F T τ₁ τ₂ q.curve = M14BackwardLAction G p := by
  obtain ⟨p, hc, hp⟩ := ordinaryCapture_exists_mapped_lift D hx hy htx hty q hq₁ hq₂
  exact ⟨p, (M08.backwardLLength_congr F T q.ordered.le hp).symm.trans
    (ordinaryCapture_action_transport D hCoordinates p hc)⟩

theorem ordinaryCapture_actionSet_transport {τ₁ τ₂ : ℝ} {x y : G.Point}
    (hmax : τ₂ ≤ τmax) (hx : x ∈ range e.toSpacetime)
    (hy : y ∈ range e.toSpacetime)
    (htx : G.spacetime.timeFunction x = T - τ₁)
    (hty : G.spacetime.timeFunction y = T - τ₂) :
    M14ActionSet G T τ₁ τ₂ x y =
      {a | ∃ q : BackwardTimePath F T τ₁ τ₂,
        q.curve τ₁ = D.point_map x ∧ q.curve τ₂ = D.point_map y ∧
        a = backwardLLength F T τ₁ τ₂ q.curve} := by
  ext a
  constructor
  · rintro ⟨p, hp⟩
    let hc := D.capture_from_start τ₁ τ₂ x y hmax hx p
    refine ⟨D.path_map τ₁ τ₂ x y p hc, D.path_start_eq τ₁ τ₂ x y p hc,
      D.path_end_eq τ₁ τ₂ x y p hc, ?_⟩
    exact hp.symm.trans (ordinaryCapture_action_transport D hCoordinates p hc).symm
  · rintro ⟨q, hq₁, hq₂, ha⟩
    obtain ⟨p, hp⟩ := ordinaryCapture_lift_action D hCoordinates hx hy htx hty q hq₁ hq₂
    exact ⟨p, hp.symm.trans ha.symm⟩

theorem ordinaryCapture_reducedLength_transport {τ : ℝ} {x y : G.Point}
    (hτ : 0 < τ) (hmax : τ ≤ τmax)
    (htx : G.spacetime.timeFunction x = T)
    (hty : G.spacetime.timeFunction y = T - τ)
    (hx : x ∈ range e.toSpacetime) (hy : y ∈ range e.toSpacetime) :
    M14ReducedLengthValue G T 0 τ x y =
      reducedLength F T (D.point_map x) (D.point_map y) τ := by
  have htx' : G.spacetime.timeFunction x = T - 0 := by simpa only [sub_zero] using htx
  unfold M14ReducedLengthValue M14ActionValue
  rw [ordinaryCapture_actionSet_transport D hCoordinates hmax hx hy htx' hty]
  simp only [reducedLength, dif_pos hτ]

theorem ordinaryCapture_minimizing_transport {τ₁ τ₂ : ℝ} {x y : G.Point}
    (hmax : τ₂ ≤ τmax) (hx : x ∈ range e.toSpacetime)
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (hc : ∀ s ∈ Icc τ₁ τ₂, p.curve s ∈ range e.toSpacetime) :
    M14IsMinimizing p ↔
      IsMinimizingBackwardLPath F T τ₁ τ₂ (D.path_map τ₁ τ₂ x y p hc) := by
  have hy : y ∈ range e.toSpacetime := by
    have h := hc τ₂ ⟨p.tau_lt.le, le_rfl⟩
    rwa [p.curve_end] at h
  constructor
  · intro hp q hq₁ hq₂
    obtain ⟨r, hr⟩ := ordinaryCapture_lift_action D hCoordinates hx hy
      p.base_time p.endpoint_time q
      (hq₁.trans (D.path_start_eq τ₁ τ₂ x y p hc))
      (hq₂.trans (D.path_end_eq τ₁ τ₂ x y p hc))
    rw [ordinaryCapture_action_transport D hCoordinates p hc, hr]
    exact hp r
  · intro hp r
    let hr := D.capture_from_start τ₁ τ₂ x y hmax hx r
    rw [← ordinaryCapture_action_transport D hCoordinates p hc,
      ← ordinaryCapture_action_transport D hCoordinates r hr]
    apply hp (D.path_map τ₁ τ₂ x y r hr)
    · exact (D.path_start_eq τ₁ τ₂ x y r hr).trans
        (D.path_start_eq τ₁ τ₂ x y p hc).symm
    · exact (D.path_end_eq τ₁ τ₂ x y r hr).trans
        (D.path_end_eq τ₁ τ₂ x y p hc).symm

end PoincareConjecture.M14
