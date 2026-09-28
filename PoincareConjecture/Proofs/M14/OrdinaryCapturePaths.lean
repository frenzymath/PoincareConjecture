import PoincareConjecture.Statements.M14GeneralizedLGeometry










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

include D



theorem ordinaryCapture_point_reconstruct {q : G.Point}
    (hq : q ∈ range e.toSpacetime) (t : (G.timeIntervals.interval K).Point)
    (ht : G.spacetime.timeFunction q = t.val) :
    e.toSpacetime (t, D.point_map q) = q := by
  rcases hq with ⟨⟨s, c⟩, rfl⟩
  have hst : s = t := Subtype.ext ((e.time_eq (s, c)).symm.trans ht)
  rw [D.point_map_on_cylinder, hst]



theorem ordinaryCapture_point_injective {q r : G.Point}
    (hq : q ∈ range e.toSpacetime) (hr : r ∈ range e.toSpacetime)
    (ht : G.spacetime.timeFunction q = G.spacetime.timeFunction r)
    (hpoint : D.point_map q = D.point_map r) : q = r := by
  rcases hr with ⟨⟨t, c⟩, rfl⟩
  have hq' := ordinaryCapture_point_reconstruct D hq t (ht.trans (e.time_eq (t, c)))
  rw [hpoint, D.point_map_on_cylinder] at hq'
  exact hq'.symm



theorem ordinaryCapture_lift_with_endpoints {τ₁ τ₂ : ℝ} {x y : G.Point}
    (hx : x ∈ range e.toSpacetime) (hy : y ∈ range e.toSpacetime)
    (htx : G.spacetime.timeFunction x = T - τ₁)
    (hty : G.spacetime.timeFunction y = T - τ₂)
    (q : BackwardTimePath F T τ₁ τ₂)
    (hq₁ : q.curve τ₁ = D.point_map x) (hq₂ : q.curve τ₂ = D.point_map y) :
    ∃ p : M14BackwardPath G T τ₁ τ₂ x y, ∀ s (hs : s ∈ Icc τ₁ τ₂),
      e.toSpacetime (⟨T - s, q.time_mem s hs⟩, q.curve s) = p.curve s := by
  have hstart : e.toSpacetime
      (⟨T - τ₁, q.time_mem τ₁ ⟨le_rfl, q.ordered.le⟩⟩, q.curve τ₁) = x := by
    rw [hq₁]
    exact ordinaryCapture_point_reconstruct D hx _ htx
  have hend : e.toSpacetime
      (⟨T - τ₂, q.time_mem τ₂ ⟨q.ordered.le, le_rfl⟩⟩, q.curve τ₂) = y := by
    rw [hq₂]
    exact ordinaryCapture_point_reconstruct D hy _ hty
  cases hstart
  cases hend
  exact D.path_lift τ₁ τ₂ q



theorem ordinaryCapture_exists_mapped_lift {τ₁ τ₂ : ℝ} {x y : G.Point}
    (hx : x ∈ range e.toSpacetime) (hy : y ∈ range e.toSpacetime)
    (htx : G.spacetime.timeFunction x = T - τ₁)
    (hty : G.spacetime.timeFunction y = T - τ₂)
    (q : BackwardTimePath F T τ₁ τ₂)
    (hq₁ : q.curve τ₁ = D.point_map x) (hq₂ : q.curve τ₂ = D.point_map y) :
    ∃ p : M14BackwardPath G T τ₁ τ₂ x y,
      ∃ hc : ∀ s ∈ Icc τ₁ τ₂, p.curve s ∈ range e.toSpacetime,
        EqOn (D.path_map τ₁ τ₂ x y p hc).curve q.curve (Icc τ₁ τ₂) := by
  obtain ⟨p, hp⟩ := ordinaryCapture_lift_with_endpoints D hx hy htx hty q hq₁ hq₂
  have hc : ∀ s ∈ Icc τ₁ τ₂, p.curve s ∈ range e.toSpacetime :=
    fun s hs => ⟨(⟨T - s, q.time_mem s hs⟩, q.curve s), hp s hs⟩
  refine ⟨p, hc, ?_⟩
  intro s hs
  rw [← D.path_curve_eq τ₁ τ₂ x y p hc s hs, ← hp s hs,
    D.point_map_on_cylinder]



theorem ordinaryCapture_actionSet_eq {τ₁ τ₂ : ℝ} {x y : G.Point}
    (hmax : τ₂ ≤ τmax) (hx : x ∈ range e.toSpacetime) :
    M14ActionSet G T τ₁ τ₂ x y =
      {a | ∃ p : M14BackwardPath G T τ₁ τ₂ x y,
        (∀ s ∈ Icc τ₁ τ₂, p.curve s ∈ range e.toSpacetime) ∧
        M14BackwardLAction G p = a} := by
  ext a
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, D.capture_from_start τ₁ τ₂ x y hmax hx p, hp⟩
  · rintro ⟨p, _, hp⟩
    exact ⟨p, hp⟩



theorem ordinaryCapture_actionValue_eq {τ₁ τ₂ : ℝ} {x y : G.Point}
    (hmax : τ₂ ≤ τmax) (hx : x ∈ range e.toSpacetime) :
    M14ActionValue G T τ₁ τ₂ x y =
      sInf {a | ∃ p : M14BackwardPath G T τ₁ τ₂ x y,
        (∀ s ∈ Icc τ₁ τ₂, p.curve s ∈ range e.toSpacetime) ∧
        M14BackwardLAction G p = a} := by
  unfold M14ActionValue
  rw [ordinaryCapture_actionSet_eq D hmax hx]



theorem ordinaryCapture_endpoint_image {τ : ℝ} {x : G.Point}
    {E : M14ExponentialFamily G T x} (H : M14StableSet G T τ x E)
    (hmax : τ ≤ τmax) (hx : x ∈ range e.toSpacetime) :
    (fun q => q.val) '' (H.endpoint_slice_map '' H.carrier) ⊆ range e.toSpacetime := by
  rintro q ⟨r, ⟨Z, hZ, rfl⟩, rfl⟩
  obtain ⟨p, _, _, _⟩ := H.minimizing_path Z hZ
  have hp := D.capture_from_start 0 τ x (H.endpoint_map Z) hmax hx p τ
    ⟨H.tau_pos.le, le_rfl⟩
  rw [p.curve_end] at hp
  simpa only [H.endpoint_slice_map_val Z hZ] using hp

end PoincareConjecture.M14
