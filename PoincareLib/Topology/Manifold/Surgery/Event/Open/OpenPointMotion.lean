import PoincareLib.Topology.Manifold.Surgery.Event.Local.LocalPointMotion
import PoincareLib.Topology.Manifold.Surgery.Event.Chart.ChartBall
import Mathlib.Topology.Connected.Clopen

/-!
# Actual point motions inside an open region

Compactly supported coordinate motions make each orbit open and closed
relative to the given region. A connected component therefore lies in
one orbit of actual smooth ambient diffeomorphisms fixing the exterior.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (A : GeneralizedSliceCarrier.{u}) (O : Set A.carrier)

/-- An actual smooth point motion whose ambient map fixes the whole exterior. -/
def PointMotionWithin (x y : A.carrier) : Prop :=
  ∃ e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞,
    e x = y ∧ ∀ z : A.carrier, z ∉ O → e z = z

/-- Identity provides the stationary motion, including every exterior point. -/
theorem pointMotionWithin_refl (x : A.carrier) : PointMotionWithin A O x x :=
  ⟨Diffeomorph.refl (𝓡 3) A.carrier ∞, rfl, fun _ _ => rfl⟩

variable {A O}

/-- The actual inverse of a motion fixes the same exterior. -/
theorem PointMotionWithin.symm {x y : A.carrier} (h : PointMotionWithin A O x y) :
    PointMotionWithin A O y x := by
  obtain ⟨e, hxy, hfix⟩ := h
  refine ⟨e.symm, ?_, ?_⟩
  · rw [← hxy, e.symm_apply_apply]
  · intro z hz
    apply e.injective
    change e (e.symm z) = e z
    rw [e.apply_symm_apply, hfix z hz]

/-- Composition retains the exterior identity and the exact point images. -/
theorem PointMotionWithin.trans {x y z : A.carrier}
    (hxy : PointMotionWithin A O x y) (hyz : PointMotionWithin A O y z) :
    PointMotionWithin A O x z := by
  obtain ⟨e, he, hefix⟩ := hxy
  obtain ⟨f, hf, hffix⟩ := hyz
  refine ⟨e.trans f, ?_, ?_⟩
  · change f (e x) = z
    rw [he, hf]
  · intro p hp
    change f (e p) = p
    rw [hefix p hp, hffix p hp]

/-- Fixing the exterior forces an actual diffeomorphism to preserve the region. -/
theorem PointMotionWithin.mem {x y : A.carrier}
    (hxy : PointMotionWithin A O x y) (hx : x ∈ O) : y ∈ O := by
  obtain ⟨e, he, hfix⟩ := hxy
  by_contra hy
  have h : y = x := e.injective ((hfix y hy).trans he.symm)
  exact hy (h.symm ▸ hx)

/-- A sufficiently small original chart image consists of actual reachable points. -/
theorem exists_pointMotionWithin_neighborhood (hO : IsOpen O)
    (p : A.carrier) (hp : p ∈ O) :
    ∃ V : Set A.carrier, IsOpen V ∧ p ∈ V ∧ V ⊆ O ∧
      ∀ q ∈ V, PointMotionWithin A O p q := by
  obtain ⟨B, hcenter, himage, _⟩ := exists_surgeryBall_in_open A p hO hp
  obtain ⟨r, hr, hmotion⟩ := exists_surgeryBallCenterMotion B
  let a : ℝ := min r 1
  have ha : 0 < a := lt_min hr (by norm_num)
  have ha2 : a ≤ 2 := (min_le_right r 1).trans (by norm_num)
  have hsmall : Metric.ball (0 : StandardCapSpace) a ⊆ Metric.ball 0 2 :=
    Metric.ball_subset_ball ha2
  have hopen : IsOpen (B.map '' Metric.ball 0 a) := by
    have h := B.open_embedding.isOpenMap
      (Subtype.val ⁻¹' Metric.ball 0 a)
      (Metric.isOpen_ball.preimage continuous_subtype_val)
    have heq : (fun z : Metric.ball (0 : StandardCapSpace) 2 => B.map z.val) ''
        (Subtype.val ⁻¹' Metric.ball 0 a) = B.map '' Metric.ball 0 a := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.val, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hsmall hz⟩, hz, rfl⟩
    rwa [heq] at h
  refine ⟨B.map '' Metric.ball 0 a, hopen, ?_,
    (Set.image_mono hsmall).trans himage, ?_⟩
  · rw [← hcenter]
    exact Set.mem_image_of_mem B.map (Metric.mem_ball_self ha)
  · rintro q ⟨v, hv, rfl⟩
    have hvnorm : ‖v‖ < r := by
      have hv' : ‖v‖ < a := by
        simpa only [Metric.mem_ball, dist_zero_right] using hv
      exact hv'.trans_le (min_le_left r 1)
    obtain ⟨e, he, hfix⟩ := hmotion v hvnorm
    refine ⟨e, ?_, fun z hz => hfix z (fun h => hz (himage h))⟩
    rwa [hcenter] at he

/-- Every actual-motion orbit is open relative to the original open region. -/
theorem pointMotionWithin_orbit_open (hO : IsOpen O) (x : A.carrier) :
    IsOpen {y : O | PointMotionWithin A O x y.val} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨V, hV, hyV, _, hmove⟩ :=
    exists_pointMotionWithin_neighborhood hO y.val y.property
  refine Filter.mem_of_superset
    ((hV.preimage (continuous_subtype_val : Continuous (Subtype.val : O → A.carrier))).mem_nhds
      hyV) ?_
  intro z hz
  exact hy.trans (hmove z.val hz)

/-- The complement is open by the same local motions and their actual inverses. -/
theorem pointMotionWithin_orbit_clopen (hO : IsOpen O) (x : A.carrier) :
    IsClopen {y : O | PointMotionWithin A O x y.val} := by
  refine ⟨isOpen_compl_iff.mp ?_, pointMotionWithin_orbit_open hO x⟩
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨V, hV, hyV, _, hmove⟩ :=
    exists_pointMotionWithin_neighborhood hO y.val y.property
  refine Filter.mem_of_superset
    ((hV.preimage (continuous_subtype_val : Continuous (Subtype.val : O → A.carrier))).mem_nhds
      hyV) ?_
  intro z hz hzreach
  exact hy (hzreach.trans (hmove z.val hz).symm)

/-- Points in the same actual component of an open region are related by a
smooth ambient diffeomorphism fixing every point outside that region. -/
theorem exists_diffeomorph_in_open_component (hO : IsOpen O)
    (x : A.carrier) (hx : x ∈ O) (y : A.carrier)
    (hy : y ∈ connectedComponentIn O x) :
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞,
      e x = y ∧ ∀ z : A.carrier, z ∉ O → e z = z := by
  rw [connectedComponentIn_eq_image hx] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  exact (pointMotionWithin_orbit_clopen hO x).connectedComponent_subset
    (pointMotionWithin_refl A O x) hq

/-- A connected open region supports the same actual motion between any two of its points. -/
theorem exists_diffeomorph_in_connected_open (hO : IsOpen O) (hconn : IsPreconnected O)
    (x : A.carrier) (hx : x ∈ O) (y : A.carrier) (hy : y ∈ O) :
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞,
      e x = y ∧ ∀ z : A.carrier, z ∉ O → e z = z :=
  exists_diffeomorph_in_open_component hO x hx y
    ((hconn.connectedComponentIn hx).symm ▸ hy)

end PoincareMT.M38
