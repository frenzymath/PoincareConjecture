import PoincareLib.Geometry.RicciFlow.Blowup.Construction.Generalized.OrdinaryExtraction
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.Generalized.TerminalMetric
import PoincareLib.Geometry.RicciFlow.Compactness.GeometricLimit.BoundaryCoverage
import PoincareLib.Geometry.Riemannian.Compactness.IntrinsicMetric

/-!
# The actual ordinary source of a controlled cylinder

An open terminal ball is a connected pointed source. Its extracted ordinary
flow retains the supplied cylinder's full pullback metric, and its actual
terminal metric supplies the finite distance used for partial compactness.
Morgan--Tian Corollary 11.3 and Claim 11.5, pp. 269-270, with Theorem 5.6,
pp. 85-87. See the independently reviewed controlled-cylinder-source derivation.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareMT.M30

/-- The actual normalized terminal ball is open, including at nonpositive
radii (Corollary 11.3, p. 269). -/
theorem baseBall_isOpen (S : GeneralizedBlowupSequence.{u}) (k : ℕ) (R : ℝ) :
    IsOpen (S.baseBall k R) := by
  let C := (S.flow k).slice (S.base k).1
  let g : RiemannianMetric 3 C.carrier := (S.flow k).metric (S.base k).1
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : C.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : C.carrier → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace C.carrier := EMetricSpace.ofRiemannianMetric (𝓡 3) C.carrier
  change IsOpen {x : C.carrier |
    edist (S.base k).2 x < ENNReal.ofReal (R / Real.sqrt (S.scale k))}
  exact isOpen_lt (continuous_const.edist continuous_id) continuous_const

/-- Positive normalized terminal balls contain the designated basepoint and
are connected, without completeness of the slice (Theorem 5.6, pp. 85-87). -/
theorem baseBall_pointed_connected (S : GeneralizedBlowupSequence.{u}) (k : ℕ)
    {R : ℝ} (hR : 0 < R) :
    (S.base k).2 ∈ S.baseBall k R ∧ ConnectedSpace (S.baseBall k R) := by
  let C := (S.flow k).slice (S.base k).1
  let g : RiemannianMetric 3 C.carrier := (S.flow k).metric (S.base k).1
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : C.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hp : (S.base k).2 ∈ S.baseBall k R := by
    change g.edist (S.base k).2 (S.base k).2 <
      ENNReal.ofReal (R / Real.sqrt (S.scale k))
    have hself : g.edist (S.base k).2 (S.base k).2 = 0 :=
      Manifold.riemannianEDist_self
    rw [hself]
    exact ENNReal.ofReal_pos.mpr
      (div_pos hR (Real.sqrt_pos.mpr (S.base_scalar_pos k)))
  exact ⟨hp, Subtype.connectedSpace
    ⟨⟨(S.base k).2, hp⟩, g.isPreconnected_ball (S.base k).2 _⟩⟩

/-- A controlled cylinder supplies the actual ordinary flow on its terminal
ball, the exact terminal inclusion pullback, and the intrinsic distance
fields for partial compactness (Corollary 11.3 and Claim 11.5, pp. 269-270).
The source metric instance is constructed from this same flow. -/
theorem exists_controlled_ordinary_source
    {S : GeneralizedBlowupSequence.{u}} {k : ℕ} {R T B eta : ℝ}
    (E : ControlledBlowupCylinder S k R T B eta) (hR : 0 < R) (hT : 0 < T) :
    let C := (S.flow k).slice (S.base k).1
    let U : TopologicalSpace.Opens C.carrier := ⟨S.baseBall k R, baseBall_isOpen S k R⟩
    let gbar : RiemannianMetric 3 C.carrier :=
      M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
        (S.scale k) (S.base_scalar_pos k)
    ∃ G : RicciFlow 3 U (Icc (-T) 0),
      (∀ s (hs : s ∈ Icc (-T) 0) (x : U) (v w : TangentSpace (𝓡 3) x),
        (G.metric s).inner x v w = E.embedding.pullbackInner s hs x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w)) ∧
      (∀ (x : U) (v w : TangentSpace (𝓡 3) x),
        (G.metric 0).inner x v w = gbar.inner x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w)) ∧
      (letI : ConnectedSpace U := (baseBall_pointed_connected S k hR).2;
        letI : MetricSpace U := (G.metric 0).toMetricSpace;
        (∀ x y : U, edist x y = (G.metric 0).edist x y) ∧
          ∀ q : U, ∀ r : ℝ, IsPreconnected (Metric.ball q r)) := by
  let C := (S.flow k).slice (S.base k).1
  let U : TopologicalSpace.Opens C.carrier := ⟨S.baseBall k R, baseBall_isOpen S k R⟩
  let gbar : RiemannianMetric 3 C.carrier :=
    M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
      (S.scale k) (S.base_scalar_pos k)
  let : Nonempty C.carrier := ⟨(S.base k).2⟩
  let J : SpacetimeInterval := {
    domain := Icc (-T) 0
    ordConnected := ordConnected_Icc
    nontrivial := ⟨-T, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩,
      by linarith⟩ }
  let e : GeneralizedFlowCylinder (S.flow k) C (S.base k).1 (S.scale k) J.domain U :=
    E.embedding
  obtain ⟨G, hG⟩ := Cylinder.exists_ordinaryFlow e (Cylinder.physicalInterval_subset e)
  refine ⟨G, hG, ?_, ?_⟩
  · intro x v w
    have h₀ : (0 : ℝ) ∈ J.domain := ⟨by linarith, le_rfl⟩
    rw [hG 0 h₀ x v w,
      Cylinder.pullbackInner_zero_of_identity U.isOpen e h₀
        (E.zero_identity h₀) x.val x.property]
    rfl
  · let : ConnectedSpace U := (baseBall_pointed_connected S k hR).2
    let : MetricSpace U := (G.metric 0).toMetricSpace
    refine ⟨fun _ _ => rfl, ?_⟩
    intro q r
    rw [(G.metric 0).toMetricSpace_ball]
    exact (G.metric 0).isPreconnected_ball q r

end PoincareMT.M30
