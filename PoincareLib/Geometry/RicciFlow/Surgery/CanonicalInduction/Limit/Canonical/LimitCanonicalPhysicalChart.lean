import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.R.LimitRP2Charts

/-!
# The actual physical charts for canonical transfer

The generalized convergence chart and the same source's regular history
retain their full maps, inverses and both metric slots. MT Proposition
17.1, pp. 407-408; limit-canonical-transfer.md, B.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

variable {G : GeneralizedRicciFlowData.{u}} {F : SurgeryFlowData.{u}}
  {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ}
  {I : Set ℝ} {U : Set C.carrier}

/-- The same actual spatial chart at its included physical clock.
MT Proposition 17.1, pp. 407-408. -/
noncomputable def limitCanonicalPhysicalChart
    (e : GeneralizedFlowCylinder G C origin scale I U) (hU : IsOpen U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier
      (F.slice (origin + s / scale)).carrier ∞ :=
  (limitRP2CylinderSliceChart e hU s hs).trans
    (limitRP2HistorySliceChart R (origin + s / scale) ht)

/-- The history chart has full source, so composition loses no points.
MT Proposition 17.1, pp. 407-408. -/
theorem limitCanonicalPhysicalChart_source
    (e : GeneralizedFlowCylinder G C origin scale I U) (hU : IsOpen U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval) :
    (limitCanonicalPhysicalChart e hU R s hs ht).source = U := by
  change U ∩ (e.forward s hs) ⁻¹' univ = U
  simp

/-- Its target is exactly the image of the entire original source.
MT Proposition 17.1, pp. 407-408. -/
theorem limitCanonicalPhysicalChart_target
    (e : GeneralizedFlowCylinder G C origin scale I U) (hU : IsOpen U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval) :
    (limitCanonicalPhysicalChart e hU R s hs ht).target =
      limitRP2PhysicalMap e R s hs ht '' U := by
  have h := (limitCanonicalPhysicalChart e hU R s hs ht).toPartialEquiv.image_source_eq_target
  rw [limitCanonicalPhysicalChart_source] at h
  exact h.symm

/-- The literal derivative composition preserves both normalized slots.
MT Proposition 17.1, pp. 407-408. -/
theorem limitCanonicalPhysicalChart_metric
    (e : GeneralizedFlowCylinder G C origin scale I U) (hU : IsOpen U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval) {x : C.carrier} (hx : x ∈ U)
    (v w : TangentSpace (𝓡 3) x) :
    scale * (F.metric (origin + s / scale)).inner
        (limitCanonicalPhysicalChart e hU R s hs ht x)
        (mfderiv (𝓡 3) (𝓡 3) (limitCanonicalPhysicalChart e hU R s hs ht) x v)
        (mfderiv (𝓡 3) (𝓡 3) (limitCanonicalPhysicalChart e hU R s hs ht) x w) =
      e.pullbackInner s hs x v w := by
  have he := ((e.forward_smooth s hs).contMDiffAt
    (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hR := (R.forward_smooth (origin + s / scale) ht).mdifferentiableAt
    (x := e.forward s hs x) (by simp)
  have hchain := mfderiv_comp x hR he
  change scale * (F.metric _).inner (R.forward _ ht (e.forward s hs x))
      (mfderiv (𝓡 3) (𝓡 3) (R.forward _ ht ∘ e.forward s hs) x v)
      (mfderiv (𝓡 3) (𝓡 3) (R.forward _ ht ∘ e.forward s hs) x w) = _
  rw [hchain]
  exact congrArg (scale * ·) (R.metric_pullback _ ht (e.forward s hs x)
    (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
    (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x w))

/-- A based generalized spacetime identity gives the same physical point,
including its dependent clock. MT Proposition 17.1, pp. 407-408. -/
theorem limitCanonicalPhysicalChart_point_identity
    (e : GeneralizedFlowCylinder G C origin scale I U) (hU : IsOpen U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval) (x : C.carrier)
    (q : G.point) (hq : q.1 ∈ G.interval) (hbase : e.pointMap s hs x = q) :
    (⟨origin + s / scale, limitCanonicalPhysicalChart e hU R s hs ht x⟩ :
        (t : ℝ) × (F.slice t).carrier) =
      ⟨q.1, R.forward q.1 hq q.2⟩ := by
  have heq : (⟨e.pointMap s hs x, ht⟩ : {p : G.point // p.1 ∈ G.interval}) =
      ⟨q, hq⟩ := Subtype.ext hbase
  exact congrArg (fun p : {p : G.point // p.1 ∈ G.interval} =>
    (⟨p.val.1, R.forward p.val.1 p.property p.val.2⟩ :
      (t : ℝ) × (F.slice t).carrier)) heq

end PoincareMT.M47
