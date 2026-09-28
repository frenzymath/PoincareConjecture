import PoincareConjecture.Proofs.M47.LimitFiniteOriginalChart









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance finiteAnchorDualAdd : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteAnchorDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance finiteAnchorBilinAdd :
    NormedAddCommGroup V := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteAnchorBilinSpace :
    NormedSpace ℝ V := ContinuousLinearMap.toNormedSpace



theorem limitFinite_anchor_coefficients
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {H : GeneralizedRicciFlowData.{u}}
    {origin scale : ℝ} {I : Set ℝ} {A : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder H L.sliceCarrier origin scale I A) (hA : IsOpen A)
    (U : TopologicalSpace.Opens L.sliceCarrier.carrier) (q : U) (hUA : (U : Set _) ⊆ A)
    (t : ℝ) (ht : t ∈ I) (g : RiemannianMetric 3 U)
    (hmetric : ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = e.pullbackInner t ht x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → L.sliceCarrier.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → L.sliceCarrier.carrier) x w))
    {R : ℝ} (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞)
    (hsource : Φ.source = Metric.ball 0 R)
    (hmap : ∀ z ∈ Metric.ball 0 R,
      (Φ z).val = (extChartAt (𝓡 3) q.val).symm
        ((extChartAt (𝓡 3) q.val) q.val + z))
    {z : E} (hz : z ∈ Metric.ball 0 R)
    (htarget : (extChartAt (𝓡 3) q.val) q.val + z ∈ (extChartAt (𝓡 3) q.val).target) :
    g.pullbackCoefficients Φ z =
      ContinuousLinearMap.piLpBilinearFromCoordinates (p := 2) (q := 2) (𝕜 := ℝ)
        (fun a b : Fin 3 => blowupPullbackCoefficient e q.val a b
          (t, (extChartAt (𝓡 3) q.val) q.val + z)) := by
  have hmem : (extChartAt (𝓡 3) q.val).symm
      ((extChartAt (𝓡 3) q.val) q.val + z) ∈ A := by
    rw [← hmap z hz]
    exact hUA (Φ z).property
  rw [limitCanonical_round_reconstructed_eq_chartForm e hA q.val t ht _ htarget hmem]
  have hd := limitFinite_original_chart_differential U q Φ hsource hmap hz htarget
  have hslot (v : E) :
      mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → L.sliceCarrier.carrier) (Φ z)
          (mfderiv (𝓡 3) (𝓡 3) Φ z v) =
        mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q.val).symm
          ((extChartAt (𝓡 3) q.val) q.val + z) v := congrArg (fun B => B v) hd
  ext v w
  rw [limitNoncollapseChartForm_apply e hA q.val t ht _ htarget hmem]
  change g.inner (Φ z) (mfderiv (𝓡 3) (𝓡 3) Φ z v)
    (mfderiv (𝓡 3) (𝓡 3) Φ z w) = _
  rw [hmetric, hslot v, hslot w, hmap z hz]



theorem limitFinite_anchor_coefficient_jets
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {H : GeneralizedRicciFlowData.{u}}
    {origin scale : ℝ} {I : Set ℝ} {A : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder H L.sliceCarrier origin scale I A) (hA : IsOpen A)
    (U : TopologicalSpace.Opens L.sliceCarrier.carrier) (q : U) (hUA : (U : Set _) ⊆ A)
    (t : ℝ) (ht : t ∈ I) (g : RiemannianMetric 3 U)
    (hmetric : ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = e.pullbackInner t ht x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → L.sliceCarrier.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → L.sliceCarrier.carrier) x w))
    {R : ℝ} (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞)
    (hsource : Φ.source = Metric.ball 0 R)
    (hmap : ∀ z ∈ Metric.ball 0 R,
      (Φ z).val = (extChartAt (𝓡 3) q.val).symm
        ((extChartAt (𝓡 3) q.val) q.val + z))
    (htarget : ∀ z ∈ Metric.ball 0 R,
      (extChartAt (𝓡 3) q.val) q.val + z ∈ (extChartAt (𝓡 3) q.val).target)
    (m : ℕ) {z : E} (hz : z ∈ Metric.ball 0 R) :
    iteratedFDeriv ℝ m (g.pullbackCoefficients Φ) z =
      iteratedFDeriv ℝ m (fun y =>
        ContinuousLinearMap.piLpBilinearFromCoordinates (p := 2) (q := 2) (𝕜 := ℝ)
          (fun a b : Fin 3 => blowupPullbackCoefficient e q.val a b (t, y)))
        ((extChartAt (𝓡 3) q.val) q.val + z) := by
  have heq : g.pullbackCoefficients Φ =ᶠ[𝓝 z] (fun y =>
      ContinuousLinearMap.piLpBilinearFromCoordinates (p := 2) (q := 2) (𝕜 := ℝ)
        (fun a b : Fin 3 => blowupPullbackCoefficient e q.val a b
          (t, (extChartAt (𝓡 3) q.val) q.val + y))) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact limitFinite_anchor_coefficients e hA U q hUA t ht g hmetric Φ hsource hmap
      hy (htarget y hy)
  rw [(heq.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
  exact iteratedFDeriv_comp_add_left (𝕜 := ℝ)
    (f := fun y => ContinuousLinearMap.piLpBilinearFromCoordinates
      (p := 2) (q := 2) (𝕜 := ℝ)
      (fun a b : Fin 3 => blowupPullbackCoefficient e q.val a b (t, y)))
    m ((extChartAt (𝓡 3) q.val) q.val) z

end PoincareConjecture.M47
