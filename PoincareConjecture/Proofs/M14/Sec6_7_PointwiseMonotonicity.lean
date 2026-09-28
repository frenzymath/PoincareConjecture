import PoincareConjecture.Proofs.M14.Sec6_7_WeightedDensity
import PoincareConjecture.Proofs.M14.Mathlib.WeightedJacobian
import PoincareConjecture.Proofs.M14.Sec6_7_ExponentialJacobian
import PoincareConjecture.Proofs.M14.Sec6_5_RegularStableEndpoint
import PoincareConjecture.Proofs.M14.Sec6_3_StrictPrefix

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem exponentialWeightedJacobian_differentiableAt_and_deriv_nonpos
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (v : Module.Basis (Fin n) ℝ (G.Horizontal x))
    {Z : G.Horizontal x} {s b : ℝ} (hb : (Z, b) ∈ E.domain)
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) (hlt : s < b)
    (hz : (Z, s) ∈ M14JointDomain G E) :
    DifferentiableAt ℝ (exponentialWeightedJacobian E v Z) s ∧
      deriv (exponentialWeightedJacobian E v Z) s ≤ 0 := by
  have hnhds : {r | (Z, r) ∈ E.domain} ∈ 𝓝 s := by
    apply mem_of_superset (isOpen_Ioo.mem_nhds ⟨hpos, hlt⟩)
    intro r hr
    exact (E.maximal_lifetime Z).out (E.domain_zero Z) hb ⟨hr.1.le, hr.2.le⟩
  have ha := (exponential_reducedLength_hasDerivWithinAt hM12 E hs hpos).hasDerivAt hnhds
  have hJ := exponentialJacobian_hasDerivAt hCoordinates hM04 hM12 E v hb hs hpos hlt hz
  have hp := regular_square_endpoint E hs hpos
  have hq : G.spacetime.timeFunction ((E.square_path Z s hs hpos).curve s) = T - s ^ 2 := by
    rw [hp]
    exact E.clock Z s hs
  have hqeq : (⟨(E.square_path Z s hs hpos).curve s, hq⟩ : (G.slices (T - s ^ 2)).Point) =
      ⟨E.gamma Z s, E.clock Z s hs⟩ := Subtype.ext hp
  have hL := reducedLengthLaplacian_joint_bound hCoordinates hM04 hM12 E hs hpos hz hp hq
  rw [hqeq, hp, Real.sqrt_sq hpos.le] at hL
  have hden : 2 * s ^ 2 * s = 2 * s ^ 3 := by ring
  rw [hden] at hL
  exact ⟨(squareWeightedJacobian_hasDerivAt hpos ha hJ).differentiableAt,
    squareWeightedJacobian_deriv_nonpos hpos ha hJ (exponentialJacobian_nonneg E v Z s) hL⟩

theorem exponentialWeightedJacobian_antitoneOn
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (v : Module.Basis (Fin n) ℝ (G.Horizontal x))
    {τ : ℝ} (H : M14StableSet G T τ x E) {Z : G.Horizontal x} (hZ : Z ∈ H.carrier) :
    AntitoneOn (exponentialWeightedJacobian E v Z) (Ioc 0 (Real.sqrt τ)) := by
  have hb := H.survivor Z hZ
  have hregular (s : ℝ) (hs : s ∈ Ioo 0 (Real.sqrt τ)) :=
    exponentialWeightedJacobian_differentiableAt_and_deriv_nonpos hCoordinates hM04 hM12 E v hb
      ((E.maximal_lifetime Z).out (E.domain_zero Z) hb ⟨hs.1.le, hs.2.le⟩) hs.1 hs.2
      (mem_jointDomain_of_stable_extension hCoordinates hM04 hM12 E H hZ hs)
  apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 (Real.sqrt τ))
    (exponentialWeightedJacobian_continuousOn hM04 hM12 E v hb (Real.sqrt_pos.mpr H.tau_pos))
  · intro s hs
    rw [interior_Ioc] at hs
    exact (hregular s hs).1.differentiableWithinAt
  · intro s hs
    rw [interior_Ioc] at hs
    exact (hregular s hs).2

end PoincareConjecture.M14
