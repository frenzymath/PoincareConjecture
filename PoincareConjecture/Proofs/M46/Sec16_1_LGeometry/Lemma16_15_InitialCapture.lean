import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_SafeExitEnergy
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_CylinderFirstExit









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Function
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12




theorem actualSafeCylinder_confines_initial_prefix
    {F : GeneralizedRicciFlowData.{u}} (G : FlowBoxRicciGeometry F)
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {C : GeneralizedSliceCarrier.{u}} [CompactSpace C.carrier]
    {origin scale : ℝ} {J : SpacetimeInterval}
    {U : TopologicalSpace.Opens C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale J.domain U)
    (hI : (cylinderPhysicalInterval origin scale e.scale_pos J).domain ⊆ F.interval)
    (gBirth : RiemannianMetric 3 C.carrier) {rho : ℝ} (hrho : 0 < rho)
    (hbound : ∀ (s : ℝ) (hs : s ∈ J.domain) (z : U)
      (v : TangentSpace (𝓡 3) z.val),
      scale * ((1 / 2 : ℝ) * gBirth.inner z.val v v) ≤ e.pullbackInner s hs z.val v v)
    (center : C.carrier) (hsource : (U : Set C.carrier) = gBirth.ball center (rho / 2))
    {T tau b : ℝ} {x y : G.toLGeometry.Point}
    (p : M14BackwardPath G.toLGeometry T 0 tau x y)
    (_hb : 0 < b) (hbtau : b ≤ Real.sqrt tau)
    (hclock : ∀ s ∈ Icc 0 b,
      G.realization.spacetime.timeFunction (p.curve (s ^ 2)) ∈
        (cylinderPhysicalInterval origin scale e.scale_pos J).domain)
    (z : (G.realization.timeIntervals.interval
      (cylinderPhysicalInterval origin scale e.scale_pos J)).Point × U)
    (hbase : p.curve 0 = rawCylinderMap G.realization e z) (hcenter : z.2.val = center)
    (hbudget : (∫ t in 0..tau, Real.sqrt t * pathPositiveDensity p t) < rho ^ 2 / (16 * b)) :
    MapsTo (fun s => p.curve (s ^ 2)) (Icc 0 b) (range (rawCylinderMap G.realization e)) := by
  have hcont : ContinuousOn (fun s => p.curve (s ^ 2)) (Icc 0 b) := by
    apply (M14.squarePath_continuousOn p).mono
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using Icc_subset_Icc le_rfl hbtau
  have hrelative : IsOpen {s : Icc (0 : ℝ) b |
      p.curve (s.val ^ 2) ∈ range (rawCylinderMap G.realization e)} :=
    rawCylinder_preimage_isOpen G.realization e hI (fun s : Icc (0 : ℝ) b =>
      p.curve (s.val ^ 2)) (continuousOn_iff_continuous_domRestrict.mp hcont)
      (fun s => hclock s.val s.property)
  have hstart : p.curve ((0 : ℝ) ^ 2) ∈ range (rawCylinderMap G.realization e) := by
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact ⟨z, hbase.symm⟩
  by_contra hnot
  have hleave : ∃ s ∈ Icc 0 b,
      p.curve (s ^ 2) ∉ range (rawCylinderMap G.realization e) := by
    simpa only [MapsTo, not_forall, Classical.not_imp, exists_prop] using hnot
  obtain ⟨d, hd, hdout, hinside, _⟩ :=
    exists_first_exit_of_relative_preimage hcont hrelative hstart hleave
  have hexit := actualSafeCylinder_exit_energy G hM12 e hI gBirth hrho hbound
    center hsource p hd.1 (hd.2.trans hbtau)
    (hinside.mono_left Ioo_subset_Ico_self) (hclock d ⟨hd.1.le, hd.2⟩) hdout z hbase hcenter
  have hden : rho ^ 2 / (16 * b) ≤ rho ^ 2 / (16 * d) := by
    exact div_le_div_of_nonneg_left (sq_nonneg rho) (mul_pos (by norm_num) hd.1)
      (mul_le_mul_of_nonneg_left hd.2 (by norm_num))
  exact (not_lt_of_ge (hden.trans hexit)) hbudget

end PoincareConjecture.Proofs.M46
