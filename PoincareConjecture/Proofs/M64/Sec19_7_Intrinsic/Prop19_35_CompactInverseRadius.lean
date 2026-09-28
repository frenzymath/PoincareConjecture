import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PolarLiftRadiusDecrease





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture






theorem m64Intrinsic_compact_inverse_radius_decreases_left
    (N : IntrinsicAnnulus)
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    {e : AnnulusCoordinates → AnnulusCoordinates} (hFe : EqOn F e F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    {v : AnnulusCoordinates} (hv : v ∈ F.source) (he : DifferentiableAt ℝ e v)
    {beta : ℝ → AnnulusCoordinates} {s : ℝ} (hb : ContDiffAt ℝ ∞ beta s)
    (hend : beta s = e v)
    (hgauss : ∀ w : AnnulusCoordinates,
      N.metric.pullbackCoefficients e v v w = inner ℝ v w)
    (hangle : N.metric.cornerAngle (e v) (fderiv ℝ e v v) (deriv beta s) < Real.pi / 2) :
    ∀ᶠ b in 𝓝[<] s, ‖F.symm (beta b)‖ < ‖v‖ := by
  have ht : beta s ∈ F.target := by
    rw [hend, ← hFe hv]
    exact F.map_source hv
  let u : ℝ → AnnulusCoordinates := F.symm ∘ beta
  have huv : u s = v := by
    change F.symm (beta s) = v
    rw [hend, ← hFe hv, F.left_inv hv]
  have hu : ContDiffAt ℝ ∞ u s :=
    ((contMDiffOn_iff_contDiffOn.mp hFi).contDiffAt (F.open_target.mem_nhds ht)).comp s hb
  have hlift : (fun b => e (u b)) =ᶠ[𝓝 s] beta := by
    filter_upwards [hb.continuousAt.preimage_mem_nhds (F.open_target.mem_nhds ht)] with b hbF
    change e (F.symm (beta b)) = beta b
    rw [← hFe (F.map_target hbF), F.right_inv hbF]
  have he' : DifferentiableAt ℝ e (u s) := huv.symm ▸ he
  have hgauss' : ∀ w : AnnulusCoordinates,
      N.metric.pullbackCoefficients e (u s) (u s) w = inner ℝ (u s) w := by
    simpa only [huv] using hgauss
  have hangle' : N.metric.cornerAngle (e (u s))
      (fderiv ℝ e (u s) (u s)) (deriv beta s) < Real.pi / 2 := by
    have h := congrArg (fun x : AnnulusCoordinates => N.metric.cornerAngle (e x)
      (fderiv ℝ e x x : AnnulusCoordinates) (deriv beta s : AnnulusCoordinates)) huv
    exact h.trans_lt hangle
  have hshort := m64Intrinsic_polar_lift_radius_decreases_left N he'
    (hu.differentiableAt (by simp)).hasDerivAt
    (hb.differentiableAt (by simp)).hasDerivAt hlift hgauss' hangle'
  simpa only [huv, u, Function.comp_apply] using hshort

end PoincareConjecture
