import PoincareConjecture.Proofs.M34.Standard.CapIntrinsicDiameter
import PoincareConjecture.Proofs.M34.Standard.CapIntrinsicDiameterAxial
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceRecutDiffeomorph










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)



theorem recutCarrier_intrinsicDiameter_le_two {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹) :
    intrinsicDiameter g (N.recutCarrier b) ≤
      ENNReal.ofReal 2 * intrinsicDiameter g N.carrier := by
  let c := (-N.epsilon⁻¹ + b) / 2
  have hc : -N.epsilon⁻¹ < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  obtain ⟨e, he, he', houter, hfix, hderiv⟩ :=
    Real.exists_smooth_orderIso_compression hcb hb'
  let d := N.recutDiffeomorph hc hcb hb' e he he' houter hfix
  have hinner : e (-N.epsilon⁻¹) = -N.epsilon⁻¹ := hfix _ hc.le
  have hvalid (x : M) (hx : x ∈ N.end_neck.carrier) :
      e (N.end_neck.coordinate_inverse x).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    have ht : (N.end_neck.coordinate_inverse x).2 ∈
        Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      simpa only [N.end_neck_epsilon] using (N.end_neck.coordinate_inverse_mem x hx).2
    exact ⟨hinner ▸ e.strictMono ht.1, (houter ▸ e.strictMono ht.2).trans hb'⟩
  have habs (s : ℝ) : |deriv (e : ℝ → ℝ) s| ≤ 1 := by
    rw [abs_of_pos (hderiv s).1]
    exact (hderiv s).2
  have hbound : ∀ x ∈ d.source, ∀ v : TangentSpace (𝓡 3) x,
      g.tangentNorm (d x) (mfderiv (𝓡 3) (𝓡 3) d x v) ≤ 2 * g.tangentNorm x v := by
    intro x hx v
    exact N.axialMap_tangentNorm_le_two hc (hcb.trans hb') he hfix habs hvalid hx v
  have hdiam := g.intrinsicDiameter_image_le_mul_of_isOpen g d d.open_source
    (d.contMDiffOn_toFun.of_le (by exact_mod_cast le_top)) (by norm_num : (0 : ℝ) < 2) hbound
  rw [d.toPartialEquiv.image_source_eq_target] at hdiam
  exact hdiam

end PoincareConjecture.CapCertificate
