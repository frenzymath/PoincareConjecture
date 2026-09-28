import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMinimizerSubsegments
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceEdgeMinimizerOverlap










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}




theorem successor_exit_sign_eq_one_of_minimizer
    (N Q : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000)
    (heq : Q.epsilon = N.epsilon)
    (hout : Q.center ∉ N.carrier)
    (hrecip : Q.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆
      N.region (-(0.2 : ℝ) * N.epsilon⁻¹) ((0.6 : ℝ) * N.epsilon⁻¹))
    {U : Set M} (hNU : N.carrier ⊆ U)
    {γ : ℝ → M} {a b tN tQ v σ : ℝ}
    (haN : a ≤ tN) (hNQ : tN < tQ) (hQv : tQ < v) (hvb : v ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hfinite : g.pathELength γ a b ≠ ⊤)
    (hmin : g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b))
    (hcN : γ tN = N.center) (hcQ : γ tQ = Q.center)
    (hvQ : γ v ∈ Q.carrier) (hσ : σ = 1 ∨ σ = -1)
    (hlevel : σ * (Q.coordinate_inverse (γ v)).2 = 509 * Q.epsilon⁻¹ / 512) :
    σ = 1 := by
  rcases hσ with hσ | rfl
  · exact hσ
  exfalso
  rw [heq] at hlevel
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hApos : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hA : (1000 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hε hApos.le
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
    linarith
  have hvband : γ v ∈ Q.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) := by
    refine ⟨hvQ, ?_, ?_⟩ <;> linarith only [hlevel, hApos]
  have hvN := hrecip hvband
  have hheight : |(N.coordinate_inverse (γ v)).2| ≤ (0.6 : ℝ) * N.epsilon⁻¹ := by
    apply abs_le.mpr
    constructor <;> linarith only [hvN.2.1, hvN.2.2, hApos]
  have hcNmem := N.central_sphere_subset N.center_on_central_sphere
  have hzero : (N.coordinate_inverse N.center).2 = 0 :=
    (N.mem_central_sphere_iff_of_mem_carrier hcNmem).mp N.center_on_central_sphere
  have hupper : intrinsicEDist g U N.center (γ v) ≤ ENNReal.ofReal
      (N.scale * Real.sqrt (1 + N.epsilon) *
        (|(N.coordinate_inverse (γ v)).2| + Real.sqrt 2 * (Real.pi + 1))) := by
    apply (intrinsicEDist_mono_of_subset (g := g) hNU).trans
    simpa only [hzero, sub_zero] using N.intrinsicEDist_le_axial_add hcNmem hvN.1
  have hroot : Real.sqrt (1 + N.epsilon) ≤ (1.001 : ℝ) := by
    have hsquare := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos])
    nlinarith only [hsquare, Real.sqrt_nonneg (1 + N.epsilon), hε]
  have hsqrt2 : Real.sqrt 2 ≤ (2 : ℝ) := by
    exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsphere : Real.sqrt 2 * (Real.pi + 1) ≤ (10 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hsqrt2 (by positivity : 0 ≤ Real.pi + 1)
    nlinarith only [h, Real.pi_le_four]
  have hcoefficient : Real.sqrt (1 + N.epsilon) *
      (|(N.coordinate_inverse (γ v)).2| + Real.sqrt 2 * (Real.pi + 1)) <
        (0.99 : ℝ) * N.epsilon⁻¹ := by
    calc
      _ ≤ (1.001 : ℝ) * ((0.6 : ℝ) * N.epsilon⁻¹ + 10) :=
        mul_le_mul hroot (add_le_add hheight hsphere) (by positivity) (by norm_num)
      _ < _ := by linarith only [hA]
  have hbudget : N.scale * Real.sqrt (1 + N.epsilon) *
      (|(N.coordinate_inverse (γ v)).2| + Real.sqrt 2 * (Real.pi + 1)) <
        (0.99 : ℝ) * N.scale * N.epsilon⁻¹ := by
    have h := mul_lt_mul_of_pos_left hcoefficient N.scale_pos
    nlinarith only [h]
  have hshort : intrinsicEDist g U N.center (γ v) <
      ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) :=
    hupper.trans_lt ((ENNReal.ofReal_lt_ofReal_iff
      (mul_pos (mul_pos (by norm_num) N.scale_pos) hApos)).mpr hbudget)
  have hfirst : ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      g.pathELength γ tN tQ := by
    apply (N.balanced_edist_lower_of_not_mem_carrier hε hout).trans
    exact Manifold.riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc haN (hQv.le.trans hvb))) hcN hcQ hNQ.le
  have hminimum := pathELength_eq_intrinsicEDist_subsegment g haN
    (hNQ.trans hQv).le hvb hγ hγU hfinite hmin
  rw [hcN] at hminimum
  have hlong : ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      g.pathELength γ tN v :=
    hfirst.trans (Manifold.pathELength_mono le_rfl hQv.le)
  rw [hminimum] at hlong
  exact (not_lt_of_ge hlong) hshort

end PoincareConjecture.M28
