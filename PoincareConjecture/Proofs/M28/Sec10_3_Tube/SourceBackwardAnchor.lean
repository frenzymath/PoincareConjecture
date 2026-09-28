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




theorem backward_anchor_height_le_of_positive_transition
    (N : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000)
    {U : Set M} (hNU : N.carrier ⊆ U)
    {γ : ℝ → M} {a b t₁ tN v : ℝ}
    (ha₁ : a ≤ t₁) (h₁ : t₁ < tN) (hNv : tN < v) (hvb : v ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hfinite : g.pathELength γ a b ≠ ⊤)
    (hmin : g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b))
    (hcN : γ tN = N.center)
    (hγN : MapsTo γ (Icc tN v) N.carrier)
    (hlevel : (N.coordinate_inverse (γ v)).2 =
      (509 : ℝ) * N.epsilon⁻¹ / 512)
    (hanchor : g.pathELength γ t₁ tN =
      ENNReal.ofReal ((0.3 : ℝ) * N.scale * N.epsilon⁻¹)) :
    γ t₁ ∈ N.carrier ∧
      (N.coordinate_inverse (γ t₁)).2 ≤ -(0.292 : ℝ) * N.epsilon⁻¹ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hscale : 0 < N.scale := N.scale_pos
  have hApos : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hA : (1000 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hε hApos.le
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
    linarith
  have hdist : g.edist N.center (γ t₁) ≤ g.pathELength γ t₁ tN := by
    rw [← hcN]
    change Manifold.riemannianEDist (𝓡 3) (γ tN) (γ t₁) ≤ _
    rw [Manifold.riemannianEDist_comm]
    exact Manifold.riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc ha₁ (hNv.le.trans hvb))) rfl rfl h₁.le
  rw [hanchor] at hdist
  have hslab := mem_middle_slab_of_edist_center_le N hε hdist
  have hanchorMin : ENNReal.ofReal ((0.3 : ℝ) * N.scale * N.epsilon⁻¹) =
      intrinsicEDist g U (γ t₁) N.center := by
    calc
      _ = g.pathELength γ t₁ tN := hanchor.symm
      _ = intrinsicEDist g U (γ t₁) N.center := by
        simpa only [hcN] using pathELength_eq_intrinsicEDist_subsegment g
          ha₁ h₁.le (hNv.le.trans hvb) hγ hγU hfinite hmin
  have hheight : (0.292 : ℝ) * N.epsilon⁻¹ ≤
      |(N.coordinate_inverse (γ t₁)).2| := by
    apply anchor_height_lower N hε hA hNU hslab.1
    rw [intrinsicEDist_comm_set]
    exact hanchorMin.le
  have hnegative : (N.coordinate_inverse (γ t₁)).2 < 0 := by
    by_contra hnot
    have hpos : 0 ≤ (N.coordinate_inverse (γ t₁)).2 := le_of_not_gt hnot
    have hgap : |(N.coordinate_inverse (γ v)).2 -
        (N.coordinate_inverse (γ t₁)).2| ≤ (509 : ℝ) * N.epsilon⁻¹ / 512 := by
      rw [hlevel, abs_of_nonneg (by nlinarith only [hslab.2.2, hApos])]
      linarith only [hpos]
    have hupper : intrinsicEDist g U (γ t₁) (γ v) ≤ ENNReal.ofReal
        (N.scale * Real.sqrt (1 + N.epsilon) *
          (|(N.coordinate_inverse (γ v)).2 - (N.coordinate_inverse (γ t₁)).2| +
            Real.sqrt 2 * (Real.pi + 1))) := by
      apply (intrinsicEDist_mono_of_subset (g := g) hNU).trans
      exact N.intrinsicEDist_le_axial_add hslab.1 (hγN ⟨hNv.le, le_rfl⟩)
    have hrootUpper : Real.sqrt (1 + N.epsilon) ≤ (1.001 : ℝ) := by
      have hsquare := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by
        linarith [N.epsilon_pos])
      nlinarith only [hsquare, Real.sqrt_nonneg (1 + N.epsilon), hε]
    have hsqrt2 : Real.sqrt 2 ≤ (2 : ℝ) :=
      (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
    have hsphere : Real.sqrt 2 * (Real.pi + 1) ≤ (10 : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hsqrt2
        (by positivity : 0 ≤ Real.pi + 1)
      nlinarith only [h, Real.pi_le_four]
    have hcoefficient : Real.sqrt (1 + N.epsilon) *
        (|(N.coordinate_inverse (γ v)).2 - (N.coordinate_inverse (γ t₁)).2| +
          Real.sqrt 2 * (Real.pi + 1)) <
        (0.3 : ℝ) * N.epsilon⁻¹ + (0.999 : ℝ) *
          ((509 : ℝ) * N.epsilon⁻¹ / 512) := by
      calc
        _ ≤ (1.001 : ℝ) * ((509 : ℝ) * N.epsilon⁻¹ / 512 + 10) :=
          mul_le_mul hrootUpper (add_le_add hgap hsphere) (by positivity) (by norm_num)
        _ < _ := by linarith only [hA]
    have hbudget : N.scale * Real.sqrt (1 + N.epsilon) *
        (|(N.coordinate_inverse (γ v)).2 - (N.coordinate_inverse (γ t₁)).2| +
          Real.sqrt 2 * (Real.pi + 1)) <
        (0.3 : ℝ) * N.scale * N.epsilon⁻¹ +
          N.scale * (0.999 : ℝ) * ((509 : ℝ) * N.epsilon⁻¹ / 512) := by
      have h := mul_lt_mul_of_pos_left hcoefficient hscale
      nlinarith only [h]
    have hshort : intrinsicEDist g U (γ t₁) (γ v) < ENNReal.ofReal
        ((0.3 : ℝ) * N.scale * N.epsilon⁻¹ +
          N.scale * (0.999 : ℝ) * ((509 : ℝ) * N.epsilon⁻¹ / 512)) :=
      hupper.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hbudget)
    have hrootLower : (0.999 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith only [hε]
    have hzero : (N.coordinate_inverse N.center).2 = 0 :=
      (N.mem_central_sphere_iff_of_mem_carrier
        (N.central_sphere_subset N.center_on_central_sphere)).mp
        N.center_on_central_sphere
    have hdisp := N.path_axial_displacement_le_sharp hNv.le
      (hγ.mono (Icc_subset_Icc (ha₁.trans h₁.le) hvb)) hγN
    rw [hcN, hzero, sub_zero, hlevel, abs_of_pos (by positivity)] at hdisp
    have hdispLower : ENNReal.ofReal
        (N.scale * (0.999 : ℝ) * ((509 : ℝ) * N.epsilon⁻¹ / 512)) ≤
        g.pathELength γ tN v := by
      apply le_trans (ENNReal.ofReal_le_ofReal ?_) hdisp
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrootLower hscale.le) (by positivity)
    have hprefixLower : ENNReal.ofReal
        ((0.3 : ℝ) * N.scale * N.epsilon⁻¹ +
          N.scale * (0.999 : ℝ) * ((509 : ℝ) * N.epsilon⁻¹ / 512)) ≤
        g.pathELength γ t₁ v := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      exact (add_le_add hanchor.symm.le hdispLower).trans_eq
        (Manifold.pathELength_add h₁.le hNv.le)
    have hminimum := pathELength_eq_intrinsicEDist_subsegment g ha₁
      (h₁.trans hNv).le hvb hγ hγU hfinite hmin
    rw [hminimum] at hprefixLower
    exact (not_lt_of_ge hprefixLower) hshort
  refine ⟨hslab.1, ?_⟩
  rw [abs_of_neg hnegative] at hheight
  linarith only [hheight]

end PoincareConjecture.M28
