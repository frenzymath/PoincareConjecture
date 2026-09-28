import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceEdgeCommonOrientation
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




theorem SourceEdgeCommonOrientationPacket.anchor_prefix_mem_and_not_mem_successor
    {N P W : EpsilonNeck g} {γ : ℝ → M} {tN tW : ℝ}
    (H : SourceEdgeCommonOrientationPacket N P W (γ := γ) tN tW)
    (hε : N.epsilon ≤ 1 / 1000) {U : Set M} (hWU : W.carrier ⊆ U)
    {a b t₁ : ℝ} (ha₁ : a ≤ t₁) (h₁N : t₁ < tN)
    (hNW : tN < tW) (hWb : tW ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hfinite : g.pathELength γ a b ≠ ⊤)
    (hmin : g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b))
    (hanchor : g.pathELength γ t₁ tN =
      ENNReal.ofReal ((0.3 : ℝ) * N.scale * N.epsilon⁻¹)) :
    MapsTo γ (Icc t₁ tN) N.carrier ∧ γ t₁ ∉ W.carrier := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hs : 0 < N.scale := N.scale_pos
  have hApos : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hA : (1000 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hε hApos.le
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
    linarith
  have hprefix : MapsTo γ (Icc t₁ tN) N.carrier := by
    intro t ht
    have hdist : g.edist N.center (γ t) ≤ g.pathELength γ t tN := by
      rw [← H.center_N]
      change Manifold.riemannianEDist (𝓡 3) (γ tN) (γ t) ≤ _
      rw [Manifold.riemannianEDist_comm]
      exact Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc (ha₁.trans ht.1) (hNW.le.trans hWb)))
        rfl rfl ht.2
    have hlen : g.pathELength γ t tN ≤
        ENNReal.ofReal ((0.3 : ℝ) * N.scale * N.epsilon⁻¹) := by
      rw [← hanchor]
      exact Manifold.pathELength_mono ht.1 le_rfl
    exact (mem_middle_slab_of_edist_center_le N hε (hdist.trans hlen)).1
  refine ⟨hprefix, ?_⟩
  intro hanchorW
  have hdistEdge : g.edist N.center W.center ≤ g.pathELength γ tN tW := by
    rw [← H.center_N, ← H.center_Q]
    exact Manifold.riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc (ha₁.trans h₁N.le) hWb)) rfl rfl hNW.le
  have hedge := H.center_distance.1.trans hdistEdge
  have hlower : ENNReal.ofReal
      ((0.3 : ℝ) * N.scale * N.epsilon⁻¹ +
        (0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      intrinsicEDist g U (γ t₁) W.center := by
    calc
      _ ≤ g.pathELength γ t₁ tW := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        exact (add_le_add hanchor.symm.le hedge).trans_eq
          (Manifold.pathELength_add h₁N.le hNW.le)
      _ = _ := by
        simpa only [H.center_Q] using pathELength_eq_intrinsicEDist_subsegment g
          ha₁ (h₁N.trans hNW).le hWb hγ hγU hfinite hmin
  have hcenter : W.center ∈ W.carrier :=
    W.central_sphere_subset W.center_on_central_sphere
  have hzero : (W.coordinate_inverse W.center).2 = 0 :=
    (W.mem_central_sphere_iff_of_mem_carrier hcenter).mp W.center_on_central_sphere
  have hupper := (intrinsicEDist_mono_of_subset (g := g) hWU).trans
    (W.intrinsicEDist_le_axial_add hanchorW hcenter)
  rw [hzero, zero_sub, abs_neg] at hupper
  have hheight : |(W.coordinate_inverse (γ t₁)).2| < N.epsilon⁻¹ := by
    simpa only [H.epsilon_eq] using
      (abs_lt.mpr (W.coordinate_inverse_mem (γ t₁) hanchorW).2)
  have hroot : Real.sqrt (1 + W.epsilon) ≤ (1.001 : ℝ) := by
    have hεW : W.epsilon ≤ 1 / 1000 := by simpa only [H.epsilon_eq] using hε
    have hsquare := Real.sq_sqrt (show 0 ≤ 1 + W.epsilon by
      linarith [W.epsilon_pos])
    nlinarith only [hsquare, Real.sqrt_nonneg (1 + W.epsilon), hεW]
  have hsqrt2 : Real.sqrt 2 ≤ (2 : ℝ) :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsphere : Real.sqrt 2 * (Real.pi + 1) ≤ (10 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hsqrt2
      (by positivity : 0 ≤ Real.pi + 1)
    nlinarith only [h, Real.pi_le_four]
  have hcoefficient : Real.sqrt (1 + W.epsilon) *
      (|(W.coordinate_inverse (γ t₁)).2| + Real.sqrt 2 * (Real.pi + 1)) ≤
      (1.001 : ℝ) * (N.epsilon⁻¹ + 10) :=
    mul_le_mul hroot (add_le_add hheight.le hsphere) (by positivity) (by norm_num)
  have hnumber : (1.001 : ℝ) * (1.001 * (N.epsilon⁻¹ + 10)) <
      (1.02 : ℝ) * N.epsilon⁻¹ := by linarith only [hA]
  have hbudget : W.scale * Real.sqrt (1 + W.epsilon) *
      (|(W.coordinate_inverse (γ t₁)).2| + Real.sqrt 2 * (Real.pi + 1)) <
      (0.3 : ℝ) * N.scale * N.epsilon⁻¹ +
        (0.99 : ℝ) * N.scale * N.epsilon⁻¹ := by
    calc
      _ = W.scale * (Real.sqrt (1 + W.epsilon) *
          (|(W.coordinate_inverse (γ t₁)).2| + Real.sqrt 2 * (Real.pi + 1))) :=
        by ring
      _ ≤ ((1.001 : ℝ) * N.scale) * (1.001 * (N.epsilon⁻¹ + 10)) :=
        mul_le_mul H.scale.2.le hcoefficient (by positivity) (by positivity)
      _ < (1.02 : ℝ) * N.scale * N.epsilon⁻¹ := by
        have h := mul_lt_mul_of_pos_left hnumber hs
        nlinarith only [h]
      _ < _ := by nlinarith only [mul_pos hs hApos]
  have hshort := hupper.trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hbudget)
  exact (not_lt_of_ge hlower) hshort

end PoincareConjecture.M28
