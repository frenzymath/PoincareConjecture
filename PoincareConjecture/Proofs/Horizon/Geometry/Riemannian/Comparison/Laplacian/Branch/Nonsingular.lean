import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.RadialJacobi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.JacobiUnique
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Reversal
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Radial.Differential










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

open ConnectionAlongCurve ConnectionVariation LaplacianComparison

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [T2Space M] in
private theorem tangentNorm_smul (g : RiemannianMetric n M) (p : M)
    (v : TangentSpace (𝓡 n) p) (c : ℝ) :
    g.tangentNorm p (c • v) = |c| * g.tangentNorm p v := by
  simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

omit [T2Space M] in
private theorem curvature_smul_velocity (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (x : M) (u v : TangentSpace (𝓡 n) x) (a : ℝ) :
    D.curvature x u (a • v) (a • v) = a ^ 2 • D.curvature x u v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro w
  change D.curvatureTensor x u (a • v) w (a • v) =
    inner ℝ (a ^ 2 • D.curvature x u v v) w
  rw [real_inner_smul_left]
  change D.curvatureTensor x u (a • v) w (a • v) =
    a ^ 2 * D.curvatureTensor x u v w v
  rw [D.curvatureTensor_smul_second, D.curvatureTensor_smul_last]
  ring



theorem isInvertible_mfderiv_of_minimizing_backward_extension
    (g : RiemannianMetric n M) (D : LeviCivitaData g) {R : ℝ}
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hinit : (mfderiv (𝓡 n) (𝓡 n) e 0).IsInvertible)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Metric.ball 0 R})
    (hspeed : ∀ v ∈ Metric.ball 0 R, ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (s • v)) t 1) = ‖v‖)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R) (hv0 : v ≠ 0)
    (hmin : g.edist (e ((-1 / 3 : ℝ) • v)) (e v) =
      ENNReal.ofReal ((4 / 3 : ℝ) * ‖v‖)) :
    (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible := by
  apply isInvertible_mfderiv_of_injective
  apply (injective_iff_map_eq_zero _).mpr
  change ∀ w : EuclideanSpace ℝ (Fin n), mfderiv (𝓡 n) (𝓡 n) e v w = 0 → w = 0
  intro w hw
  by_contra hw0
  have hvR : ‖v‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  have hR : 0 < R := (norm_nonneg v).trans_lt hvR
  have hezero : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e 0 :=
    he.contMDiffAt (Metric.isOpen_ball.mem_nhds (by simpa using hR))
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt (sub_pos.mpr hvR) ‖v‖
  let I₀ := Ioo (-(1 + δ)) (1 + δ)
  let q : ℝ → M := fun t => e (t • v)
  let J₀ : (t : ℝ) → TangentSpace (𝓡 n) (q t) :=
    fun t => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (t • (v + s • w))) 0 1
  have hdom : ∀ t ∈ I₀, t • v ∈ Metric.ball 0 R := by
    intro t ht
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    have htime : |t| ≤ 1 + δ := (abs_lt.mpr ht).le
    have hmul := mul_le_mul_of_nonneg_right htime (norm_nonneg v)
    nlinarith
  have hI₀ : IsOpen I₀ := isOpen_Ioo
  have hqgeo : g.IsGeodesicOn q I₀ := fun t ht => hgeo v hv t (hdom t ht)
  have hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I₀ := by
    apply he.comp
    · apply contMDiffOn_iff_contDiffOn.mpr
      fun_prop
    · exact hdom
  have hJ₀ : ∀ t ∈ I₀, ContDiffAt ℝ ∞ (chartField q (q t) J₀) t := by
    intro t ht
    exact contDiffAt_chartField_radialVariation v w
      (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (hdom t ht))) (mem_extChartAt_source _)
  have hjac₀ : ∀ t ∈ I₀,
      manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J₀ 1) 1 t =
        -D.curvature (q t) (J₀ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) := by
    intro t ht
    exact eq_neg_of_add_eq_zero_left
      (g.radialVariation_jacobi_on_domain D he hgeo hv w (hdom t ht))
  have hzero : (0 : ℝ) ∈ I₀ := by constructor <;> linarith
  have hDJzero : manifoldCovDerivAlong g q J₀ 1 0 ≠ 0 := by
    rw [g.radialVariation_initial_covariantDerivative hezero v w]
    intro hzero
    apply hw0
    apply hinit.injective
    simpa only [map_zero] using hzero
  let f : ℝ → ℝ := fun t => (4 / 3) * t + (-1 / 3)
  let γ := q ∘ f
  let J : (t : ℝ) → TangentSpace (𝓡 n) (γ t) := fun t => J₀ (f t)
  let I := f ⁻¹' I₀
  have hf : ContDiff ℝ ∞ f := by dsimp [f]; fun_prop
  have hI : IsOpen I := hI₀.preimage hf.continuous
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I :=
    hq.comp hf.contMDiff.contMDiffOn (fun _ ht => ht)
  have hγgeo : g.IsGeodesicOn γ I := hqgeo.comp_affine (4 / 3) (-1 / 3)
  have hsub : Icc (-δ / 4) (1 + δ / 4) ⊆ I := by
    intro t ht
    change f t ∈ I₀
    dsimp [f, I₀]
    constructor <;> linarith [ht.1, ht.2]
  have h01 : Icc (0 : ℝ) 1 ⊆ I := by
    intro t ht
    apply hsub
    constructor <;> linarith [ht.1, ht.2]
  have hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) J) t := by
    intro t ht
    exact (hJ₀ (f t) ht).comp t hf.contDiffAt
  have hjac : ∀ t ∈ Icc (0 : ℝ) 1,
      manifoldCovDerivAlong g γ (manifoldCovDerivAlong g γ J 1) 1 t =
        -D.curvature (γ t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) := by
    intro t ht
    have hqt := hq.contMDiffAt (hI₀.mem_nhds (h01 ht))
    dsimp only [γ, J, Function.comp_def, f]
    rw [manifoldCovDerivAlong_twice_comp_affine g hI₀ hq hJ₀ (h01 ht),
      hjac₀ _ (h01 ht), mfderiv_comp_affine_apply_one hqt]
    rw [curvature_smul_velocity, smul_neg]
  have hJ1 : J 1 = 0 := by
    change J₀ ((4 / 3) * 1 + (-1 / 3)) = 0
    rw [show (4 / 3 : ℝ) * 1 + (-1 / 3) = 1 by ring]
    exact (radialVariation_field_one v w
      ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)).mdifferentiableAt (by simp))).trans hw
  have hJquarter : J (1 / 4) = 0 := by
    change J₀ ((4 / 3) * (1 / 4) + (-1 / 3)) = 0
    rw [show (4 / 3 : ℝ) * (1 / 4) + (-1 / 3) = 0 by ring]
    exact radialVariation_field_zero e v w
  have hDJquarter : manifoldCovDerivAlong g γ J 1 (1 / 4) ≠ 0 := by
    have heq : (4 / 3 : ℝ) * (1 / 4) + (-1 / 3) = 0 := by ring
    have hd := manifoldCovDerivAlong_comp_affine g (a := 4 / 3) (b := -1 / 3)
      (t := 1 / 4) (by rw [heq]; exact hq.contMDiffAt (hI₀.mem_nhds hzero))
      (by rw [heq]; exact (hJ₀ 0 hzero).differentiableAt (by simp))
    dsimp only [γ, J, Function.comp_def, f]
    rw [hd, heq]
    exact smul_ne_zero (by norm_num : (4 / 3 : ℝ) ≠ 0) hDJzero
  have hDJ1 := jacobi_terminal_deriv_ne_zero D (a := -δ / 4) (b := 1 + δ / 4)
    (by linarith) (by linarith) (by norm_num : (1 / 4 : ℝ) ∈ Icc 0 1)
    hI hγ hsub hJ hjac hJ1 hDJquarter
  obtain ⟨C, hC⟩ := hqgeo.exists_constant_tangentNorm
    (by linarith : -(1 + δ) < 1 + δ)
  have hCnorm : (C : ℝ) = ‖v‖ :=
    (hC 0 hzero).symm.trans (hspeed v hv 0 (by simp))
  have hγspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = (4 / 3) * ‖v‖ := by
    intro t ht
    have hqt := hq.contMDiffAt (hI₀.mem_nhds (h01 ht))
    dsimp only [γ, Function.comp_def, f]
    rw [mfderiv_comp_affine_apply_one hqt, tangentNorm_smul,
      abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3), hC _ (h01 ht), hCnorm]
  have hn := jacobi_ne_zero_of_minimizing_terminal g D
    (a := -δ / 4) (b := 1 + δ / 4) (c := 1 / 4)
    (by linarith) (by linarith) (by norm_num) hI hγ hγgeo hsub hJ hjac hJ1 hDJ1
    (mul_pos (by norm_num) (norm_pos_iff.mpr hv0)) hγspeed
    (by simpa [γ, q, f, show (4 / 3 : ℝ) + -1 / 3 = 1 by ring] using hmin)
  exact hn hJquarter

end PoincareConjecture.RiemannianMetric
