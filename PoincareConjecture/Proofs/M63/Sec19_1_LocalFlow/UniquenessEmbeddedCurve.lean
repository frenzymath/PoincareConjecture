import PoincareConjecture.Definitions.M63Ramp
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι





theorem c2ShrinkingCurve_embedded_closed_data
    {F : RicciFlow n M (Icc a b)} {c : ℝ → ℝ → M} {J : Set ℝ}
    (hc : M63C2ShrinkingCurveOn F c J) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e) :
    (∀ t ∈ J, ContDiff ℝ 2 (fun x => e (c x t))) ∧
    (∀ t ∈ J, ∀ x, HasDerivAt (fun y => e (c y t))
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t)
        (curveVelocity (n := n) (fun y => c y t) x) : W) x) ∧
    ContinuousOn (fun z : ℝ × ℝ => e (c z.1 z.2)) (univ ×ˢ J) ∧
    ContinuousOn (fun z : ℝ × ℝ => deriv (fun y => e (c y z.2)) z.1)
      (univ ×ˢ J) ∧
    ContinuousOn (fun z : ℝ × ℝ =>
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c z.1 z.2)
        (m62CurvatureVector F c z.2 z.1) : W)) (univ ×ˢ J) := by
  have hspace (t : ℝ) (ht : t ∈ J) : ContDiff ℝ 2 (fun x => e (c x t)) :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp
      (hc.spatial_regular t ht)).contDiff
  have hderiv (t : ℝ) (ht : t ∈ J) (x : ℝ) : HasDerivAt (fun y => e (c y t))
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t)
        (curveVelocity (n := n) (fun y => c y t) x) : W) x := by
    have hchain : fderiv ℝ (fun y => e (c y t)) x =
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t)).comp
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun y => c y t) x) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp x (he.mdifferentiable (by simp)).mdifferentiableAt
        ((hc.spatial_regular t ht x).mdifferentiableAt (by norm_num))
    have hd := ((hspace t ht).differentiable (by norm_num) x).hasDerivAt
    have heq := congrArg (fun L : ℝ →L[ℝ] W => L 1) hchain
    exact hd.congr_deriv heq
  have hpush : Continuous (fun p : TangentBundle (𝓡 n) M =>
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e p.1 p.2 : W)) :=
    (contMDiff_snd_tangentBundle_modelSpace (n := ∞) W 𝓘(ℝ, W)).continuous.comp
      (he.continuous_tangentMap (by simp))
  refine ⟨hspace, hderiv, he.continuous.comp_continuousOn hc.continuous, ?_, ?_⟩
  · exact (hpush.comp_continuousOn hc.velocity_continuous).congr
      (fun z hz => (hderiv z.2 hz.2 z.1).deriv)
  · exact hpush.comp_continuousOn hc.curvature_continuous




theorem c2ShrinkingCurve_embedded_interior_equation
    {F : RicciFlow n M (Icc a b)} {c : ℝ → ℝ → M} {J : Set ℝ}
    (hc : M63C2ShrinkingCurveOn F c J) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e) :
    ContDiffOn ℝ 1 (fun z : ℝ × ℝ => e (c z.1 z.2)) (univ ×ˢ interior J) ∧
    ∀ t ∈ interior J, ∀ x, HasDerivAt (fun s => e (c x s))
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x) : W) t := by
  have hC1 : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => e (c z.1 z.2))
      (univ ×ˢ interior J) :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).comp_contMDiffOn
      hc.joint_c1).contDiffOn
  refine ⟨hC1, ?_⟩
  intro t ht x
  have hmem : (x, t) ∈ univ ×ˢ interior J := ⟨mem_univ _, ht⟩
  have htime : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun s : ℝ => (x, s)) t :=
    ((differentiableAt_const x).prodMk differentiableAt_id).mdifferentiableAt
  have hct := (((hc.joint_c1 (x, t) hmem).contMDiffAt
    ((isOpen_univ.prod isOpen_interior).mem_nhds hmem)).mdifferentiableAt
      (by norm_num)).comp t htime
  have hqd : DifferentiableAt ℝ (fun s => e (c x s)) t :=
    ((hC1.contDiffAt ((isOpen_univ.prod isOpen_interior).mem_nhds hmem)).differentiableAt
      (by norm_num)).comp t ((differentiableAt_const x).prodMk differentiableAt_id)
  have hchain : fderiv ℝ (fun s => e (c x s)) t =
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t)).comp
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => c x s) t) := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp t (he.mdifferentiable (by simp)).mdifferentiableAt hct
  have heq := congrArg (fun L : ℝ →L[ℝ] W => L 1) hchain
  change deriv (fun s => e (c x s)) t =
    mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (curveVelocity (fun s => c x s) t) at heq
  rw [hc.equation t ht x] at heq
  exact hqd.hasDerivAt.congr_deriv heq

end PoincareConjecture.M63
