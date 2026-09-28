import PoincareConjecture.Definitions.M63Polygon
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessAmbientAcceleration
import PoincareConjecture.Proofs.M63.Mathlib.SmoothRetractionDifferentials
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u v w

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {Z : Type w} [TopologicalSpace Z] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι




theorem continuous_embedded_initial_jets
    (F : RicciFlow n M (Icc a b)) {tau : ℝ} (htau : tau ∈ Icc a b)
    (gamma : Z → ℝ → M)
    (hgamma : Continuous (fun z : Z × ℝ => gamma z.1 z.2))
    (hfirst : Continuous (fun z : Z × ℝ =>
      m63AngularFirstJet (n := n) (gamma z.1) z.2))
    (hsecond : Continuous (fun z : Z × ℝ =>
      m63AngularSecondJet (F.connection tau) (gamma z.1) z.2))
    (hC2 : ∀ z, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (gamma z))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p) :
    (∀ z, ContDiff ℝ 2 (fun x => e (gamma z x))) ∧
    Continuous (fun z : Z × ℝ => e (gamma z.1 z.2)) ∧
    Continuous (fun z : Z × ℝ => deriv (fun y => e (gamma z.1 y)) z.2) ∧
    Continuous (fun z : Z × ℝ => deriv (deriv (fun y => e (gamma z.1 y))) z.2) := by
  have hspace (z : Z) : ContDiff ℝ 2 (fun x => e (gamma z x)) :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp (hC2 z)).contDiff
  have hderiv (z : Z) (x : ℝ) : HasDerivAt (fun y => e (gamma z y))
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma z x)
        (curveVelocity (n := n) (gamma z) x) : W) x := by
    have hchain : fderiv ℝ (fun y => e (gamma z y)) x =
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma z x)).comp
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (gamma z) x) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp x (he.mdifferentiable (by simp)).mdifferentiableAt
        ((hC2 z x).mdifferentiableAt (by norm_num))
    exact ((hspace z).differentiable (by norm_num) x).hasDerivAt.congr_deriv
      (congrArg (fun L : ℝ →L[ℝ] W => L 1) hchain)
  have hpush : Continuous (fun p : TangentBundle (𝓡 n) M =>
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e p.1 p.2 : W)) :=
    (contMDiff_snd_tangentBundle_modelSpace (n := ∞) W 𝓘(ℝ, W)).continuous.comp
      (he.continuous_tangentMap (by simp))
  have hzero : Continuous (fun z : Z × ℝ => e (gamma z.1 z.2)) :=
    he.continuous.comp hgamma
  have hfirstW : Continuous
      (fun z : Z × ℝ => deriv (fun y => e (gamma z.1 y)) z.2) :=
    (hpush.comp hfirst).congr (fun z => (hderiv z.1 z.2).deriv.symm)
  have hacc : Continuous (fun z : Z × ℝ =>
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma z.1 z.2)
        (rampHorizontalCovariantDerivative (F.connection tau) (gamma z.1)
          (fun y => curveVelocity (n := n) (gamma z.1) y) z.2) : W)) :=
    hpush.comp hsecond
  have hB : ContinuousOn
      (fun z : (ℝ × W) × W =>
        (coordinateHessian (F.connection z.1.1) e (ρ z.1.2)
          (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2)
          (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2) : W))
      ((Icc a b ×ˢ U) ×ˢ univ) :=
    (flow_coordinateHessian_pullback_contDiffOn F he hU hρ).continuousOn
  let coefficientInput : Z × ℝ → (ℝ × W) × W := fun z =>
    ((tau, e (gamma z.1 z.2)), deriv (fun y => e (gamma z.1 y)) z.2)
  have hinput : Continuous coefficientInput :=
    (continuous_const.prodMk hzero).prodMk hfirstW
  have hmem (z : Z × ℝ) : coefficientInput z ∈ ((Icc a b ×ˢ U) ×ˢ univ) :=
    ⟨⟨htau, heU (mem_range_self _)⟩, mem_univ _⟩
  have hcomposed := hB.comp_continuous (f := coefficientInput) hinput hmem
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  have hHessian : Continuous (fun z : Z × ℝ =>
      (coordinateHessian (F.connection tau) e (gamma z.1 z.2)
        (curveVelocity (n := n) (gamma z.1) z.2)
        (curveVelocity (n := n) (gamma z.1) z.2) : W)) := by
    apply hcomposed.congr
    intro z
    change coordinateHessian (F.connection tau) e (ρ (e (gamma z.1 z.2)))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (e (gamma z.1 z.2))
        (deriv (fun y => e (gamma z.1 y)) z.2))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (e (gamma z.1 z.2))
        (deriv (fun y => e (gamma z.1 y)) z.2)) = _
    rw [(hderiv z.1 z.2).deriv]
    erw [hleft (gamma z.1 z.2) (curveVelocity (n := n) (gamma z.1) z.2),
      hρe (gamma z.1 z.2)]
  refine ⟨hspace, hzero, hfirstW, ?_⟩
  exact (hHessian.add hacc).congr (fun z =>
    (secondDeriv_embedding_eq_hessian_add_acceleration
      (F.connection tau) he (hC2 z.1) z.2).symm)

end PoincareConjecture.M63
