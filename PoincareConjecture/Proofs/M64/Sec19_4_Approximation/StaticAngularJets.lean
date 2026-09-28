import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ContinuousDependenceAngularJets
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Hessian.Tensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u v w

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem m64_continuous_hessian_on_tangent_field
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {Z : Type w} [TopologicalSpace Z] {gamma : Z → M}
    {V : ∀ z, TangentSpace (𝓡 n) (gamma z)}
    (hgamma : Continuous gamma)
    (hV : Continuous (fun z => (⟨gamma z, V z⟩ : TangentBundle (𝓡 n) M))) :
    Continuous (fun z => D.hessian f (gamma z) (V z) (V z)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hgrad := D.contMDiff_gradient hf
  have hconnection := D.smooth.contMDiff.contMDiff
    (show ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (∞ + 1) (T% (D.gradient f)) univ from by simpa using hgrad.contMDiffOn)
  have hc := (contMDiffOn_univ.mp hconnection).continuous.comp hgamma
  have hcv := hc.clm_bundle_apply hV
  have hi := hcv.inner_bundle hV
  exact hi.congr (fun z => (D.hessian_eq_inner_connection_gradient (hf (gamma z))
    (V z) (V z)).symm)

theorem m64_continuous_angular_jets_of_embedded_jets
    (D : LeviCivitaData g)
    {ι : Type v} [Fintype ι] {Z : Type w} [TopologicalSpace Z]
    (gamma : Z → ℝ → M)
    (hC2 : ∀ z, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (gamma z))
    {e : M → EuclideanSpace ℝ ι}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ ι) ∞ e)
    {U : Set (EuclideanSpace ℝ ι)} (hU : IsOpen U) (heU : range e ⊆ U)
    {rho : EuclideanSpace ℝ ι → M}
    (hrho : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ ι) (𝓡 n) ∞ rho U)
    (hrhoe : ∀ p, rho (e p) = p)
    (hzero : Continuous (fun z : Z × ℝ => e (gamma z.1 z.2)))
    (hfirst : Continuous (fun z : Z × ℝ => deriv (fun y => e (gamma z.1 y)) z.2))
    (hsecond : Continuous (fun z : Z × ℝ =>
      deriv (deriv (fun y => e (gamma z.1 y))) z.2)) :
    Continuous (fun z : Z × ℝ => gamma z.1 z.2) ∧
    Continuous (fun z : Z × ℝ => m63AngularFirstJet (n := n) (gamma z.1) z.2) ∧
    Continuous (fun z : Z × ℝ => m63AngularSecondJet D (gamma z.1) z.2) := by
  let W := EuclideanSpace ℝ ι
  have hgamma : Continuous (fun z : Z × ℝ => gamma z.1 z.2) :=
    (hrho.continuousOn.comp_continuous hzero
      (fun _ => heU (mem_range_self _))).congr (fun z => hrhoe (gamma z.1 z.2))
  have hspace (z : Z) : ContDiff ℝ 2 (fun x => e (gamma z x)) :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp (hC2 z)).contDiff
  have hderiv (z : Z) (x : ℝ) : HasDerivAt (fun y => e (gamma z y))
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma z x)
        (curveVelocity (gamma z) x) : W) x := by
    have hchain : fderiv ℝ (fun y => e (gamma z y)) x =
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma z x)).comp
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (gamma z) x) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp x (he.mdifferentiable (by simp)).mdifferentiableAt
        ((hC2 z x).mdifferentiableAt (by norm_num))
    exact ((hspace z).differentiable (by norm_num) x).hasDerivAt.congr_deriv
      (congrArg (fun L : ℝ →L[ℝ] W => L 1) hchain)
  have hpushFirst : Continuous (fun z : Z × ℝ =>
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma z.1 z.2)
        (curveVelocity (gamma z.1) z.2) : W)) :=
    hfirst.congr (fun z => (hderiv z.1 z.2).deriv)
  have hangularFirst : Continuous (fun z : Z × ℝ =>
      m63AngularFirstJet (n := n) (gamma z.1) z.2) :=
    continuousOn_univ.mp
      (M63.continuousOn_tangentSection_of_retraction_pushforward he hU heU hrho hrhoe
        (fun z : Z × ℝ => gamma z.1 z.2)
        (fun z => curveVelocity (gamma z.1) z.2)
        hgamma.continuousOn hpushFirst.continuousOn)
  have hHessian : Continuous (fun z : Z × ℝ =>
      (M63.coordinateHessian D e (gamma z.1 z.2)
        (curveVelocity (gamma z.1) z.2) (curveVelocity (gamma z.1) z.2) : W)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp
    apply continuous_pi
    intro i
    have hei : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => e x i) :=
      (EuclideanSpace.proj i).contDiff.contMDiff.comp he
    exact m64_continuous_hessian_on_tangent_field D hei hgamma hangularFirst
  have hpushSecond : Continuous (fun z : Z × ℝ =>
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma z.1 z.2)
        (rampHorizontalCovariantDerivative D (gamma z.1)
          (fun y => curveVelocity (gamma z.1) y) z.2) : W)) := by
    apply (hsecond.sub hHessian).congr
    intro z
    simp only [Pi.sub_apply]
    rw [M63.secondDeriv_embedding_eq_hessian_add_acceleration D he (hC2 z.1) z.2]
    abel
  exact ⟨hgamma, hangularFirst, continuousOn_univ.mp
    (M63.continuousOn_tangentSection_of_retraction_pushforward he hU heU hrho hrhoe
      (fun z : Z × ℝ => gamma z.1 z.2)
      (fun z => rampHorizontalCovariantDerivative D (gamma z.1)
        (fun y => curveVelocity (gamma z.1) y) z.2)
      hgamma.continuousOn hpushSecond.continuousOn)⟩

end PoincareConjecture
