import PoincareConjecture.Proofs.M10.PreferredFields
import PoincareConjecture.Proofs.M10.RegularGerms
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem preferred_diagonal_koszul (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (q : M) (v w : TangentSpace (𝓡 n) q) :
    2 * g.inner q (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) q v) w =
      2 * mvfderiv (𝓡 n) (fun x ↦ g.inner x
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w x)) q v -
      mvfderiv (𝓡 n) (fun x ↦ g.inner x
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) q w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hv := FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  have hw := FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w
  have h₁ := D.metricCompatible.mvfderiv_inner_eq
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) hv hw
  have h₂ := D.metricCompatible.mvfderiv_inner_eq
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) hv hv
  have ht := (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero) hv hw
  rw [preferredFields_mlieBracket_eq_zero] at ht
  simp only [FiberBundle.extend_apply_self] at h₁ h₂ ht
  have hconn := sub_eq_zero.mp ht
  change mvfderiv (𝓡 n) (fun x ↦ g.inner x
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w x)) q v =
    g.inner q (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) q v) w +
      g.inner q v (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) q v) at h₁
  change mvfderiv (𝓡 n) (fun x ↦ g.inner x
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) q w =
    g.inner q (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) q w) v +
      g.inner q v (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) q w) at h₂
  rw [g.symm q _ v] at h₂
  rw [hconn] at h₁
  linarith

set_option backward.isDefEq.respectTransparency false in

theorem preferredField_second_scalar_derivative {f : M → ℝ} (q : M)
    (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f q) (v : TangentSpace (𝓡 n) q) :
    mvfderiv (𝓡 n) (fun x ↦ mvfderiv (𝓡 n) f x
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) q v =
        fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 n) q).symm))
          (extChartAt (𝓡 n) q q) v v := by
  let e := extChartAt (𝓡 n) q
  let l := f ∘ e.symm
  let v' : EuclideanSpace ℝ (Fin n) := v
  have hi : ContMDiffAt (𝓡 n) (𝓡 n) 2 e.symm (e q) :=
    (contMDiffOn_extChartAt_symm q).contMDiffAt
      (extChartAt_target_mem_nhds (I := 𝓡 n) q)
  have hfl : ContDiffAt ℝ 2 l (e q) := by
    have hf' : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f (e.symm (e q)) := by
      simpa only [e, extChartAt_to_inv] using hf
    exact (hf'.comp (e q) hi).contDiffAt
  have hDl := (hfl.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  let K := fun y ↦ fderiv ℝ l y v'
  have hK : DifferentiableAt ℝ K (e q) :=
    hDl.clm_apply (differentiableAt_const v')
  have heq : (fun x ↦ mvfderiv (𝓡 n) f x
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) =ᶠ[𝓝 q] K ∘ e := by
    filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hf,
      (chartAt (EuclideanSpace ℝ (Fin n)) q).open_source.mem_nhds (mem_chart_source _ _)]
      with x hx hchart
    exact (preferredField_scalar_derivative q v hchart (hx.mdifferentiableAt two_ne_zero)).symm
  rw [mvfderiv_eq_of_eventuallyEq heq]
  have hchain := mfderiv_comp_apply q hK.mdifferentiableAt
    (mdifferentiableAt_extChartAt (mem_chart_source _ _)) v
  rw [mfderiv_extChartAt_self, mfderiv_eq_fderiv] at hchain
  change mvfderiv (𝓡 n) (K ∘ e) q v = fderiv ℝ K (e q) v at hchain
  change mvfderiv (𝓡 n) (K ∘ e) q v = _
  rw [show mvfderiv (𝓡 n) (K ∘ e) q v = fderiv ℝ K (e q) v from hchain]
  have hEval := hDl.hasFDerivAt.clm_apply (hasFDerivAt_const v' (e q))
  have hEq := congrArg (fun D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ D v') hEval.fderiv
  simpa only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply,
    K, l] using hEq

theorem preferred_hessian_of_metric_dual (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {f : M → ℝ} (q : M) (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f q)
    (v w : TangentSpace (𝓡 n) q)
    (hdual : ∀ a, mvfderiv (𝓡 n) f q a = g.inner q w a) :
    D.hessian f q v v =
      fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 n) q).symm))
          (extChartAt (𝓡 n) q q) v v -
        mvfderiv (𝓡 n) (fun x ↦ g.inner x
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w x)) q v +
        mvfderiv (𝓡 n) (fun x ↦ g.inner x
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) q w / 2 := by
  have hk := preferred_diagonal_koszul g D q v w
  unfold LeviCivitaData.hessian LeviCivitaData.hessianOnFields
  rw [FiberBundle.extend_apply_self, preferredField_second_scalar_derivative q hf v,
    hdual, g.symm q w _]
  linarith

end PoincareConjecture.M10
