import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Equation.Potential
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Equation.TensorSquare
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.ScalarEvolution









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem hasDerivAt_entropyFactor (F : RicciFlow n M J)
    {f : M × ℝ → ℝ} {t : ℝ} (ht : t ∈ interior J)
    (hf : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f (univ ×ˢ J))
    (x : M) :
    HasDerivAt (fun s ↦ F.entropyFactor f s x)
      (-(2 * (F.connection t).laplacian (fun y ↦ f (y, t)) x -
          (F.metric t).inner x ((F.connection t).gradient (fun y ↦ f (y, t)) x)
            ((F.connection t).gradient (fun y ↦ f (y, t)) x) +
          (F.connection t).scalarCurvature x) + deriv (fun s ↦ f (x, s)) t +
        -t * (2 * deriv (fun s ↦ (F.connection s).laplacian (fun y ↦ f (y, s)) x) t -
          deriv (fun s ↦ (F.metric s).inner x
            ((F.connection s).gradient (fun y ↦ f (y, s)) x)
            ((F.connection s).gradient (fun y ↦ f (y, s)) x)) t +
          deriv (fun s ↦ (F.connection s).scalarCurvature x) t)) t := by
  have hL := (F.hasDerivAt_laplacian ht hf x).differentiableAt.hasDerivAt
  have hN := (F.hasDerivAt_gradient_normSq ht hf x).differentiableAt.hasDerivAt
  have hR := (F.hasDerivAt_scalarCurvature ht x).differentiableAt.hasDerivAt
  have hsmooth := hf.contMDiffAt (prod_mem_nhds Filter.univ_mem
    (mem_interior_iff_mem_nhds.mp ht) : univ ×ˢ J ∈ 𝓝 (x, t))
  have hs : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s ↦ f (x, s)) t :=
    hsmooth.comp t (contMDiffAt_const.prodMk contMDiffAt_id)
  have hF := (hs.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have h := ((((hasDerivAt_id t).neg).mul (((hL.const_mul 2).sub hN).add hR)).add
    hF).sub_const (n : ℝ)
  apply h.congr_deriv
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq]
  ring

theorem entropyFactor_drift_eq_tensor_square (F : RicciFlow n M J)
    {f : M × ℝ → ℝ} {t : ℝ} (ht : t ∈ interior J) (ht0 : t < 0)
    (hf : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f (univ ×ˢ J))
    (hpde : ∀ y, F.potentialResidual f t y = 0) (x : M) :
    deriv (fun s ↦ F.entropyFactor f s x) t +
      (F.connection t).spatialDrift (fun y ↦ f (y, t)) (F.entropyFactor f t) x =
        2 * -t * (F.connection t).solitonDefectNormSq (fun y ↦ f (y, t))
          (1 / (2 * -t)) x := by
  have hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ f (y, t)) :=
    contMDiffOn_univ.mp (hf.comp (contMDiffOn_id.prodMk contMDiffOn_const)
      (fun y _ ↦ ⟨mem_univ y, interior_subset ht⟩))
  have hL := F.laplacian_drift_of_potentialResidual ht hf hpde x
  have hN := F.gradientEnergy_drift_of_potentialResidual ht hf hpde x
  have hR := (F.hasDerivAt_scalarCurvature ht x).deriv
  have hF := hpde x
  rw [(F.hasDerivAt_entropyFactor ht hf x).deriv,
    F.spatialDrift_entropyFactor hφ x,
    (F.connection t).solitonDefectNormSq_expansion]
  dsimp only [LeviCivitaData.spatialDrift, potentialResidual] at hL hN hF ⊢
  rw [← (F.connection t).inner_gradient (fun y ↦ f (y, t)) x
    ((F.connection t).gradient (fun y ↦ f (y, t)) x)]
  have htne : t ≠ 0 := ne_of_lt ht0
  linear_combination (norm := (field_simp [htne]; ring))
    (-2 * t) * hL + t * hN - t * hR + hF

theorem soliton_equation_of_entropyFactor_eq_zero (F : RicciFlow n M J)
    {f : M × ℝ → ℝ} {t : ℝ} (ht : t ∈ interior J) (ht0 : t < 0)
    (hf : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f (univ ×ˢ J))
    (hpde : ∀ y, F.potentialResidual f t y = 0)
    (hzero : ∀ s ∈ J, ∀ y, F.entropyFactor f s y = 0)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    (F.connection t).ricci x u v +
      (F.connection t).hessian (fun y ↦ f (y, t)) x u v +
      (1 / (2 * t)) * (F.metric t).inner x u v = 0 := by
  have hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ f (y, t)) :=
    contMDiffOn_univ.mp (hf.comp (contMDiffOn_id.prodMk contMDiffOn_const)
      (fun y _ ↦ ⟨mem_univ y, interior_subset ht⟩))
  have heq : (fun s ↦ F.entropyFactor f s x) =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
    filter_upwards [show ∀ᶠ s in 𝓝 t, s ∈ J from mem_interior_iff_mem_nhds.mp ht]
      with s hs using hzero s hs x
  have htime : deriv (fun s ↦ F.entropyFactor f s x) t = 0 := by
    rw [heq.deriv_eq, deriv_const]
  have hspace : F.entropyFactor f t = fun _ ↦ 0 :=
    funext (hzero t (interior_subset ht))
  have hsq := F.entropyFactor_drift_eq_tensor_square ht ht0 hf hpde x
  rw [htime, hspace, LeviCivitaData.spatialDrift_const, zero_add] at hsq
  have hdefect := ((F.connection t).solitonDefectNormSq_eq_zero_iff hφ
    (1 / (2 * -t)) x).mp ((mul_eq_zero.mp hsq.symm).resolve_left
      (mul_ne_zero (by norm_num) (neg_ne_zero.mpr (ne_of_lt ht0)))) u v
  simpa only [mul_neg, div_neg, neg_mul, sub_neg_eq_add] using hdefect

theorem soliton_equation_of_scalar_equalities (F : RicciFlow n M (Iio 0))
    {f : M × ℝ → ℝ}
    (hf : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f (univ ×ˢ Iio 0))
    (hpde : ∀ t < 0, ∀ y, F.potentialResidual f t y = 0)
    (hzero : ∀ t < 0, ∀ y, F.entropyFactor f t y = 0) :
    ∀ t < 0, ∀ x : M, ∀ u v : TangentSpace (𝓡 n) x,
      (F.connection t).ricci x u v +
        (F.connection t).hessian (fun y ↦ f (y, t)) x u v +
        (1 / (2 * t)) * (F.metric t).inner x u v = 0 := by
  intro t ht x u v
  exact F.soliton_equation_of_entropyFactor_eq_zero
    (by simpa only [interior_Iio, mem_Iio] using ht) ht hf (hpde t ht) hzero x u v

end PoincareConjecture.RicciFlow
