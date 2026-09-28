import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Data
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Real
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LineIsometry











set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Poincare.Analysis.Heat Set

universe u

namespace PoincareConjecture.LeviCivitaData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]
  {g : RiemannianMetric 1 M}


theorem inner_gradient_eq_one_of_metric_coordinate (D : LeviCivitaData g)
    {f : M → ℝ} {x : M}
    (hmetric : ∀ v w : TangentSpace (𝓡 1) x,
      g.inner x v w = mvfderiv (𝓡 1) f x v * mvfderiv (𝓡 1) f x w) :
    g.inner x (D.gradient f x) (D.gradient f x) = 1 := by
  let : Nontrivial (TangentSpace (𝓡 1) x) := by
    change Nontrivial (EuclideanSpace ℝ (Fin 1))
    infer_instance
  obtain ⟨v, hv⟩ := exists_ne (0 : TangentSpace (𝓡 1) x)
  have hdf : mvfderiv (𝓡 1) f x v ≠ 0 := by
    intro hz
    have hp := g.pos x v hv
    rw [hmetric, hz, zero_mul] at hp
    exact (lt_irrefl 0) hp
  have h := (hmetric (D.gradient f x) v).symm.trans (D.inner_gradient f x v)
  rw [D.inner_gradient]
  exact mul_right_cancel₀ hdf (h.trans (one_mul _).symm)


theorem hessian_eq_zero_of_unit_gradient (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : ∀ x, g.inner x (D.gradient f x) (D.gradient f x) = 1)
    (x : M) (v w : TangentSpace (𝓡 1) x) : D.hessian f x v w = 0 := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 1) x) = 1 :=
    finrank_euclideanSpace_fin
  have hne : D.gradient f x ≠ 0 := by
    intro hz
    have hh := hunit x
    simp only [hz, map_zero] at hh
    norm_num at hh
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hdim hne w
  have hd := D.mvfderiv_gradient_normSq (hf x) v
  have heq : (fun y => g.inner y (D.gradient f y) (D.gradient f y)) =
      fun _ => (1 : ℝ) := funext hunit
  rw [heq, mvfderiv_const] at hd
  have hz : D.hessian f x v (D.gradient f x) = 0 := by
    simpa only [zero_apply] using (mul_eq_zero.mp hd.symm).resolve_left (by norm_num)
  rw [D.hessian_eq_inner_connection_gradient (hf x)] at hz ⊢
  simp only [map_smul, smul_eq_mul, hz, mul_zero]


theorem laplacian_eq_zero_of_unit_gradient (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : ∀ x, g.inner x (D.gradient f x) (D.gradient f x) = 1) (x : M) :
    D.laplacian f x = 0 := by
  simp only [laplacian, D.hessian_eq_zero_of_unit_gradient hf hunit, Finset.sum_const_zero]



theorem hasDerivAt_realHeatKernel_comp_of_unit_gradient (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : ∀ x, g.inner x (D.gradient f x) (D.gradient f x) = 1)
    {t : ℝ} (ht : 0 < t) (x : M) :
    HasDerivAt (fun s => realHeatKernel s (f x))
      (D.laplacian (fun y => realHeatKernel t (f y)) x) t := by
  have hK : ContDiff ℝ ∞ (realHeatKernel t) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact (contDiffOn_realHeatKernel.contDiffAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds
        (show (t, z) ∈ {p : ℝ × ℝ | 0 < p.1} from ht))).comp z
        (contDiffAt_const.prodMk contDiffAt_id)
  change HasDerivAt (fun s => realHeatKernel s (f x))
    (D.laplacian (realHeatKernel t ∘ f) x) t
  rw [D.laplacian_comp hf hK, D.laplacian_eq_zero_of_unit_gradient hf hunit,
    hunit, mul_zero, mul_one, zero_add]
  exact (realHeatKernel_properties ht).2.2.2 (f x)



theorem hasDerivAt_realHeatKernel_shift_comp_of_unit_gradient
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : ∀ x, g.inner x (D.gradient f x) (D.gradient f x) = 1)
    (a : ℝ) {t : ℝ} (ht : 0 < t) (x : M) :
    HasDerivAt (fun s => realHeatKernel s (a - f x))
      (D.laplacian (fun y => realHeatKernel t (a - f y)) x) t := by
  let q : ℝ → ℝ := fun z => a - z
  have hq : ContDiff ℝ ∞ q := by fun_prop
  have hqf : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ (q ∘ f) := hq.contMDiff.comp hf
  have hgradq (z : M) : D.gradient (q ∘ f) z =
      (-1 : ℝ) • D.gradient f z := by
    simpa [q] using D.gradient_comp ((hf z).mdifferentiableAt (by simp))
      (hq.differentiable (by simp) (f z))
  have hunitq (z : M) : g.inner z (D.gradient (q ∘ f) z)
      (D.gradient (q ∘ f) z) = 1 := by
    simp only [hgradq, map_smul, smul_apply, smul_eq_mul, hunit]
    norm_num
  exact D.hasDerivAt_realHeatKernel_comp_of_unit_gradient hqf hunitq ht x



theorem hasDerivAt_realHeatKernel_of_metric_coordinate
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ f)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 1) x),
      g.inner x v w = mvfderiv (𝓡 1) f x v * mvfderiv (𝓡 1) f x w)
    (y : M) {t : ℝ} (ht : 0 < t) (x : M) :
    HasDerivAt (fun s => realHeatKernel s (f y - f x))
      (D.laplacian (fun z => realHeatKernel t (f y - f z)) x) t := by
  exact D.hasDerivAt_realHeatKernel_shift_comp_of_unit_gradient hf
    (fun z => D.inner_gradient_eq_one_of_metric_coordinate (hmetric z)) (f y) ht x

section ConservativeData

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

open PoincareConjecture.RiemannianMetric



theorem exists_conservativeHeatKernelData_of_metric_line_coordinate
    (g : RiemannianMetric 1 M) (e : M ≃ ℝ)
    (he : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ e)
    (hi : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) 1 e.symm)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 1) x),
      g.inner x v w = mvfderiv (𝓡 1) e x v * mvfderiv (𝓡 1) e x w)
    (D : LeviCivitaData g) :
    Nonempty (PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData g) := by
  have hedist := g.edist_eq_of_metric_line_coordinate e (he.of_le (by simp)) hi hmetric
  let H : PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData g :=
    { connection := D
      kernel := fun x y t => realHeatKernel t (e y - e x)
      positive := fun x y t ht => transported_realHeatKernel_pos g e hedist ht x y
      smooth := by
        intro x y t ht
        have hK : ContDiff ℝ ∞ (realHeatKernel t) := by
          apply contDiff_iff_contDiffAt.mpr
          intro z
          exact (contDiffOn_realHeatKernel.contDiffAt
            ((isOpen_lt continuous_const continuous_fst).mem_nhds
              (show (t, z) ∈ {p : ℝ × ℝ | 0 < p.1} from ht))).comp z
            (contDiffAt_const.prodMk contDiffAt_id)
        have harg : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun z : M => e y - e z) :=
          contMDiff_const.sub he
        exact (hK.contMDiff.comp harg) x
      timeDifferentiable := fun x y t ht =>
        transported_realHeatKernel_timeDifferentiable g e hedist ht x y
      mass_one := fun x t ht => transported_realHeatKernel_mass_one g e hedist ht x
      initial := by
        intro φ hφ hφc x
        exact tendsto_transported_realHeatKernel_initial g e hedist hφ hφc x
      heat_equation := by
        intro x y t ht
        exact (D.hasDerivAt_realHeatKernel_of_metric_coordinate he hmetric y ht x).deriv
      first_moment_integrable := fun x t ht =>
        transported_realHeatKernel_first_moment_integrable g e hedist ht x
      first_moment_bound := by
        refine ⟨Real.sqrt 2, Real.sqrt_pos.2 (by norm_num), ?_⟩
        intro x t ht ht1
        exact transported_realHeatKernel_first_moment_bound g e hedist ht ht1 x
      first_moment_tendsto_zero :=
        tendsto_transported_realHeatKernel_first_moment g e hedist }
  exact ⟨H⟩

end ConservativeData

omit [IsManifold (𝓡 1) ∞ M] in


theorem contMDiffOn_realHeatKernel_coordinate {e : M → ℝ}
    (he : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ e) :
    ContMDiffOn ((𝓘(ℝ, ℝ).prod (𝓡 1)).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : (ℝ × M) × M => realHeatKernel p.1.1 (e p.2 - e p.1.2))
      ((Ioi 0 ×ˢ univ) ×ˢ univ) := by
  intro p hp
  have hK := contDiffOn_realHeatKernel.contDiffAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds
      (show (p.1.1, e p.2 - e p.1.2) ∈ {q : ℝ × ℝ | 0 < q.1} from hp.1.1))
  exact (hK.contMDiffAt.comp p
    ((contMDiffAt_fst.comp p contMDiffAt_fst).prodMk_space
      (((he p.2).comp p contMDiffAt_snd).sub
        ((he p.1.2).comp p (contMDiffAt_snd.comp p contMDiffAt_fst))))).contMDiffWithinAt

end PoincareConjecture.LeviCivitaData
