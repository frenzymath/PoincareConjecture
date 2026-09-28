import PoincareConjecture.Proofs.Horizon.Analysis.Matrix.Determinant
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Density
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Contraction
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private lemma scalar_eq_inverse_gram_ricci
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M)
    (b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)) :
    D.scalarCurvature x =
      ∑ i, ∑ j, (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j *
        D.ricci x (b i) (b j) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨A, hA⟩ := hD.2.1.1 x
  have h := bilinear_sum_basis_eq_inverse_gram (bilinearOfTwoTensor A)
    b (g.orthonormalBasis x)
  change (∑ a, bilinearOfTwoTensor A (g.orthonormalBasis x a) (g.orthonormalBasis x a)) =
    ∑ i, ∑ j, (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j *
      bilinearOfTwoTensor A (b i) (b j) at h
  simpa only [LeviCivitaData.scalarCurvature, bilinearOfTwoTensor_apply, ← hA,
    LeviCivitaData.ricciEvaluation,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

private lemma hasDerivAt_basis_density
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (x : M)
    (hD : (F.connection t).CurvatureTensorCalculus)
    (b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)) :
    HasDerivAt
      (fun s => Real.sqrt (Matrix.of (fun i j => (F.metric s).inner x (b i) (b j))).det)
      (-(F.connection t).scalarCurvature x *
        Real.sqrt (Matrix.of (fun i j => (F.metric t).inner x (b i) (b j))).det) t := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let G := fun s => Matrix.of (fun i j => (F.metric s).inner x (b i) (b j))
  let G' := Matrix.of (fun i j => -2 * (F.connection t).ricci x (b i) (b j))
  have hpos : 0 < (G t).det :=
    (Matrix.posDef_gram_of_linearIndependent b.linearIndependent).det_pos
  have hd := Poincare.Matrix.hasDerivAt_sqrt_det_eq_half_trace_inv_mul G G' t
    (fun i j => (F.equation t (interior_subset ht) x (b i) (b j)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)) hpos
  have hscalar := scalar_eq_inverse_gram_ricci (F.connection t) hD x b
  have hsymm (i j : Fin n) :
      (F.connection t).ricci x (b j) (b i) =
        (F.connection t).ricci x (b i) (b j) :=
    (hD.2.2.2.1 x (b j) (b i) (b j) (b i)).2.2.2
  have htrace : Matrix.trace ((G t)⁻¹ * G') =
      -2 * (F.connection t).scalarCurvature x := by
    rw [hscalar]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, G', Matrix.of_apply,
      hsymm, Finset.mul_sum]
    dsimp only [G]
    congr 1
    ext i
    congr 1
    ext j
    ring
  rw [htrace] at hd
  convert hd using 1
  ring



theorem hasDerivAt_pullbackVolumeDensity
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (hD : (F.connection t).CurvatureTensorCalculus)
    (f : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n))
    (hi : Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    HasDerivAt (fun s => (F.metric s).pullbackVolumeDensity f x)
      (-(F.connection t).scalarCurvature (f x) *
        (F.metric t).pullbackVolumeDensity f x) t := by
  let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap
  let e := LinearEquiv.ofInjectiveEndo L hi
  let b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) (f x)) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map e
  have hb (i : Fin n) : b i =
      mfderiv (𝓡 n) (𝓡 n) f x (EuclideanSpace.basisFun (Fin n) ℝ i) := rfl
  simpa only [RiemannianMetric.pullbackVolumeDensity, hb] using
    F.hasDerivAt_basis_density ht (f x) hD b

private lemma contDiffAt_pullback_inner_spacetime
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (v w : EuclideanSpace ℝ (Fin n)) :
    ContDiffAt ℝ ∞ (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      (F.metric p.1).inner (f p.2) (mfderiv (𝓡 n) (𝓡 n) f p.2 v)
        (mfderiv (𝓡 n) (𝓡 n) f p.2 w)) (t, x) := by
  have hg := (F.smooth (t, f x) ⟨interior_subset ht, mem_univ _⟩).contMDiffAt
    (prod_mem_nhds (mem_interior_iff_mem_nhds.mp ht) Filter.univ_mem)
  have hp : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, f p.2)) (t, x) :=
    contMDiffAt_fst.prodMk (hf.comp (t, x) contMDiffAt_snd)
  have hv (v : EuclideanSpace ℝ (Fin n)) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (f p.2)
            (mfderiv (𝓡 n) (𝓡 n) f p.2 v)) (t, x) :=
    (RiemannianMetric.contMDiffAt_mfderiv_const_vector hf v).comp
      (t, x) contMDiffAt_snd
  have h := (hg.comp (t, x) hp).clm_bundle_apply₂ (F₃ := ℝ)
    (E₃ := Bundle.Trivial M ℝ) (hv v) (hv w)
  have hh := (Bundle.contMDiffAt_totalSpace.mp h).2
  simp +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hh
  exact hh.contDiffAt


lemma contDiffAt_pullbackVolumeDensity_spacetime
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hi : Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    ContDiffAt ℝ ∞ (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      (F.metric p.1).pullbackVolumeDensity f p.2) (t, x) := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let G := fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
    Matrix.of (fun i j => (F.metric p.1).inner (f p.2)
      (mfderiv (𝓡 n) (𝓡 n) f p.2 (b i)) (mfderiv (𝓡 n) (𝓡 n) f p.2 (b j)))
  have hdet : ContDiffAt ℝ ∞ (fun p => (G p).det) (t, x) := by
    have heq : (fun p => (G p).det) = fun p =>
        ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) * ∏ i, G p (σ i) i := by
      funext p
      simp [Matrix.det_apply, Units.smul_def]
    rw [heq]
    apply ContDiffAt.sum
    intro σ _
    apply contDiffAt_const.mul
    exact contDiffAt_prod fun i _ => F.contDiffAt_pullback_inner_spacetime ht hf _ _
  exact hdet.sqrt ((F.metric t).pullback_gram_det_ne_zero (f x)
    (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap hi)



theorem hasDerivAt_integral_pullbackVolumeDensity_of_subset
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (hD : (F.connection t).CurvatureTensorCalculus)
    (f : EuclideanSpace ℝ (Fin n) → M) {K L : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hL : IsCompact L) (hKL : K ⊆ L)
    (hf : ∀ x ∈ L, ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hi : ∀ x ∈ L, Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    HasDerivAt (fun s => ∫ x in K, (F.metric s).pullbackVolumeDensity f x)
      (∫ x in K, -(F.connection t).scalarCurvature (f x) *
        (F.metric t).pullbackVolumeDensity f x) t := by
  let ρ := fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
    (F.metric p.1).pullbackVolumeDensity f p.2
  let q := fun s x => fderiv ℝ ρ (s, x) (1, 0)
  have hsmooth (s : ℝ) (hs : s ∈ interior J) (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ L) : ContDiffAt ℝ ∞ ρ (s, x) :=
    F.contDiffAt_pullbackVolumeDensity_spacetime hs (hf x hx) (hi x hx)
  have hρ (s : ℝ) (hs : s ∈ interior J) : ContinuousOn (fun x => ρ (s, x)) L := by
    intro x hx
    exact ((hsmooth s hs x hx).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hq : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => q p.1 p.2)
      (interior J ×ˢ L) := by
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    exact (((hsmooth s hs x hx).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiffAt_const).continuousAt.continuousWithinAt
  have hqs (s : ℝ) (hs : s ∈ interior J) : ContinuousOn (q s) L :=
    hq.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hx => ⟨hs, hx⟩)
  have hd (s : ℝ) (hs : s ∈ interior J) (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ L) : HasDerivAt (fun r => ρ (r, x)) (q s x) s := by
    exact ((hsmooth s hs x hx).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior t ht
  have hcl : Metric.closedBall t (r / 2) ⊆ interior J :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t (r / 2)).prod hL).exists_bound_of_continuousOn
    (hq.mono (prod_mono hcl Subset.rfl))
  have hbound : Integrable (fun _ : EuclideanSpace ℝ (Fin n) => C)
      (volume.restrict K) := integrableOn_const
        (lt_of_le_of_lt (measure_mono hKL) hL.measure_lt_top).ne
  have hint := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => ρ (s, x)) (F' := q) (μ := volume.restrict K)
    (bound := fun _ => C)
    (Metric.closedBall_mem_nhds t (by positivity : 0 < r / 2))
    (by
      filter_upwards [isOpen_interior.mem_nhds ht] with s hs
      exact ((hρ s hs).mono hKL).aestronglyMeasurable hK)
    (((hρ t ht).integrableOn_compact hL).mono_set hKL)
    (((hqs t ht).mono hKL).aestronglyMeasurable hK)
    (by
      filter_upwards [ae_restrict_mem hK] with x hx
      intro s hs
      exact hC (s, x) ⟨hs, hKL hx⟩)
    hbound
    (by
      filter_upwards [ae_restrict_mem hK] with x hx
      intro s hs
      exact hd s (hcl hs) x (hKL hx))).2
  apply hint.congr_deriv
  apply setIntegral_congr_fun hK
  intro x hx
  exact (hd t ht x (hKL hx)).unique
    (F.hasDerivAt_pullbackVolumeDensity ht hD f x (hi x (hKL hx)))


theorem hasDerivAt_integral_pullbackVolumeDensity
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (hD : (F.connection t).CurvatureTensorCalculus)
    (f : EuclideanSpace ℝ (Fin n) → M) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K)
    (hf : ∀ x ∈ K, ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    HasDerivAt (fun s => ∫ x in K, (F.metric s).pullbackVolumeDensity f x)
      (∫ x in K, -(F.connection t).scalarCurvature (f x) *
        (F.metric t).pullbackVolumeDensity f x) t :=
  F.hasDerivAt_integral_pullbackVolumeDensity_of_subset ht hD f
    hK.measurableSet hK Subset.rfl hf hi

end PoincareConjecture.RicciFlow
