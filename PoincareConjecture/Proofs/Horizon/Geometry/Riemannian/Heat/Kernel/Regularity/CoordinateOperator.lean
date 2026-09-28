import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Operators.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.ClassicalEquation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Regularity.Coordinates









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open Bundle
open VectorField
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)


def coordinatePrincipalCoefficients (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph E M) (x : E) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => divergenceCoefficients g e x i j / g.pullbackVolumeDensity e x


def coordinateDriftCoefficients (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph E M) (j : Fin n) (x : E) : ℝ :=
  (∑ i, partialDeriv i (fun y => divergenceCoefficients g e y i j) x) /
    g.pullbackVolumeDensity e x

theorem contDiffOn_coordinatePrincipalCoefficients
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun x => coordinatePrincipalCoefficients g e x i j) e.source := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  intro x hx
  have hρ := g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds hx)) (hD.mfderiv_injective hx)
  exact (((contDiffOn_divergenceCoefficients e he hei i j).contDiffAt
    (e.open_source.mem_nhds hx)).div hρ.1 hρ.2.ne').contDiffWithinAt

theorem contDiffOn_coordinateDriftCoefficients
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target) (j : Fin n) :
    ContDiffOn ℝ ∞ (coordinateDriftCoefficients g e j) e.source := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  intro x hx
  have hρ := g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds hx)) (hD.mfderiv_injective hx)
  have hs : ContDiffAt ℝ ∞ (fun x =>
      ∑ i, partialDeriv i (fun y => divergenceCoefficients g e y i j) x) x := by
    apply ContDiffAt.sum
    intro i _
    exact (((contDiffOn_divergenceCoefficients e he hei i j).contDiffAt
      (e.open_source.mem_nhds hx)).fderiv_right
        (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).clm_apply contDiffAt_const
  exact (hs.div hρ.1 hρ.2.ne').contDiffWithinAt

theorem coordinatePrincipalCoefficients_symm
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {x : E} (hx : x ∈ e.source) (i j : Fin n) :
    coordinatePrincipalCoefficients g e x i j =
      coordinatePrincipalCoefficients g e x j i := by
  unfold coordinatePrincipalCoefficients
  rw [divergenceCoefficients_symm e he hei hx i j]

theorem coordinatePrincipalCoefficients_pos
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {x : E} (hx : x ∈ e.source) (v : E) (hv : v ≠ 0) :
    0 < ∑ i, ∑ j, coordinatePrincipalCoefficients g e x i j * v i * v j := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ := (g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds hx)) (hD.mfderiv_injective hx)).2
  have heq : (∑ i, ∑ j, coordinatePrincipalCoefficients g e x i j * v i * v j) =
      (∑ i, ∑ j, divergenceCoefficients g e x i j * v i * v j) /
        g.pullbackVolumeDensity e x := by
    simp only [coordinatePrincipalCoefficients, div_mul_eq_mul_div, Finset.sum_div]
  rw [heq]
  exact div_pos (divergenceCoefficients_pos e he hei hx v hv) hρ

private theorem covector_eq_sum_proj (F : E →L[ℝ] ℝ) :
    F = ∑ j, F (EuclideanSpace.single j 1) • EuclideanSpace.proj j := by
  ext v
  have h := congrArg F ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, sum_apply,
    smul_apply, PiLp.proj_apply, mul_comm] using h.symm

theorem coordinateGradientFlux_eq_sum
    (D : LeviCivitaData g) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {u : M → ℝ} {x : E} (hx : x ∈ e.source)
    (hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ u (e x)) (i : Fin n) :
    g.pullbackVolumeDensity e x *
      WithLp.ofLp (mpullback (𝓡 n) (𝓡 n) e (D.gradient u) x) i =
      ∑ j, divergenceCoefficients g e x i j * partialDeriv j (u ∘ e) x := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hA : (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible := ⟨hD.mfderiv hx, rfl⟩
  have hB := g.isInvertible_pullbackCoefficients (hD.mfderiv_injective hx)
  have hgrad : g.pullbackCoefficients e x
      (mpullback (𝓡 n) (𝓡 n) e (D.gradient u) x) = fderiv ℝ (u ∘ e) x := by
    ext v
    change g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x
      ((mfderiv (𝓡 n) (𝓡 n) e x).inverse (D.gradient u (e x))))
      (mfderiv (𝓡 n) (𝓡 n) e x v) = _
    rw [hA.self_apply_inverse, D.inner_gradient]
    have h := congrArg (fun L => L v) (mvfderiv_comp x
      (hu.mdifferentiableAt (by simp)) (hD.mdifferentiableAt hx))
    simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
      ContinuousLinearMap.comp_apply] at h
    exact h.symm
  have hgrad' := congrArg (g.pullbackCoefficients e x).inverse hgrad
  rw [hB.inverse_apply_self] at hgrad'
  rw [hgrad', covector_eq_sum_proj (fderiv ℝ (u ∘ e) x)]
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul, Finset.mul_sum, divergenceCoefficients, partialDeriv, PiLp.proj_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring



theorem secondOrderOperator_coordinate_eq_laplacian
    (D : LeviCivitaData g) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {U : Set M} (hU : IsOpen U) {u : M → ℝ}
    (hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u U)
    {x : E} (hx : x ∈ e.source) (hxu : e x ∈ U) :
    secondOrderOperator (coordinatePrincipalCoefficients g e)
      (coordinateDriftCoefficients g e) (u ∘ e) x = D.laplacian u (e x) := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ := (g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds hx)) (hD.mfderiv_injective hx)).2
  have huat := hu.contMDiffAt (hU.mem_nhds hxu)
  have hucomp : ContDiffAt ℝ ∞ (u ∘ e) x :=
    contMDiffAt_iff_contDiffAt.mp
      (huat.comp x (he.contMDiffAt (e.open_source.mem_nhds hx)))
  have hA (i j : Fin n) :=
    ((contDiffOn_divergenceCoefficients (g := g) e he hei i j).contDiffAt
      (e.open_source.mem_nhds hx))
  have hpartial (j : Fin n) : ContDiffAt ℝ ∞ (partialDeriv j (u ∘ e)) x :=
    (hucomp.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).clm_apply contDiffAt_const
  have hproduct (i j : Fin n) :
      partialDeriv i (fun y => divergenceCoefficients g e y i j *
        partialDeriv j (u ∘ e) y) x =
      divergenceCoefficients g e x i j * partialDeriv i (partialDeriv j (u ∘ e)) x +
        partialDeriv i (fun y => divergenceCoefficients g e y i j) x *
          partialDeriv j (u ∘ e) x := by
    have hp := fderiv_fun_mul ((hA i j).differentiableAt (by simp))
      ((hpartial j).differentiableAt (by simp))
    have hp' := congrArg (fun L : E →L[ℝ] ℝ =>
      L (EuclideanSpace.single i 1)) hp
    simpa only [partialDeriv, add_apply, smul_apply, smul_eq_mul, mul_comm] using hp'
  have hflux (i : Fin n) : (fun y => g.pullbackVolumeDensity e y *
      WithLp.ofLp (mpullback (𝓡 n) (𝓡 n) e (D.gradient u) y) i) =ᶠ[𝓝 x]
      (fun y => ∑ j, divergenceCoefficients g e y i j * partialDeriv j (u ∘ e) y) := by
    filter_upwards [e.open_source.mem_nhds hx,
      (e.continuousOn.continuousAt (e.open_source.mem_nhds hx)).eventually
        (hU.mem_nhds hxu)] with y hys hyu
    exact coordinateGradientFlux_eq_sum D e he hei hys
      (hu.contMDiffAt (hU.mem_nhds hyu)) i
  have hsum : g.pullbackVolumeDensity e x * D.laplacian u (e x) =
      ∑ i, ∑ j, (divergenceCoefficients g e x i j *
        partialDeriv i (partialDeriv j (u ∘ e)) x +
          partialDeriv i (fun y => divergenceCoefficients g e y i j) x *
            partialDeriv j (u ∘ e) x) := by
    rw [D.density_mul_laplacian_eq_coordinate_divergence e he hei hx huat]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hflux i).fderiv_eq, fderiv_fun_sum
      (fun j _ => ((hA i j).mul (hpartial j)).differentiableAt (by simp))]
    simp only [sum_apply, EuclideanSpace.basisFun_apply]
    exact Finset.sum_congr rfl (fun j _ => hproduct i j)
  apply (mul_left_cancel₀ hρ.ne')
  rw [hsum]
  unfold secondOrderOperator coordinatePrincipalCoefficients coordinateDriftCoefficients
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, ← add_div]
  rw [mul_div_cancel₀ _ hρ.ne']
  simp_rw [Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun j i =>
    partialDeriv i (fun y => divergenceCoefficients g e y i j) x *
      partialDeriv j (u ∘ e) x)]


theorem contMDiffOn_laplacian_of_isOpen [T3Space M]
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U) {u : M → ℝ}
    (hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u U) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (D.laplacian u) U := by
  intro x hx
  obtain ⟨v, hv, -, -, hvu⟩ := exists_compact_smooth_germ hU hu hx
  have hlocal : D.laplacian u =ᶠ[𝓝 x] D.laplacian v := by
    filter_upwards [hvu.eventually_nhds] with y hy
    have hy' : v =ᶠ[𝓝 y] u := hy
    exact D.laplacian_eq_of_eventuallyEq hy'.symm
  exact ((D.contMDiff_laplacian hv x).congr_of_eventuallyEq hlocal).contMDiffWithinAt

theorem contMDiffOn_iterate_laplacian [T3Space M]
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U) {u : M → ℝ}
    (hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u U) (j : ℕ) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ ((D.laplacian)^[j] u) U := by
  induction j with
  | zero => exact hu
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact contMDiffOn_laplacian_of_isOpen D hU ih



theorem iterate_secondOrderOperator_coordinate_eq_laplacian [T3Space M]
    (D : LeviCivitaData g) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {U : Set M} (hU : IsOpen U) {u : M → ℝ}
    (hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u U)
    {V : Set E} (hV : IsOpen V) (hVs : V ⊆ e.source) (hVU : e '' V ⊆ U) (j : ℕ) :
    EqOn ((secondOrderOperator (coordinatePrincipalCoefficients g e)
      (coordinateDriftCoefficients g e))^[j] (u ∘ e))
      (fun x => ((D.laplacian)^[j] u) (e x)) V := by
  induction j with
  | zero => intro x hx; rfl
  | succ j ih =>
      intro x hx
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hlocal : ((secondOrderOperator (coordinatePrincipalCoefficients g e)
          (coordinateDriftCoefficients g e))^[j] (u ∘ e)) =ᶠ[𝓝 x]
          (fun y => ((D.laplacian)^[j] u) (e y)) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨V, hV.mem_nhds hx, ih⟩
      rw [secondOrderOperator_eq_of_eventuallyEq _ _ hlocal]
      exact secondOrderOperator_coordinate_eq_laplacian D e he hei hU
        (contMDiffOn_iterate_laplacian D hU hu j) (hVs hx) (hVU (mem_image_of_mem e hx))

open MeasureTheory



theorem eventually_eLpNorm_coordinateOperator_powers_exhaustion_bound
    [NeZero n] [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    (D : LeviCivitaData g) (hn : 0 < n) (hc : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M}
    (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    (O : M) {R : ℝ} (hR : 1 ≤ R) {a b : ℝ} (ha : 0 < a)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {V : Set E} (hVo : IsOpen V)
    (hVcl : IsCompact (closure V)) (hVcls : closure V ⊆ e.source) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ q in atTop, ∀ j t, t ∈ Icc a b →
      ∀ y, (g.edist O y).toReal ≤ R →
        MemLp ((secondOrderOperator (coordinatePrincipalCoefficients g e)
          (coordinateDriftCoefficients g e))^[j]
          (fun z => heatKernelContinuousTime D (S q) t (e z) y)) 2
            (volume.restrict V) ∧
        (eLpNorm ((secondOrderOperator (coordinatePrincipalCoefficients g e)
          (coordinateDriftCoefficients g e))^[j]
          (fun z => heatKernelContinuousTime D (S q) t (e z) y)) 2
            (volume.restrict V)).toReal ≤ ((j.factorial : ℝ) / (a / 2) ^ j) * B := by
  obtain ⟨B, hB, hbound⟩ :=
    eventually_eLpNorm_coordinate_laplacian_powers_exhaustion_bound
      D hn hc hk hRic S hΩmono hcover O hR ha e he hei hVo hVcl hVcls
  have hcompact : IsCompact (e '' closure V) :=
    hVcl.image_of_continuousOn (e.continuousOn.mono hVcls)
  obtain ⟨q₀, hq₀⟩ := hcompact.elim_directed_cover Ω (fun q => (S q).isOpen)
    (by rw [hcover]; exact subset_univ _) hΩmono.directed_le
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop q₀] with q hqbound hq
  intro j t ht y hy
  have htpos := ha.trans_le ht.1
  have hVdomain : e '' V ⊆ Ω q :=
    (image_mono subset_closure).trans (hq₀.trans (hΩmono hq))
  have hK : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => heatKernelContinuousTime D (S q) t x y) (Ω q) := by
    simp only [heatKernelContinuousTime_of_pos D (S q) htpos]
    exact contMDiffOn_heatKernelContinuous_left D (S q) t htpos y
  have heq := iterate_secondOrderOperator_coordinate_eq_laplacian D e he hei
    (S q).isOpen hK hVo (subset_closure.trans hVcls) hVdomain j
  have hae : ((secondOrderOperator (coordinatePrincipalCoefficients g e)
      (coordinateDriftCoefficients g e))^[j]
      (fun z => heatKernelContinuousTime D (S q) t (e z) y)) =ᵐ[volume.restrict V]
      (fun z => ((D.laplacian)^[j]
        (fun x => heatKernelContinuousTime D (S q) t x y)) (e z)) := by
    filter_upwards [ae_restrict_mem hVo.measurableSet] with z hz
    exact heq hz
  obtain ⟨hmem, hnorm⟩ := hqbound j t ht y hy
  refine ⟨(memLp_congr_ae hae).mpr hmem, ?_⟩
  rw [eLpNorm_congr_ae hae]
  exact hnorm

end PoincareConjecture.LeviCivitaData.Dirichlet
