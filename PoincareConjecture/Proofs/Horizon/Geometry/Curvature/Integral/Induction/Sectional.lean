import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.RegularLevelScalar

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open Poincare.Geometry.Curvature.Hypersurface
open scoped Manifold ContDiff Bundle Topology InnerProductSpace BigOperators

namespace PoincareConjecture.LeviCivitaData

private theorem exists_orthonormalBasis_adjoin
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (L : V →ₗ[ℝ] W) (hL : ∀ u v, ⟪L u, L v⟫_ℝ = ⟪u, v⟫_ℝ)
    (N : W) (hN : ⟪N, N⟫_ℝ = 1) (hNT : ∀ u, ⟪N, L u⟫_ℝ = 0)
    (hdim : Module.finrank ℝ W = Fintype.card ι + 1) :
    ∃ B : OrthonormalBasis (Option ι) ℝ W,
      B none = N ∧ ∀ i, B (some i) = L (b i) := by
  classical
  let v : Option ι → W := fun i => i.elim N (fun j => L (b j))
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    cases i with
    | none =>
      cases j with
      | none => exact hN
      | some j => exact hNT (b j)
    | some i =>
      cases j with
      | none => exact (real_inner_comm _ _).trans (hNT (b i))
      | some j => simpa only [v, Option.elim_some, hL, Option.some.injEq]
          using b.inner_eq_ite i j
  have hcard : Fintype.card (Option ι) = Module.finrank ℝ W := by
    simpa using hdim.symm
  let a := basisOfOrthonormalOfCardEqFinrank hv hcard
  have ha : Orthonormal ℝ a := by simpa [a] using hv
  refine ⟨a.toOrthonormalBasis ha, ?_, ?_⟩ <;> simp [a, v]

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
  [IsManifold (𝓡 (m + 2)) ∞ M]
  {g : RiemannianMetric (m + 2) M}

theorem regularLevel_sectionalCurvature_lower_bound
    (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
    (U : Opens M)
    (hreg : ∀ x ∈ U, mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0)
    (c K β : ℝ) (hβ : 0 ≤ β) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U hreg (m + 1) c
    letI := isManifold_openLevelSet hf U hreg (m + 1) c
    ∀ (D' : LeviCivitaData (RiemannianMetric.regularLevelMetric hf U hreg c g))
      (z : openLevelSet f U c),
      (∀ a b : TangentSpace (𝓡 (m + 2)) (openLevelIncl f U c z),
        g.inner (openLevelIncl f U c z) a a = 1 →
        g.inner (openLevelIncl f U c z) b b = 1 →
        g.inner (openLevelIncl f U c z) a b = 0 →
        -K ≤ D.sectionalCurvature (openLevelIncl f U c z) a b) →
      (∀ w : TangentSpace (𝓡 (m + 1)) z,
        D.hessian f (openLevelIncl f U c z)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U c) z w)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U c) z w) /
          Real.sqrt (D.levelQ f (openLevelIncl f U c z)) ≤
        β * (RiemannianMetric.regularLevelMetric hf U hreg c g).inner z w w) →
      ∀ u v : TangentSpace (𝓡 (m + 1)) z,
        (RiemannianMetric.regularLevelMetric hf U hreg c g).inner z u u = 1 →
        (RiemannianMetric.regularLevelMetric hf U hreg c g).inner z v v = 1 →
        (RiemannianMetric.regularLevelMetric hf U hreg c g).inner z u v = 0 →
        -K - (max 0 (-D.levelMeanCurvature f (openLevelIncl f U c z)) +
          ((m + 1 : ℕ) : ℝ) * β) * β ≤ D'.sectionalCurvature z u v := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
    ⟨finrank_euclideanSpace_fin⟩
  letI := openLevelSetChartedSpace hf U hreg (m + 1) c
  letI := isManifold_openLevelSet hf U hreg (m + 1) c
  intro D' z hambient hhess u v hu hv huv
  let h := RiemannianMetric.regularLevelMetric hf U hreg c g
  let x := openLevelIncl f U c z
  let N := D.levelUnitNormal f x
  let S := D.regularLevelNormalShapeOperator hf U hreg c z
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 2)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 (m + 1)) : openLevelSet f U c → Type _) :=
    ⟨h.toRiemannianMetric⟩
  have hdf : mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0 :=
    hreg x (z.1 : U).property
  have hgrad : D.gradient f x ≠ 0 := by
    intro hz
    exact hdf ((g.gradient_eq_zero_iff_mfderiv_eq_zero f x).mp hz)
  have hQ : 0 < D.levelQ f x := real_inner_self_pos.mpr hgrad
  have hN : g.inner x N N = 1 := by
    have hs := Real.sq_sqrt hQ.le
    have hr := (Real.sqrt_pos.2 hQ).ne'
    change g.inner x ((Real.sqrt (D.levelQ f x))⁻¹ • D.gradient f x)
      ((Real.sqrt (D.levelQ f x))⁻¹ • D.gradient f x) = 1
    simp only [map_smul, smul_apply, smul_eq_mul]
    change (Real.sqrt (D.levelQ f x))⁻¹ *
      ((Real.sqrt (D.levelQ f x))⁻¹ * D.levelQ f x) = 1
    field_simp
    exact hs.symm
  let L : TangentSpace (𝓡 (m + 1)) z →ₗ[ℝ] TangentSpace (𝓡 (m + 2)) x :=
    (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U c) z).toLinearMap
  have hnormal (w : TangentSpace (𝓡 (m + 1)) z) : g.inner x N (L w) = 0 := by
    have hrange := range_mfderiv_openLevelIncl hf U hreg (m + 1) c z
    have hw : L w ∈ (mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x).ker := by
      rw [← hrange]
      exact ⟨w, rfl⟩
    change mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x (L w) = 0 at hw
    have hi : g.inner x (D.gradient f x) (L w) = 0 := by
      rw [D.inner_gradient]
      have hw' := congrArg (fun q => NormedSpace.fromTangentSpace (f x) q) hw
      convert hw' using 1 <;>
        simp only [mvfderiv, ContinuousLinearMap.coe_comp, Function.comp_apply,
          map_zero] <;> rfl
    change g.inner x ((Real.sqrt (D.levelQ f x))⁻¹ • D.gradient f x) (L w) = 0
    simp only [map_smul, smul_apply, smul_eq_mul, hi, mul_zero]
  have hpair (a b : TangentSpace (𝓡 (m + 1)) z) :
      h.inner z (S a) b = D.hessian f x (L a) (L b) / Real.sqrt (D.levelQ f x) :=
    D.regularLevelNormalShapeOperator_inner hf U hreg c D' z a b
  have hupper : ∀ κ, Module.End.HasEigenvalue S κ → κ ≤ β := by
    intro κ hκ
    obtain ⟨w, hw⟩ := hκ.exists_hasEigenvector
    have hwpos : 0 < h.inner z w w := real_inner_self_pos.mpr hw.2
    have hbound := hhess w
    change D.hessian f x (L w) (L w) / Real.sqrt (D.levelQ f x) ≤
      β * h.inner z w w at hbound
    rw [← hpair w w, hw.apply_eq_smul] at hbound
    simp only [map_smul, smul_apply, smul_eq_mul] at hbound
    exact (mul_le_mul_iff_left₀ hwpos).mp hbound
  let b := h.orthonormalBasis z
  have hL (a b : TangentSpace (𝓡 (m + 1)) z) : ⟪L a, L b⟫_ℝ = ⟪a, b⟫_ℝ :=
    (RiemannianMetric.regularLevelMetric_inner hf U hreg c g z a b).symm
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 (m + 2)) x) =
      Fintype.card (Fin (Module.finrank ℝ (TangentSpace (𝓡 (m + 1)) z))) + 1 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) =
      Fintype.card (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1)))) ) + 1
    simp
  obtain ⟨B, hB0, hBi⟩ := exists_orthonormalBasis_adjoin b L hL N hN hnormal hdim
  let A := D.connection (D.gradient f) x
  let traceForm : TangentSpace (𝓡 (m + 2)) x →ₗ[ℝ]
      TangentSpace (𝓡 (m + 2)) x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun a b => ⟪A a, b⟫_ℝ)
      (by intros; simp only [map_add, inner_add_left])
      (by intros; simp only [map_smul, real_inner_smul_left, smul_eq_mul])
      (by intros; exact inner_add_right ..)
      (by intros; exact real_inner_smul_right ..)
  have hlap : D.laplacian f x = D.hessian f x N N +
      ∑ i, D.hessian f x (L (b i)) (L (b i)) := by
    have hinner (a b : TangentSpace (𝓡 (m + 2)) x) :
        ⟪a, b⟫_ℝ = g.inner x a b := rfl
    have ht := bilinear_sum_orthonormalBasis_eq traceForm (g.orthonormalBasis x) B
    rw [D.laplacian_eq_sum_inner_connection_gradient (hf x)]
    simpa only [traceForm, LinearMap.mk₂_apply, Fintype.sum_option, hB0, hBi,
      D.hessian_eq_inner_connection_gradient (hf x), hinner, A] using ht
  have hmean : D.levelMeanCurvature f x =
      ∑ i, D.hessian f x (L (b i)) (L (b i)) / Real.sqrt (D.levelQ f x) := by
    have ht := D.hessian_mean_curvature hf x hQ
    change D.levelMeanCurvature f x =
      (D.laplacian f x - D.hessian f x N N) / Real.sqrt (D.levelQ f x) at ht
    rw [hlap, add_sub_cancel_left, Finset.sum_div] at ht
    exact ht
  have htrace : S.trace ℝ (TangentSpace (𝓡 (m + 1)) z) =
      D.levelMeanCurvature f x := by
    rw [LinearMap.trace_eq_sum_inner S b, hmean]
    apply Finset.sum_congr rfl
    intro i _
    exact (real_inner_comm _ _).trans (hpair (b i) (b i))
  have hb := sectionalCurvature_lower_bound_of_normal_curvatures g h D D'
    (contMDiff_openLevelIncl hf U hreg (m + 1) c) z
    (Filter.Eventually.of_forall (RiemannianMetric.regularLevelMetric_inner hf U hreg c g))
    N hN hnormal K β hβ hambient hupper u v hu hv huv
  change -K - (negativePart (S.trace ℝ (TangentSpace (𝓡 (m + 1)) z)) +
    ((m + 1 : ℕ) : ℝ) * β) * β ≤ D'.sectionalCurvature z u v at hb
  rw [htrace] at hb
  exact hb

end PoincareConjecture.LeviCivitaData
