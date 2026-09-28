import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Hessian
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberOpen
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle Topology BigOperators InnerProductSpace

namespace PoincareConjecture.RiemannianMetric

variable {m k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
  [IsManifold (𝓡 (m + k)) ∞ M]
  {f : M → Fin k → ℝ}
  (hf : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f) (U : Opens M)
  (hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f x))
  (c : Fin k → ℝ)

local instance fiberHessian_ambient_finrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
  ⟨finrank_euclideanSpace_fin⟩



theorem exists_normal_hessian_correction_openRegularFiberMetric
    {g : RiemannianMetric (m + k) M} (D : LeviCivitaData g)
    (x : openFiber f U c) (u v : EuclideanSpace ℝ (Fin m)) :
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    let D' := (openRegularFiberMetric hf U hreg c g).leviCivitaData
    ∃ B : TangentSpace (𝓡 (m + k)) (openFiberIncl f U c x),
      (∀ w : TangentSpace (𝓡 m) x,
        g.inner (openFiberIncl f U c x) B
          (mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x w) = 0) ∧
      (∀ i : Fin k, g.inner (openFiberIncl f U c x)
        (D.gradient (fun y => f y i) (openFiberIncl f U c x)) B =
          -D.hessian (fun y => f y i) (openFiberIncl f U c x)
            (mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x u)
            (mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x v)) ∧
      ∀ (φ : M → ℝ), ContMDiffAt (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ φ (openFiberIncl f U c x) →
        D'.hessian (φ ∘ openFiberIncl f U c) x u v =
          D.hessian φ (openFiberIncl f U c x)
            (mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x u)
            (mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x v) +
          g.inner (openFiberIncl f U c x) (D.gradient φ (openFiberIncl f U c x)) B := by
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let D' := (openRegularFiberMetric hf U hreg c g).leviCivitaData
  change ∃ B : TangentSpace (𝓡 (m + k)) (openFiberIncl f U c x), _
  obtain ⟨B, hn, hB⟩ := Induced.exists_normal_hessian_correction D D'
    (contMDiff_openFiberIncl hf U hreg c) x
    (Filter.Eventually.of_forall (openRegularFiberMetric_inner hf U hreg c g)) u v
  refine ⟨B, hn, ?_, hB⟩
  intro i
  have he : ((fun y => f y i) ∘ openFiberIncl f U c) = fun _ => c i := by
    funext z
    exact congrFun z.2 i
  have hi := hB (fun y => f y i)
    ((contMDiff_pi_space.mp hf i) (openFiberIncl f U c x))
  rw [he] at hi
  have hz : D'.hessian (fun _ => c i) x u v = 0 := by
    simp only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
      mvfderiv_const, zero_apply, sub_zero]
  rw [hz] at hi
  linarith




theorem exists_hessian_restriction_coefficients_openRegularFiberMetric
    {g : RiemannianMetric (m + k) M} (D : LeviCivitaData g)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ φ)
    (x : openFiber f U c) :
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    let h := openRegularFiberMetric hf U hreg c g
    ∃ a : Fin k → ℝ,
      g.gradient φ (openFiberIncl f U c x) =
        mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x
          (h.gradient (φ ∘ openFiberIncl f U c) x) +
        ∑ i, a i • g.gradient (fun y => f y i) (openFiberIncl f U c x) ∧
      ∀ u v : TangentSpace (𝓡 m) x,
        h.leviCivitaData.hessian (φ ∘ openFiberIncl f U c) x u v =
          D.hessian φ (openFiberIncl f U c x)
            (mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x u)
            (mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x v) -
          ∑ i, a i * D.hessian (fun y => f y i) (openFiberIncl f U c x)
            (mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x u)
            (mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x v) := by
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let h := openRegularFiberMetric hf U hreg c g
  let p := openFiberIncl f U c x
  let dι := mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl f U c) x
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + k)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 (m + k)) p) := by
    unfold TangentSpace
    infer_instance
  let S := Submodule.span ℝ (Set.range (fun i : Fin k => g.gradient (fun y => f y i) p))
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (S.starProjection_apply_mem (g.gradient φ p))
  have ht : dι (h.gradient (φ ∘ openFiberIncl f U c) x) =
      Sᗮ.starProjection (g.gradient φ p) :=
    mfderiv_gradient_openRegularFiberMetric hf U hreg c g hφ x
  have hg : g.gradient φ p = dι (h.gradient (φ ∘ openFiberIncl f U c) x) +
      ∑ i, a i • g.gradient (fun y => f y i) p := by
    rw [ht, ha]
    exact (S.starProjection_add_starProjection_orthogonal (g.gradient φ p)).symm.trans
      (add_comm _ _)
  change ∃ a : Fin k → ℝ, _
  refine ⟨a, hg, ?_⟩
  intro u v
  obtain ⟨B, hn, hfi, hB⟩ :=
    exists_normal_hessian_correction_openRegularFiberMetric hf U hreg c D x u v
  have hcorr : g.inner p (D.gradient φ p) B =
      -∑ i, a i * D.hessian (fun y => f y i) p (dι u) (dι v) := by
    change g.inner p (g.gradient φ p) B = _
    rw [hg]
    simp only [map_add, add_apply, map_sum, sum_apply, map_smul,
      smul_apply, smul_eq_mul]
    have hn' : g.inner p (dι (h.gradient (φ ∘ openFiberIncl f U c) x)) B = 0 := by
      rw [g.symm]
      exact hn _
    rw [hn', zero_add, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change a i * g.inner p (D.gradient (fun y => f y i) p) B = _
    rw [hfi]
    ring
  have hh := hB φ (hφ p)
  rw [hcorr] at hh
  exact hh

end PoincareConjecture.RiemannianMetric
