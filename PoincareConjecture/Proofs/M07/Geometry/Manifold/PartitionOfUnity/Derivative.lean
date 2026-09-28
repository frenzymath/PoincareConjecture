import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.Instances.Real










set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators Topology

namespace Poincare

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {ι : Type*}


theorem mvfderiv_finset_sum (s : Finset ι) (f : ι → M → ℝ) (x : M)
    (v : TangentSpace (𝓡 n) x)
    (hf : ∀ i ∈ s, MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (f i) x) :
    mvfderiv (𝓡 n) (fun y ↦ ∑ i ∈ s, f i y) x v =
      ∑ i ∈ s, mvfderiv (𝓡 n) (f i) x v := by
  classical
  suffices MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun y ↦ ∑ i ∈ s, f i y) x ∧
      mvfderiv (𝓡 n) (fun y ↦ ∑ i ∈ s, f i y) x v =
        ∑ i ∈ s, mvfderiv (𝓡 n) (f i) x v from this.2
  induction s using Finset.induction_on with
  | empty => simpa [mvfderiv_const] using mdifferentiableAt_const (c := (0 : ℝ))
  | @insert i s hi ih =>
    obtain ⟨hs, hsum⟩ := ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
    have hfi := hf i (Finset.mem_insert_self _ _)
    simp only [Finset.sum_insert hi]
    refine ⟨hfi.add hs, ?_⟩
    rw [mvfderiv_fun_add hfi hs]
    simp only [add_apply, hsum]


theorem mvfderiv_eq_of_eventuallyEq {f h : M → ℝ} {x : M}
    (heq : f =ᶠ[𝓝 x] h) : mvfderiv (𝓡 n) f x = mvfderiv (𝓡 n) h x := by
  unfold mvfderiv
  rw [heq.mfderiv_eq]
  rw [heq.eq_of_nhds]


theorem sum_mvfderiv_partition_eq_zero (ρ : SmoothPartitionOfUnity ι (𝓡 n) M)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    ∑ i ∈ ρ.fintsupport x, mvfderiv (𝓡 n) (ρ i) x v = 0 := by
  rw [← mvfderiv_finset_sum _ _ x v (fun i _ ↦ (ρ i).contMDiff.mdifferentiable (by simp) x)]
  have heq : (fun y ↦ ∑ i ∈ ρ.fintsupport x, ρ i y) =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) := by
    filter_upwards [ρ.eventually_finsupport_subset x] with y hy
    exact ρ.sum_finsupport' y (Set.mem_univ y) hy
  rw [mvfderiv_eq_of_eventuallyEq heq, mvfderiv_const]
  rfl



theorem mvfderiv_partition_mul_eq (ρ : SmoothPartitionOfUnity ι (𝓡 n) M)
    (f : ι → M → ℝ) (x : M) (v : TangentSpace (𝓡 n) x) (a : ℝ)
    (hf : ∀ i, x ∈ tsupport (ρ i) → MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (f i) x) :
    mvfderiv (𝓡 n) (fun y ↦ ∑ᶠ i, ρ i y * f i y) x v =
      ∑ i ∈ ρ.fintsupport x,
        (ρ i x * mvfderiv (𝓡 n) (f i) x v +
          (f i x - a) * mvfderiv (𝓡 n) (ρ i) x v) := by
  classical
  have heq : (fun y ↦ ∑ᶠ i, ρ i y * f i y) =ᶠ[𝓝 x]
      (fun y ↦ ∑ i ∈ ρ.fintsupport x, ρ i y * f i y) := by
    filter_upwards [ρ.eventually_finsupport_subset x] with y hy
    apply finsum_eq_sum_of_support_subset
    intro i hi
    apply hy
    rw [ρ.mem_finsupport]
    exact (mul_ne_zero_iff.mp hi).1
  rw [mvfderiv_eq_of_eventuallyEq heq]
  rw [mvfderiv_finset_sum _ (fun i y ↦ ρ i y * f i y) x v (fun i hi ↦
    ((ρ i).contMDiff.mdifferentiable (by simp) x).mul
      (hf i ((ρ.mem_fintsupport_iff x i).mp hi)))]
  have hterm : ∀ i ∈ ρ.fintsupport x,
      mvfderiv (𝓡 n) (fun y ↦ ρ i y * f i y) x v =
        ρ i x * mvfderiv (𝓡 n) (f i) x v + f i x * mvfderiv (𝓡 n) (ρ i) x v := by
    intro i hi
    rw [mvfderiv_fun_mul ((ρ i).contMDiff.mdifferentiable (by simp) x)
      (hf i ((ρ.mem_fintsupport_iff x i).mp hi))]
    simp
  simp_rw [Finset.sum_congr rfl hterm]
  have hzero := sum_mvfderiv_partition_eq_zero ρ x v
  simp only [sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hzero, mul_zero, sub_zero]



theorem abs_partition_mul_sub_le (ρ : SmoothPartitionOfUnity ι (𝓡 n) M)
    (f : ι → M → ℝ) (x : M) (a ε : ℝ)
    (hf : ∀ i, x ∈ tsupport (ρ i) → |f i x - a| ≤ ε) :
    |(∑ᶠ i, ρ i x * f i x) - a| ≤ ε := by
  have hmem : (∑ᶠ i, ρ i x • f i x) ∈ Metric.closedBall a ε :=
    ρ.finsum_smul_mem_convex (Set.mem_univ x)
      (fun i hi ↦ by
        simpa only [Metric.mem_closedBall, Real.dist_eq] using
          hf i (subset_closure hi)) (convex_closedBall a ε)
  simpa only [smul_eq_mul, Metric.mem_closedBall, Real.dist_eq] using hmem



theorem abs_mvfderiv_partition_mul_le (ρ : SmoothPartitionOfUnity ι (𝓡 n) M)
    (f : ι → M → ℝ) (x : M) (v : TangentSpace (𝓡 n) x) (a L N : ℝ)
    (hf : ∀ i, x ∈ tsupport (ρ i) → MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (f i) x)
    (hd : ∀ i, x ∈ tsupport (ρ i) → |mvfderiv (𝓡 n) (f i) x v| ≤ L * N) :
    |mvfderiv (𝓡 n) (fun y ↦ ∑ᶠ i, ρ i y * f i y) x v| ≤
      L * N + ∑ i ∈ ρ.fintsupport x,
        |f i x - a| * |mvfderiv (𝓡 n) (ρ i) x v| := by
  rw [mvfderiv_partition_mul_eq ρ f x v a hf]
  calc
    |∑ i ∈ ρ.fintsupport x,
        (ρ i x * mvfderiv (𝓡 n) (f i) x v +
          (f i x - a) * mvfderiv (𝓡 n) (ρ i) x v)|
      ≤ ∑ i ∈ ρ.fintsupport x,
        |ρ i x * mvfderiv (𝓡 n) (f i) x v +
          (f i x - a) * mvfderiv (𝓡 n) (ρ i) x v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ ρ.fintsupport x,
        (ρ i x * (L * N) + |f i x - a| * |mvfderiv (𝓡 n) (ρ i) x v|) := by
      apply Finset.sum_le_sum
      intro i hi
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_mul, abs_of_nonneg (ρ.nonneg i x)]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hd i ((ρ.mem_fintsupport_iff x i).mp hi))
          (ρ.nonneg i x)) le_rfl
    _ = L * N + ∑ i ∈ ρ.fintsupport x,
        |f i x - a| * |mvfderiv (𝓡 n) (ρ i) x v| := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul,
        ρ.sum_finsupport' x (Set.mem_univ x) (ρ.finsupport_subset_fintsupport x), one_mul]

end Poincare
