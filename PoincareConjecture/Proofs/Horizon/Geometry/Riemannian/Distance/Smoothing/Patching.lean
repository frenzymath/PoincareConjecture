import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Locality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {ι : Type*}

theorem hessian_finset_sum_at (D : LeviCivitaData g) (s : Finset ι)
    (f : ι → M → ℝ) {x : M}
    (hf : ∀ i ∈ s, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) x)
    (u v : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => ∑ i ∈ s, f i y) x u v =
      ∑ i ∈ s, D.hessian (f i) x u v := by
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  have hY := FiberBundle.contMDiffAt_extend (𝓡 n)
    (EuclideanSpace ℝ (Fin n)) (k := ∞) v
  have hnear : ∀ᶠ y in 𝓝 x, ∀ i ∈ s,
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (f i) y := by
    apply (Filter.eventually_all_finset s).mpr
    intro i hi
    have hn := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
      ((hf i hi).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
    exact hn.mono fun y hy => hy.mdifferentiableAt (by simp)
  have he : (fun y => mvfderiv (𝓡 n) (fun z => ∑ i ∈ s, f i z) y (Y y)) =ᶠ[𝓝 x]
      (fun y => ∑ i ∈ s, mvfderiv (𝓡 n) (f i) y (Y y)) := by
    filter_upwards [hnear] with y hy
    exact Poincare.mvfderiv_finset_sum s f y (Y y) hy
  have hdiff (i : ι) (hi : i ∈ s) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => mvfderiv (𝓡 n) (f i) y (Y y)) x := by
    have hd := ((hf i hi).mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates
      hY (hf i hi)
    rw [Bundle.contMDiffAt_totalSpace] at hd
    apply ContMDiffAt.mdifferentiableAt (n := ∞) _ (by simp)
    convert hd.2 using 1
    funext y
    simp only [mvfderiv, ContinuousLinearMap.comp_apply]
    simp
    rfl
  simp only [hessian, hessianOnFields, FiberBundle.extend_apply_self]
  change mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) (fun z => ∑ i ∈ s, f i z) y (Y y)) x u -
      mvfderiv (𝓡 n) (fun y => ∑ i ∈ s, f i y) x (D.connection Y x u) = _
  rw [Poincare.mvfderiv_eq_of_eventuallyEq he,
    Poincare.mvfderiv_finset_sum s _ x u hdiff,
    Poincare.mvfderiv_finset_sum s f x (D.connection Y x u)
      (fun i hi => (hf i hi).mdifferentiableAt (by simp)), Finset.sum_sub_distrib]

omit [IsManifold (𝓡 n) ∞ M] in

theorem sum_mvfderiv_eq_zero_of_sum_eq_one_near (s : Finset ι) (ψ : ι → M → ℝ)
    {x : M} (hψ : ∀ i ∈ s, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (ψ i) x)
    (hone : (fun y => ∑ i ∈ s, ψ i y) =ᶠ[𝓝 x] fun _ => (1 : ℝ))
    (u : TangentSpace (𝓡 n) x) :
    (∑ i ∈ s, mvfderiv (𝓡 n) (ψ i) x u) = 0 := by
  rw [← Poincare.mvfderiv_finset_sum s ψ x u
    (fun i hi => (hψ i hi).mdifferentiableAt (by simp)),
    Poincare.mvfderiv_eq_of_eventuallyEq hone, mvfderiv_const]
  rfl

theorem sum_hessian_eq_zero_of_sum_eq_one_near (D : LeviCivitaData g)
    (s : Finset ι) (ψ : ι → M → ℝ) {x : M}
    (hψ : ∀ i ∈ s, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (ψ i) x)
    (hone : (fun y => ∑ i ∈ s, ψ i y) =ᶠ[𝓝 x] fun _ => (1 : ℝ))
    (u v : TangentSpace (𝓡 n) x) :
    (∑ i ∈ s, D.hessian (ψ i) x u v) = 0 := by
  rw [← D.hessian_finset_sum_at s ψ hψ u v, D.hessian_eq_of_eventuallyEq hone]
  simp only [hessian, hessianOnFields, mvfderiv_const, zero_apply, sub_zero]

theorem hessian_finset_patch_eq (D : LeviCivitaData g) (s : Finset ι)
    (ψ f : ι → M → ℝ) {x : M}
    (hψ : ∀ i ∈ s, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (ψ i) x)
    (hf : ∀ i ∈ s, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) x)
    (hone : (fun y => ∑ i ∈ s, ψ i y) =ᶠ[𝓝 x] fun _ => (1 : ℝ))
    (a : ℝ) (ℓ : TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    (u v : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => ∑ i ∈ s, ψ i y * f i y) x u v =
      ∑ i ∈ s, (ψ i x * D.hessian (f i) x u v +
        (f i x - a) * D.hessian (ψ i) x u v +
        mvfderiv (𝓡 n) (ψ i) x u * (mvfderiv (𝓡 n) (f i) x v - ℓ v) +
        (mvfderiv (𝓡 n) (f i) x u - ℓ u) * mvfderiv (𝓡 n) (ψ i) x v) := by
  rw [D.hessian_finset_sum_at s (fun i y => ψ i y * f i y)
    (fun i hi => (hψ i hi).mul (hf i hi)) u v]
  have hp : (∑ i ∈ s, D.hessian (fun y => ψ i y * f i y) x u v) =
      ∑ i ∈ s, (ψ i x * D.hessian (f i) x u v + f i x * D.hessian (ψ i) x u v +
        mvfderiv (𝓡 n) (ψ i) x u * mvfderiv (𝓡 n) (f i) x v +
        mvfderiv (𝓡 n) (f i) x u * mvfderiv (𝓡 n) (ψ i) x v) := by
    exact Finset.sum_congr rfl fun i hi => D.hessian_mul_at (hψ i hi) (hf i hi) u v
  rw [hp]
  have hH := D.sum_hessian_eq_zero_of_sum_eq_one_near s ψ hψ hone u v
  have hdu := sum_mvfderiv_eq_zero_of_sum_eq_one_near s ψ hψ hone u
  have hdv := sum_mvfderiv_eq_zero_of_sum_eq_one_near s ψ hψ hone v
  simp only [sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, hH, hdu, hdv, mul_zero, zero_mul, sub_zero]

theorem hessian_finset_patch_le (D : LeviCivitaData g) (s : Finset ι)
    (ψ f : ι → M → ℝ) {x : M}
    (hψ : ∀ i ∈ s, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (ψ i) x)
    (hf : ∀ i ∈ s, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) x)
    (hone : (fun y => ∑ i ∈ s, ψ i y) =ᶠ[𝓝 x] fun _ => (1 : ℝ))
    (hnonneg : ∀ i ∈ s, 0 ≤ ψ i x)
    (a C : ℝ) (ℓ : TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    (v : TangentSpace (𝓡 n) x)
    (hH : ∀ i ∈ s, D.hessian (f i) x v v ≤ C * g.inner x v v) :
    D.hessian (fun y => ∑ i ∈ s, ψ i y * f i y) x v v ≤
      C * g.inner x v v + ∑ i ∈ s,
        (|f i x - a| * |D.hessian (ψ i) x v v| +
          2 * |mvfderiv (𝓡 n) (ψ i) x v| * |mvfderiv (𝓡 n) (f i) x v - ℓ v|) := by
  rw [D.hessian_finset_patch_eq s ψ f hψ hf hone a ℓ v v]
  calc
    _ ≤ ∑ i ∈ s, (ψ i x * (C * g.inner x v v) +
        (|f i x - a| * |D.hessian (ψ i) x v v| +
          2 * |mvfderiv (𝓡 n) (ψ i) x v| * |mvfderiv (𝓡 n) (f i) x v - ℓ v|)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hmain := mul_le_mul_of_nonneg_left (hH i hi) (hnonneg i hi)
      have hvalue : (f i x - a) * D.hessian (ψ i) x v v ≤
          |f i x - a| * |D.hessian (ψ i) x v v| := by
        simpa only [abs_mul] using le_abs_self ((f i x - a) * D.hessian (ψ i) x v v)
      have hderiv : mvfderiv (𝓡 n) (ψ i) x v * (mvfderiv (𝓡 n) (f i) x v - ℓ v) ≤
          |mvfderiv (𝓡 n) (ψ i) x v| * |mvfderiv (𝓡 n) (f i) x v - ℓ v| := by
        simpa only [abs_mul] using le_abs_self
          (mvfderiv (𝓡 n) (ψ i) x v * (mvfderiv (𝓡 n) (f i) x v - ℓ v))
      nlinarith
    _ = _ := by
      have hx : (∑ i ∈ s, ψ i x) = 1 := hone.self_of_nhds
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hx, one_mul]

theorem hessian_finset_patch_le_of_error_bounds (D : LeviCivitaData g) (s : Finset ι)
    (ψ f : ι → M → ℝ) {x : M}
    (hψ : ∀ i ∈ s, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (ψ i) x)
    (hf : ∀ i ∈ s, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) x)
    (hone : (fun y => ∑ i ∈ s, ψ i y) =ᶠ[𝓝 x] fun _ => (1 : ℝ))
    (hnonneg : ∀ i ∈ s, 0 ≤ ψ i x)
    (a C : ℝ) (ℓ : TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    (ε η P Q : ι → ℝ)
    (hε : ∀ i ∈ s, 0 ≤ ε i) (hP : ∀ i ∈ s, 0 ≤ P i)
    (hvalue : ∀ i ∈ s, |f i x - a| ≤ ε i)
    (hfirst : ∀ i ∈ s, ∀ v : TangentSpace (𝓡 n) x,
      |mvfderiv (𝓡 n) (f i) x v - ℓ v| ≤ η i * g.tangentNorm x v)
    (hψfirst : ∀ i ∈ s, ∀ v : TangentSpace (𝓡 n) x,
      |mvfderiv (𝓡 n) (ψ i) x v| ≤ P i * g.tangentNorm x v)
    (hψsecond : ∀ i ∈ s, ∀ v : TangentSpace (𝓡 n) x,
      |D.hessian (ψ i) x v v| ≤ Q i * g.inner x v v)
    (hH : ∀ i ∈ s, ∀ v : TangentSpace (𝓡 n) x,
      D.hessian (f i) x v v ≤ C * g.inner x v v)
    (v : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => ∑ i ∈ s, ψ i y * f i y) x v v ≤
      (C + ∑ i ∈ s, (ε i * Q i + 2 * P i * η i)) * g.inner x v v := by
  have hq : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hN : 0 ≤ g.tangentNorm x v := Real.sqrt_nonneg _
  have hNN : g.tangentNorm x v * g.tangentNorm x v = g.inner x v v :=
    Real.mul_self_sqrt hq
  apply (D.hessian_finset_patch_le s ψ f hψ hf hone hnonneg a C ℓ v
    (fun i hi => hH i hi v)).trans
  calc
    _ ≤ C * g.inner x v v +
        ∑ i ∈ s, (ε i * Q i + 2 * P i * η i) * g.inner x v v := by
      apply add_le_add le_rfl (Finset.sum_le_sum _)
      intro i hi
      have hval := mul_le_mul (hvalue i hi) (hψsecond i hi v)
        (abs_nonneg _) (hε i hi)
      have hder := mul_le_mul (hψfirst i hi v) (hfirst i hi v)
        (abs_nonneg _) (mul_nonneg (hP i hi) hN)
      have hder' := mul_le_mul_of_nonneg_left hder (by norm_num : (0 : ℝ) ≤ 2)
      calc
        _ ≤ ε i * (Q i * g.inner x v v) +
            2 * (P i * g.tangentNorm x v * (η i * g.tangentNorm x v)) := by
          nlinarith only [hval, hder']
        _ = _ := by
          calc
            _ = (ε i * Q i) * g.inner x v v +
                (2 * P i * η i) * (g.tangentNorm x v * g.tangentNorm x v) := by ring
            _ = _ := by rw [hNN]; ring
    _ = _ := by rw [← Finset.sum_mul]; ring

omit [IsManifold (𝓡 n) ∞ M] in
private theorem partition_patch_eq_finset_near (ρ : SmoothPartitionOfUnity ι (𝓡 n) M)
    (f : ι → M → ℝ) (x : M) :
    (fun y => ∑ᶠ i, ρ i y * f i y) =ᶠ[𝓝 x]
      (fun y => ∑ i ∈ ρ.fintsupport x, ρ i y * f i y) := by
  classical
  filter_upwards [ρ.eventually_finsupport_subset x] with y hy
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply hy
  rw [ρ.mem_finsupport]
  exact (mul_ne_zero_iff.mp hi).1

omit [IsManifold (𝓡 n) ∞ M] in
private theorem partition_sum_eq_one_near (ρ : SmoothPartitionOfUnity ι (𝓡 n) M)
    (x : M) :
    (fun y => ∑ i ∈ ρ.fintsupport x, ρ i y) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
  filter_upwards [ρ.eventually_finsupport_subset x] with y hy
  exact ρ.sum_finsupport' y (Set.mem_univ y) hy

theorem hessian_partition_mul_eq (D : LeviCivitaData g)
    (ρ : SmoothPartitionOfUnity ι (𝓡 n) M) (f : ι → M → ℝ) (x : M)
    (hf : ∀ i, x ∈ tsupport (ρ i) → ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) x)
    (a : ℝ) (ℓ : TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    (u v : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => ∑ᶠ i, ρ i y * f i y) x u v =
      ∑ i ∈ ρ.fintsupport x, (ρ i x * D.hessian (f i) x u v +
        (f i x - a) * D.hessian (ρ i) x u v +
        mvfderiv (𝓡 n) (ρ i) x u * (mvfderiv (𝓡 n) (f i) x v - ℓ v) +
        (mvfderiv (𝓡 n) (f i) x u - ℓ u) * mvfderiv (𝓡 n) (ρ i) x v) := by
  rw [D.hessian_eq_of_eventuallyEq (partition_patch_eq_finset_near ρ f x)]
  exact D.hessian_finset_patch_eq (ρ.fintsupport x) (fun i => ρ i) f
    (fun i _ => (ρ i).contMDiff x)
    (fun i hi => hf i ((ρ.mem_fintsupport_iff x i).mp hi))
    (partition_sum_eq_one_near ρ x) a ℓ u v

theorem hessian_partition_mul_le_of_error_bounds (D : LeviCivitaData g)
    (ρ : SmoothPartitionOfUnity ι (𝓡 n) M) (f : ι → M → ℝ) (x : M)
    (hf : ∀ i, x ∈ tsupport (ρ i) → ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) x)
    (a C : ℝ) (ℓ : TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    (ε η P Q : ι → ℝ)
    (hε : ∀ i, x ∈ tsupport (ρ i) → 0 ≤ ε i)
    (hP : ∀ i, x ∈ tsupport (ρ i) → 0 ≤ P i)
    (hvalue : ∀ i, x ∈ tsupport (ρ i) → |f i x - a| ≤ ε i)
    (hfirst : ∀ i, x ∈ tsupport (ρ i) → ∀ v : TangentSpace (𝓡 n) x,
      |mvfderiv (𝓡 n) (f i) x v - ℓ v| ≤ η i * g.tangentNorm x v)
    (hψfirst : ∀ i, x ∈ tsupport (ρ i) → ∀ v : TangentSpace (𝓡 n) x,
      |mvfderiv (𝓡 n) (ρ i) x v| ≤ P i * g.tangentNorm x v)
    (hψsecond : ∀ i, x ∈ tsupport (ρ i) → ∀ v : TangentSpace (𝓡 n) x,
      |D.hessian (ρ i) x v v| ≤ Q i * g.inner x v v)
    (hH : ∀ i, x ∈ tsupport (ρ i) → ∀ v : TangentSpace (𝓡 n) x,
      D.hessian (f i) x v v ≤ C * g.inner x v v)
    (v : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => ∑ᶠ i, ρ i y * f i y) x v v ≤
      (C + ∑ i ∈ ρ.fintsupport x, (ε i * Q i + 2 * P i * η i)) * g.inner x v v := by
  rw [D.hessian_eq_of_eventuallyEq (partition_patch_eq_finset_near ρ f x)]
  exact D.hessian_finset_patch_le_of_error_bounds (ρ.fintsupport x) (fun i => ρ i) f
    (fun i _ => (ρ i).contMDiff x)
    (fun i hi => hf i ((ρ.mem_fintsupport_iff x i).mp hi))
    (partition_sum_eq_one_near ρ x) (fun i _ => ρ.nonneg i x) a C ℓ ε η P Q
    (fun i hi => hε i ((ρ.mem_fintsupport_iff x i).mp hi))
    (fun i hi => hP i ((ρ.mem_fintsupport_iff x i).mp hi))
    (fun i hi => hvalue i ((ρ.mem_fintsupport_iff x i).mp hi))
    (fun i hi => hfirst i ((ρ.mem_fintsupport_iff x i).mp hi))
    (fun i hi => hψfirst i ((ρ.mem_fintsupport_iff x i).mp hi))
    (fun i hi => hψsecond i ((ρ.mem_fintsupport_iff x i).mp hi))
    (fun i hi => hH i ((ρ.mem_fintsupport_iff x i).mp hi)) v

end PoincareConjecture.LeviCivitaData
