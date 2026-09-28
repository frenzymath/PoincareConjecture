import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.CovariantSmooth
import PoincareConjecture.Proofs.M28.Mathlib.FiniteHessian.JetBounds










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.Proofs.M28.NeckAnalysis

open FiniteHessian

private theorem bounded_coordinate_sum {ι β : Type*} [Fintype β]
    {n : ℕ} {f : β → ι → RoundCylinderCoordinates → ℝ}
    {x : ι → RoundCylinderCoordinates}
    (hf : ∀ b, HasUniformJetBoundsAt n (f b) x)
    (hc : ∀ i b, ContDiffAt ℝ ∞ (f b i) (x i)) :
    HasUniformJetBoundsAt n (fun i p => ∑ b, f b i p) x := by
  classical
  intro j hj
  choose C hC using fun b => hf b j hj
  refine ⟨∑ b, C b, fun i => ?_⟩
  rw [iteratedFDeriv_fun_sum_apply (fun b _ =>
    (hc i b).of_le (by exact_mod_cast le_top))]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun b _ => hC b i))



theorem hasUniformJetBoundsAt_roundCylinderTensorDerivative
    {ι : Type*} {n r : ℕ} (u : ι → ℝ) (hu : ∀ i, u i < 1)
    (q : ι → UnitTwoSphere) (s : ι → ℝ)
    (T : ι → RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ)
    (hT : ∀ a, HasUniformJetBoundsAt (n + 1)
      (fun i p => T i p a) (fun i => (0, s i)))
    (hcT : ∀ i a, ContDiffAt ℝ ∞ (fun p => T i p a) (0, s i)) :
    ∀ a, HasUniformJetBoundsAt n (fun i p => roundCylinderTensorDerivative (u i)
      (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) (T i) p a)
      (fun i => (0, s i)) := by
  intro a
  have hd : HasUniformJetBoundsAt n
      (fun i => fderiv ℝ (fun p => T i p (fun b => a b.succ)))
      (fun i => (0, s i)) := by
    intro j hj
    obtain ⟨C, hC⟩ := hT (fun b => a b.succ) (j + 1) (by omega)
    refine ⟨C, fun i => ?_⟩
    simpa only [norm_iteratedFDeriv_fderiv] using hC i
  have hcD : ∀ i, ContDiffAt ℝ ∞
      (fderiv ℝ (fun p => T i p (fun b => a b.succ))) (0, s i) :=
    fun i => (hcT i _).fderiv_right (by simp)
  have hlead := hd.clm hcD
    (ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis (a 0)))
  have hleadC : ∀ i, ContDiffAt ℝ ∞ (fun p =>
      fderiv ℝ (fun y => T i y (fun b => a b.succ)) p
        (roundCylinderCoordinateBasis (a 0))) (0, s i) :=
    fun i => (hcD i).clm_apply contDiffAt_const
  let P := fun b : Fin r => fun c : Fin 3 => fun i p =>
    roundCylinderChristoffel (u i) (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) p
      c (a 0) (a b.succ) * T i p (Function.update (fun k => a k.succ) b c)
  have hcP : ∀ i b c, ContDiffAt ℝ ∞ (P b c i) (0, s i) := by
    intro i b c
    exact (contDiff_roundCylinderChristoffel (hu i) (q i) c (a 0) (a b.succ)).contDiffAt.mul
      (hcT i _)
  have hP : ∀ b c, HasUniformJetBoundsAt n (P b c) (fun i => (0, s i)) := by
    intro b c
    have hG : HasUniformJetBoundsAt n (fun i p => roundCylinderChristoffel (u i)
        (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) p c (a 0) (a b.succ))
        (fun i => (0, s i)) := by
      obtain ⟨C, _, hC⟩ := exists_bound_roundCylinderChristoffel_jets n
      exact fun j hj => ⟨C, fun i => hC (u i) (hu i) (q i) (s i) j hj c (a 0) (a b.succ)⟩
    exact hG.bilinear ((hT _).mono_order (Nat.le_succ n))
      (fun i => (contDiff_roundCylinderChristoffel (hu i) (q i) c
        (a 0) (a b.succ)).contDiffAt) (fun i => hcT i _)
      (ContinuousLinearMap.mul ℝ ℝ)
  have hsum := bounded_coordinate_sum
    (fun b => bounded_coordinate_sum (hP b) (fun i c => hcP i b c))
    (fun i b => ContDiffAt.sum (fun c _ => hcP i b c))
  exact hlead.sub hsum hleadC
    (fun i => ContDiffAt.sum (fun b _ => ContDiffAt.sum (fun c _ => hcP i b c)))



theorem hasUniformJetBoundsAt_roundCylinderIteratedDerivative
    {ι : Type*} (m : ℕ) (epsilon : ι → ℝ) (u : ι → ℝ) (hu : ∀ i, u i < 1)
    (q : ι → UnitTwoSphere) (s : ι → ℝ)
    (hs : ∀ i, s i ∈ Ioo (-(epsilon i)⁻¹) (epsilon i)⁻¹)
    (B : ι → RoundCylinderTwoTensor)
    (hB : ∀ i, RoundCylinderTensorSmoothOn (epsilon i) (B i))
    (hzero : ∀ a, HasUniformJetBoundsAt m (fun i p => roundCylinderIteratedDerivative
      (u i) (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) (B i) 0 p a)
      (fun i => (0, s i))) :
    ∀ k ≤ m, ∀ a, HasUniformJetBoundsAt (m - k) (fun i p => roundCylinderIteratedDerivative
      (u i) (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) (B i) k p a)
      (fun i => (0, s i)) := by
  have hc (i : ι) (k : ℕ) (a : Fin (2 + k) → Fin 3) :
      ContDiffAt ℝ ∞ (fun p => roundCylinderIteratedDerivative (u i)
        (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) (B i) k p a) (0, s i) := by
    apply (contDiffOn_roundCylinderIteratedDerivative (hu i) (hB i) (q i) k a).contDiffAt
    apply ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).open_target.prod isOpen_Ioo).mem_nhds
    refine ⟨?_, hs i⟩
    rw [← sphere_chart_center (q i)]
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).map_source (mem_chart_source _ (q i))
  intro k
  induction k with
  | zero =>
      intro _
      simpa only [Nat.sub_zero] using hzero
  | succ k ih =>
      intro hkm
      have hk : k ≤ m := by omega
      have horder : m - (k + 1) + 1 = m - k := by omega
      apply hasUniformJetBoundsAt_roundCylinderTensorDerivative u hu q s
        (fun i => roundCylinderIteratedDerivative (u i)
          (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) (B i) k)
      · simpa only [horder] using ih hk
      · exact fun i a => hc i k a

end PoincareConjecture.Proofs.M28.NeckAnalysis
