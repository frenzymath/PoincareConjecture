import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.CovariantComponents
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.CovariantSmooth
import PoincareConjecture.Proofs.M28.Mathlib.FiniteHessian.Coordinates
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderCoordinates

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.Proofs.M28.NeckAnalysis

open FiniteHessian

theorem hasUniformJetBoundsAt_fderiv_of_roundCylinderTensorDerivative
    {ι : Type*} {n r : ℕ} (u : ι → ℝ) (hu : ∀ i, u i < 1)
    (q : ι → UnitTwoSphere) (s : ι → ℝ)
    (T : ι → RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ)
    (hT : ∀ a, HasUniformJetBoundsAt n (fun i p => T i p a) (fun i => (0, s i)))
    (hD : ∀ a, HasUniformJetBoundsAt n (fun i p => roundCylinderTensorDerivative (u i)
      (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) (T i) p a) (fun i => (0, s i)))
    (hcT : ∀ i a, ContDiffAt ℝ ∞ (fun p => T i p a) (0, s i))
    (hcD : ∀ i a, ContDiffAt ℝ ∞ (fun p => roundCylinderTensorDerivative (u i)
      (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) (T i) p a) (0, s i)) :
    ∀ a, HasUniformJetBoundsAt n (fun i => fderiv ℝ (fun p => T i p a))
      (fun i => (0, s i)) := by
  classical
  let b : Module.Basis (Fin 3) ℝ RoundCylinderCoordinates :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
      PoincareConjecture.M28.tube.cylinderScalarCoordinateEquiv.toLinearEquiv
  have hb (j : Fin 3) : b j = roundCylinderCoordinateBasis j := by
    exact PoincareConjecture.M28.tube.cylinderScalarCoordinateEquiv_basis j
  intro a
  apply HasUniformJetBoundsAt.of_basis b
  · intro j
    rw [hb]
    let P := fun c : Fin r => fun d : Fin 3 => fun i p =>
      roundCylinderChristoffel (u i) (chartAt (EuclideanSpace ℝ (Fin 2)) (q i))
        p d j (a c) * T i p (Function.update a c d)
    have hcP : ∀ i c d, ContDiffAt ℝ ∞ (P c d i) (0, s i) := by
      intro i c d
      exact (contDiff_roundCylinderChristoffel (hu i) (q i) d j (a c)).contDiffAt.mul
        (hcT i _)
    have hP : ∀ c d, HasUniformJetBoundsAt n (P c d) (fun i => (0, s i)) := by
      intro c d
      have hG : HasUniformJetBoundsAt n (fun i p => roundCylinderChristoffel (u i)
          (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) p d j (a c))
          (fun i => (0, s i)) := by
        obtain ⟨C, _, hC⟩ := exists_bound_roundCylinderChristoffel_jets n
        exact fun k hk => ⟨C, fun i => hC (u i) (hu i) (q i) (s i) k hk d j (a c)⟩
      exact hG.bilinear (hT _)
        (fun i => (contDiff_roundCylinderChristoffel (hu i) (q i) d j (a c)).contDiffAt)
        (fun i => hcT i _) (ContinuousLinearMap.mul ℝ ℝ)
    have hsum := HasUniformJetBoundsAt.sum
      (fun c => HasUniformJetBoundsAt.sum (hP c) (fun i d => hcP i c d))
      (fun i c => ContDiffAt.sum (fun d _ => hcP i c d))
    have hlead := (hD (Fin.cons j a)).add hsum (fun i => hcD i _)
      (fun i => ContDiffAt.sum (fun c _ => ContDiffAt.sum (fun d _ => hcP i c d)))
    apply hlead.congr_germ
    intro i
    apply Filter.Eventually.of_forall
    intro p
    simp [roundCylinderTensorDerivative, P]
  · intro i j
    rw [hb]
    exact ((hcT i a).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

theorem hasUniformJetBoundsAt_of_roundCylinderJetError
    {ι : Type*} (m : ℕ) (epsilon : ι → ℝ)
    (q : ι → UnitTwoSphere) (s : ι → ℝ)
    (hs : ∀ i, s i ∈ Ioo (-(epsilon i)⁻¹) (epsilon i)⁻¹)
    (B : ι → RoundCylinderTwoTensor)
    (hB : ∀ i, RoundCylinderTensorSmoothOn (epsilon i) (B i))
    (herror : ∀ i, roundCylinderJetErrorSquared 0 (B i) m (q i, s i) ≤ 1) :
    ∀ d k : ℕ, d + k ≤ m → ∀ a, HasUniformJetBoundsAt d
      (fun i p => roundCylinderIteratedDerivative 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) (B i) k p a)
      (fun i => (0, s i)) := by
  have hc (i : ι) (k : ℕ) (a : Fin (2 + k) → Fin 3) :
      ContDiffAt ℝ ∞ (fun p => roundCylinderIteratedDerivative 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) (B i) k p a) (0, s i) := by
    apply (contDiffOn_roundCylinderIteratedDerivative
      (by norm_num : (0 : ℝ) < 1) (hB i) (q i) k a).contDiffAt
    apply ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).open_target.prod isOpen_Ioo).mem_nhds
    refine ⟨?_, hs i⟩
    rw [← sphere_chart_center (q i)]
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).map_source (mem_chart_source _ (q i))
  intro d
  induction d with
  | zero =>
      intro k hk a
      exact hasUniformZeroJetBoundsAt_roundCylinderIteratedDerivative m q s B herror
        (by omega) a
  | succ d ih =>
      intro k hk a
      have hzero := hasUniformZeroJetBoundsAt_roundCylinderIteratedDerivative
        m q s B herror (by omega : k ≤ m) a
      have hderiv := hasUniformJetBoundsAt_fderiv_of_roundCylinderTensorDerivative
        (fun _ : ι => (0 : ℝ)) (fun _ => by norm_num) q s
        (fun i => roundCylinderIteratedDerivative 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) (B i) k)
        (ih k (by omega)) (ih (k + 1) (by omega))
        (fun i b => hc i k b) (fun i b => hc i (k + 1) b) a
      apply HasUniformJetBoundsAt.succ_of_fderiv _ hderiv
      simpa only [norm_iteratedFDeriv_zero] using hzero 0 (by omega)

theorem hasUniformJetBoundsAt_cylinder_error_of_close
    {ι : Type*} {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1)
    (m : ℕ) (hm : m ≤ ⌊epsilon⁻¹⌋₊)
    (q : ι → UnitTwoSphere) (s : ι → ℝ)
    (hs : ∀ i, s i ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (B : ι → RoundCylinderTwoTensor) (hB : ∀ i, RoundCylinderClose epsilon 0 (B i)) :
    ∀ k ≤ m, ∀ a, HasUniformJetBoundsAt (m - k)
      (fun i p => roundCylinderIteratedDerivative 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) (B i) k p a)
      (fun i => (0, s i)) := by
  have herror (i : ι) : roundCylinderJetErrorSquared 0 (B i) m (q i, s i) ≤ 1 := by
    obtain ⟨bound, hbound, hb⟩ := (hB i).2
    have hsq : epsilon ^ 2 ≤ 1 := by
      nlinarith [mul_self_le_mul_self hepsilon.le hsmall]
    exact (roundCylinderJetErrorSquared_mono_order (by norm_num) (B i) hm
      (q i, s i)).trans ((hb (q i, s i) (hs i)).trans (hbound.le.trans hsq))
  intro k hk a
  exact hasUniformJetBoundsAt_of_roundCylinderJetError m (fun _ => epsilon) q s hs B
    (fun i => (hB i).1) herror (m - k) k (by omega) a

end PoincareConjecture.Proofs.M28.NeckAnalysis
