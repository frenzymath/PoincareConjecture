import PoincareConjecture.Proofs.M47.CanonicalNeckAxialPullback
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.CylinderCovariantJetBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff BigOperators Topology

namespace PoincareConjecture.Proofs.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates

noncomputable def neckAxialConstantArray (v : ℝ) {r : ℕ} (a : Fin r → Fin 3) : ℝ :=
  v * if ∀ i, a i = 2 then 1 else 0

theorem roundCylinderTensorDerivative_add_neckAxialConstantArray
    (u v : ℝ) (q : UnitTwoSphere) {r : ℕ}
    (T : V → (Fin r → Fin 3) → ℝ) (p : V) (a : Fin (r + 1) → Fin 3) :
    roundCylinderTensorDerivative u (chartAt E₂ q)
        (fun y b => T y b + neckAxialConstantArray v b) p a =
      roundCylinderTensorDerivative u (chartAt E₂ q) T p a := by
  have hzero (i : Fin r) (j : Fin 3) :
      roundCylinderChristoffel u (chartAt E₂ q) p j (a 0) (a i.succ) *
        neckAxialConstantArray v (Function.update (fun k => a k.succ) i j) = 0 := by
    by_cases h : ∀ k, Function.update (fun k => a k.succ) i j k = 2
    · have hj : j = 2 := by simpa only [Function.update_self] using h i
      rw [roundCylinderChristoffel_axial_zero u q p j (a 0) (a i.succ) (Or.inl hj), zero_mul]
    · simp only [neckAxialConstantArray, if_neg h, mul_zero]
  simp only [roundCylinderTensorDerivative, fderiv_add_const]
  simp_rw [mul_add, hzero, add_zero]

theorem roundCylinderTensorDerivative_eq_of_eventuallyEq
    (u : ℝ) (q : UnitTwoSphere) {r : ℕ} {T S : V → (Fin r → Fin 3) → ℝ} {p : V}
    (h : ∀ a, (fun y => T y a) =ᶠ[𝓝 p] fun y => S y a)
    (a : Fin (r + 1) → Fin 3) :
    roundCylinderTensorDerivative u (chartAt E₂ q) T p a =
      roundCylinderTensorDerivative u (chartAt E₂ q) S p a := by
  unfold roundCylinderTensorDerivative
  rw [(h (fun i => a i.succ)).fderiv_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun v => roundCylinderChristoffel u (chartAt E₂ q) p j
    (a 0) (a i.succ) * v) (h (Function.update (fun k => a k.succ) i j)).self_of_nhds

theorem roundCylinderIteratedDerivative_neckAxialTensorPullback_succ
    (lambda c : ℝ) {u : ℝ} (hu : u < 1)
    (B : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ)
    (q : UnitTwoSphere) {U : Set V} (hU : IsOpen U)
    (hB : ∀ i j : Fin 3, ContDiffOn ℝ ∞
      (fun y => roundCylinderTensorCoefficient (fun z v w => B z v w) (chartAt E₂ q) y i j) U)
    (k : ℕ) (p : V) (hp : neckAxialCoordinate lambda c p ∈ U)
    (a : Fin (2 + (k + 1)) → Fin 3) :
    roundCylinderIteratedDerivative u (chartAt E₂ q)
        (neckAxialTensorPullback lambda c (fun z v w => B z v w)) (k + 1) p a =
      neckAxialTensorArray lambda c
        (roundCylinderIteratedDerivative u (chartAt E₂ q) (fun z v w => B z v w) (k + 1)) p a := by
  have hsmooth (j : ℕ) (b : Fin (2 + j) → Fin 3) (y : V) (hy : y ∈ U) :
      ContDiffAt ℝ ∞ (fun z => roundCylinderIteratedDerivative u (chartAt E₂ q)
        (fun z v w => B z v w) j z b) y :=
    M34.roundCylinderIteratedDerivative_contDiffAt hu q
      (fun i l => ((hB i l).contDiffAt (hU.mem_nhds hy)).sub
        (contDiff_roundCylinderGram u q i l).contDiffAt) j b
  induction k generalizing p with
  | zero =>
    have heq : roundCylinderIteratedDerivative u (chartAt E₂ q)
        (neckAxialTensorPullback lambda c (fun z v w => B z v w)) 0 =
        fun y b => neckAxialTensorArray lambda c
          (roundCylinderIteratedDerivative u (chartAt E₂ q) (fun z v w => B z v w) 0) y b +
          neckAxialConstantArray (lambda ^ 2 - 1) b := by
      funext y b
      simpa only [neckAxialConstantArray, Nat.add_zero, Fin.forall_fin_two] using
        roundCylinderIteratedDerivative_neckAxialTensorPullback_zero lambda c u B q y b
    change roundCylinderTensorDerivative u (chartAt E₂ q)
        (roundCylinderIteratedDerivative u (chartAt E₂ q)
          (neckAxialTensorPullback lambda c (fun z v w => B z v w)) 0) p a = _
    rw [heq, roundCylinderTensorDerivative_add_neckAxialConstantArray]
    exact roundCylinderTensorDerivative_neckAxialTensorArray lambda c u q _ p
      (fun b => (hsmooth 0 b _ hp).differentiableAt (by simp)) a
  | succ k ih =>
    have hA : Continuous (neckAxialCoordinate lambda c) :=
      continuous_fst.prodMk ((continuous_const.mul continuous_snd).add continuous_const)
    have heq (b : Fin (2 + (k + 1)) → Fin 3) :
        (fun y => roundCylinderIteratedDerivative u (chartAt E₂ q)
          (neckAxialTensorPullback lambda c (fun z v w => B z v w)) (k + 1) y b) =ᶠ[𝓝 p]
        fun y => neckAxialTensorArray lambda c
          (roundCylinderIteratedDerivative u (chartAt E₂ q)
            (fun z v w => B z v w) (k + 1)) y b := by
      filter_upwards [hA.continuousAt.eventually (hU.mem_nhds hp)] with y hy
      exact ih y hy b
    change roundCylinderTensorDerivative u (chartAt E₂ q)
        (roundCylinderIteratedDerivative u (chartAt E₂ q)
          (neckAxialTensorPullback lambda c (fun z v w => B z v w)) (k + 1)) p a = _
    rw [roundCylinderTensorDerivative_eq_of_eventuallyEq u q heq]
    exact roundCylinderTensorDerivative_neckAxialTensorArray lambda c u q _ p
      (fun b => (hsmooth (k + 1) b _ hp).differentiableAt (by simp)) a

end PoincareConjecture.Proofs.M47
