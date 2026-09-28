import PoincareConjecture.Proofs.M36.ComparisonCovariantJets
import PoincareConjecture.Proofs.M36.ComparisonCoordinateJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M44

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

theorem exists_uniform_covariant_component_bound (k d m : ℕ) {G : ℝ} (hG : 0 ≤ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : RiemannianMetric 3 E) (D : LeviCivitaData g)
      (T : CovariantTensorEvaluation 3 E k), IsSmoothCovariantTensor T →
      ∀ x : E, ∀ rho : ℝ, 0 ≤ rho →
      (∀ l ≤ d, ∀ a b c : Fin 3,
        ‖iteratedFDeriv ℝ l (comparisonChristoffel g a b c) x‖ ≤ G) →
      (∀ l ≤ d, ∀ a : Fin k → Fin 3,
        ‖iteratedFDeriv ℝ l (comparisonTensorComponent T a) x‖ ≤ rho) →
      ∀ j : ℕ, j + m ≤ d → ∀ a : Fin (k + m) → Fin 3,
        ‖iteratedFDeriv ℝ j
          (comparisonTensorComponent (D.iteratedCovariantTensorDerivative T m) a) x‖ ≤
            C * rho := by
  classical
  induction m with
  | zero =>
      refine ⟨1, by norm_num, ?_⟩
      intro g D T hT x rho hrho hchrist hbase j hj a
      simpa only [LeviCivitaData.iteratedCovariantTensorDerivative, one_mul] using
        hbase j (by omega) a
  | succ m ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      let A := C * (1 + (k + m : ℕ) * 3 * (2 : ℝ) ^ d * G)
      have hA : 0 < A := by dsimp [A]; positivity
      refine ⟨A, hA, ?_⟩
      intro g D T hT x rho hrho hchrist hbase j hj a
      let Tm := D.iteratedCovariantTensorDerivative T m
      have hTm : IsSmoothCovariantTensor Tm :=
        D.iteratedCovariantTensorDerivative_isSmooth hT m
      have hlow (l : ℕ) (hl : l + m ≤ d) (b : Fin (k + m) → Fin 3) :
          ‖iteratedFDeriv ℝ l (comparisonTensorComponent Tm b) x‖ ≤ C * rho :=
        hbound g D T hT x rho hrho hchrist hbase l hl b
      have hproduct (b c f : Fin 3) (v : Fin (k + m) → Fin 3) :
          ‖iteratedFDeriv ℝ j (fun y => comparisonChristoffel g b c f y *
            comparisonTensorComponent Tm v y) x‖ ≤ (2 : ℝ) ^ d * G * (C * rho) := by
        have h := norm_iteratedFDeriv_smul_uniform_at
          (comparisonChristoffel_contDiff g b c f).contDiffAt
          (comparisonTensorComponent_contDiff hTm v).contDiffAt j hG
          (mul_nonneg hC.le hrho)
          (fun l hl => hchrist l (by omega) b c f)
          (fun l hl => hlow l (by omega) v)
        simp only [smul_eq_mul] at h
        apply h.trans
        gcongr
        · norm_num
        · omega
      have hderiv : ‖iteratedFDeriv ℝ j (fun y =>
          fderiv ℝ (comparisonTensorComponent Tm (fun i => a i.succ)) y (e (a 0))) x‖ ≤
            C * rho := by
        have h := norm_iteratedFDeriv_clm_apply_const (x := x)
          ((comparisonTensorComponent_contDiff hTm (fun i => a i.succ)).contDiffAt.fderiv_right
            (m := ∞) (by simp)) (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
          (c := e (a 0))
        simp only [(e).norm_eq_one, one_mul, norm_iteratedFDeriv_fderiv] at h
        exact h.trans (hlow (j + 1) (by omega) _)
      let H (i : Fin (k + m)) (b : Fin 3) (y : E) :=
        comparisonChristoffel g b (a 0) (a i.succ) y *
          comparisonTensorComponent Tm (Function.update (fun l => a l.succ) i b) y
      have hH (i : Fin (k + m)) (b : Fin 3) : ContDiffAt ℝ ∞ (H i b) x :=
        (comparisonChristoffel_contDiff g b (a 0) (a i.succ)).contDiffAt.mul
          (comparisonTensorComponent_contDiff hTm _).contDiffAt
      have hsum : ‖iteratedFDeriv ℝ j (fun y => ∑ i, ∑ b, H i b y) x‖ ≤
          (k + m : ℕ) * 3 * ((2 : ℝ) ^ d * G * (C * rho)) := by
        calc
          _ ≤ ∑ i : Fin (k + m), ‖iteratedFDeriv ℝ j (fun y => ∑ b, H i b y) x‖ :=
            norm_iteratedFDeriv_finite_sum _ (fun i => ContDiffAt.sum (fun b _ => hH i b)) j
          _ ≤ ∑ i : Fin (k + m), ∑ b : Fin 3, ‖iteratedFDeriv ℝ j (H i b) x‖ :=
            Finset.sum_le_sum (fun i _ => norm_iteratedFDeriv_finite_sum _ (hH i) j)
          _ ≤ ∑ _i : Fin (k + m), ∑ _b : Fin 3, (2 : ℝ) ^ d * G * (C * rho) :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun b _ =>
              hproduct b (a 0) (a i.succ) _))
          _ = _ := by simp; ring
      have heq : comparisonTensorComponent (D.iteratedCovariantTensorDerivative T (m + 1)) a =
          fun y => fderiv ℝ (comparisonTensorComponent Tm (fun i => a i.succ)) y (e (a 0)) -
            ∑ i, ∑ b, H i b y :=
        funext (comparisonTensorComponent_covariant D hTm a)
      have hds : ContDiffAt ℝ ∞ (fun y =>
          fderiv ℝ (comparisonTensorComponent Tm (fun i => a i.succ)) y (e (a 0))) x :=
        ((comparisonTensorComponent_contDiff hTm _).contDiffAt.fderiv_right
          (m := ∞) (by simp)).clm_apply contDiffAt_const
      have hss : ContDiffAt ℝ ∞ (fun y => ∑ i, ∑ b, H i b y) x :=
        ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun b _ => hH i b))
      rw [heq, fun_iteratedFDeriv_sub_apply
        (hds.of_le (by exact_mod_cast le_top)) (hss.of_le (by exact_mod_cast le_top))]
      exact (norm_sub_le _ _).trans ((add_le_add hderiv hsum).trans_eq (by dsimp [A]; ring))

theorem tensorNorm_le_of_coordinate_components {k : ℕ}
    (g : RiemannianMetric 3 E) (T : CovariantTensorEvaluation 3 E k) (x : E)
    {a rho : ℝ} (ha : 0 < a) (hrho : 0 ≤ rho)
    (hell : ∀ v : E, a * ‖v‖ ^ 2 ≤ g.inner x v v)
    (hT : ∃ A : MultilinearMap ℝ (fun _ : Fin k => E) ℝ, ∀ v, T x v = A v)
    (hcoeff : ∀ b : Fin k → Fin 3, |comparisonTensorComponent T b x| ≤ rho) :
    g.tensorNorm T x ≤
      (Real.sqrt ((3 : ℝ) ^ k) * (3 : ℝ) ^ k * (1 + 1 / a) ^ k) * rho := by
  classical
  let L := 1 + 1 / a
  have hL : 0 < L := by dsimp [L]; positivity
  have hunitbound (v : E) (hv : g.inner x v v = 1) : ‖v‖ ≤ L := by
    have hsq : ‖v‖ ^ 2 ≤ 1 / a := by
      apply (le_div_iff₀ ha).mpr
      have h := hell v
      rw [hv] at h
      nlinarith only [h]
    dsimp [L]
    nlinarith only [hsq, sq_nonneg (‖v‖ - 1 / 2)]
  obtain ⟨A, hA⟩ := hT
  let b := g.orthonormalBasis x
  let A0 := (3 : ℝ) ^ k * L ^ k
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hunit (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      g.inner x (b i) (b i) = 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : E → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change inner ℝ (b i) (b i) = 1
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one, one_pow]
  have hcomponent (c : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      |T x (fun i => b (c i))| ≤ A0 * rho := by
    rw [hA]
    exact comparison_tensor_evaluation_bound A hrho hL.le
      (fun c => by simpa only [comparisonTensorComponent, hA] using hcoeff c)
      _ (fun i => hunitbound _ (hunit (c i)))
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    simp [TangentSpace]
  have hsq : (∑ c : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
      (T x (fun i => b (c i))) ^ 2) ≤ (3 : ℝ) ^ k * (A0 * rho) ^ 2 := by
    calc
      _ ≤ ∑ _c : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
          (A0 * rho) ^ 2 := by
        apply Finset.sum_le_sum
        intro c _
        simpa only [← pow_two, sq_abs] using
          mul_self_le_mul_self (abs_nonneg _) (hcomponent c)
      _ = _ := by simp [hdim]
  change Real.sqrt _ ≤ _
  apply (Real.sqrt_le_sqrt hsq).trans_eq
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (mul_nonneg hA0 hrho)]
  dsimp [A0, L]
  ring

theorem exists_uniform_covariant_norm_bound (k m : ℕ) {a G : ℝ}
    (ha : 0 < a) (hG : 0 ≤ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : RiemannianMetric 3 E) (D : LeviCivitaData g)
      (T : CovariantTensorEvaluation 3 E k), IsSmoothCovariantTensor T →
      ∀ x : E, ∀ rho : ℝ, 0 ≤ rho →
      (∀ v : E, a * ‖v‖ ^ 2 ≤ g.inner x v v) →
      (∀ l ≤ m, ∀ b c d : Fin 3,
        ‖iteratedFDeriv ℝ l (comparisonChristoffel g b c d) x‖ ≤ G) →
      (∀ l ≤ m, ∀ b : Fin k → Fin 3,
        ‖iteratedFDeriv ℝ l (comparisonTensorComponent T b) x‖ ≤ rho) →
      g.tensorNorm (D.iteratedCovariantTensorDerivative T m) x ≤ C * rho := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_covariant_component_bound k m m hG
  let N := Real.sqrt ((3 : ℝ) ^ (k + m)) * (3 : ℝ) ^ (k + m) * (1 + 1 / a) ^ (k + m)
  have hN : 0 < N := by dsimp [N]; positivity
  refine ⟨N * C, mul_pos hN hC, ?_⟩
  intro g D T hT x rho hrho hell hchrist hbase
  have hTm := D.iteratedCovariantTensorDerivative_isSmooth hT m
  have hc (b : Fin (k + m) → Fin 3) :
      |comparisonTensorComponent (D.iteratedCovariantTensorDerivative T m) b x| ≤ C * rho := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
      hbound g D T hT x rho hrho hchrist hbase 0 (by omega) b
  exact (tensorNorm_le_of_coordinate_components g _ x ha (mul_nonneg hC.le hrho)
    hell (hTm.1 x) hc).trans_eq (by dsimp [N]; ring)

end PoincareConjecture.M44
