import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.Covariant
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.ModelConnection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Jets.Coefficients
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Operations
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.BilinearJets

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture.M32

section Neck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in

theorem four_le_floor_inv_epsilon (N : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 4) :
    4 ≤ ⌊N.epsilon⁻¹⌋₊ := by
  apply (Nat.le_floor_iff (inv_nonneg.mpr N.epsilon_pos.le)).mpr
  rw [← one_div, le_div_iff₀ N.epsilon_pos]
  norm_num
  linarith

end Neck

theorem exists_roundCylinderChristoffel_threeJet_center_bound :
    ∃ J : ℝ, 0 < J ∧ ∀ (q : UnitTwoSphere) (s : ℝ) (r : ℕ), r ≤ 3 →
      ∀ a b c : Fin 3,
        ‖iteratedFDeriv ℝ r (fun p => roundCylinderChristoffel 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b c) (0, s)‖ ≤ J := by
  classical
  rcases isEmpty_or_nonempty UnitTwoSphere with he | hn
  · let := he
    exact ⟨1, zero_lt_one, fun q => isEmptyElim q⟩
  let q₀ : UnitTwoSphere := hn.some
  let A : Fin 4 × Fin 3 × Fin 3 × Fin 3 → ℝ := fun a =>
    ‖iteratedFDeriv ℝ a.1 (fun p => roundCylinderChristoffel 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q₀) p a.2.1 a.2.2.1 a.2.2.2) 0‖
  refine ⟨1 + ∑ a, A a, by positivity, ?_⟩
  intro q s r hr a b c
  have hshift : iteratedFDeriv ℝ r (fun p => roundCylinderChristoffel 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b c) (0, s) =
      iteratedFDeriv ℝ r (fun p => roundCylinderChristoffel 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b c) 0 := by
    have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ)
      (f := fun p => roundCylinderChristoffel 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b c) r (0, s) 0
    simpa only [roundCylinderChristoffel_add_axial, zero_add] using h.symm
  rw [hshift, roundCylinderChristoffel_eq_chart_center 0 q₀ q]
  let i : Fin 4 × Fin 3 × Fin 3 × Fin 3 := (⟨r, by omega⟩, a, b, c)
  exact (Finset.single_le_sum (f := A) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)

section Neck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem normalized_pullback_covariant_contDiffAt (N : EpsilonNeck g)
    (q : UnitTwoSphere) {p : RoundCylinderCoordinates}
    (hp : p.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (k : ℕ) (a : Fin (2 + k) → Fin 3) :
    ContDiffAt ℝ ∞ (fun y => roundCylinderIteratedDerivative 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) N.normalized_pullback k y a) p := by
  induction k with
  | zero =>
      apply ((N.normalized_pullback_close.1 q (a 0) (a 1)).contDiffAt ?_).sub
        (contDiff_roundCylinderGram 0 q (a 0) (a 1)).contDiffAt
      rw [roundCylinder_sphereChart_target]
      exact (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hp⟩
  | succ k ih =>
      exact (((ih (fun i => a i.succ)).fderiv_right (by simp)).clm_apply
        contDiffAt_const).sub (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
          (contDiff_roundCylinderChristoffel (u := 0) (by norm_num) q j (a 0)
            (a i.succ)).contDiffAt.mul (ih (Function.update (fun l => a l.succ) i j)))

end Neck

private theorem norm_iteratedFDeriv_succ_le_of_cylinder_basis_bound
    {f : RoundCylinderCoordinates → ℝ} {x : RoundCylinderCoordinates}
    (hf : ContDiffAt ℝ ∞ f x) (r : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i : Fin 3, ‖iteratedFDeriv ℝ r
      (fun p => fderiv ℝ f p (roundCylinderCoordinateBasis i)) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ (r + 1) f x‖ ≤ 3 * B := by
  rw [← norm_iteratedFDeriv_fderiv]
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hp : 0 ≤ ∏ i, ‖v i‖ := Finset.prod_nonneg (by simp)
  have h := norm_le_of_cylinder_basis_bound (iteratedFDeriv ℝ r (fderiv ℝ f) x v)
    (mul_nonneg hB hp) (fun i => ?_)
  · exact h.trans_eq (by ring)
  · have heq := congrArg (fun T => T v)
      ((ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis i)).iteratedFDeriv_comp_left
        (hf.fderiv_right (m := ∞) (by simp)) (by exact_mod_cast le_top))
    change iteratedFDeriv ℝ r
      (fun p => fderiv ℝ f p (roundCylinderCoordinateBasis i)) x v =
        iteratedFDeriv ℝ r (fderiv ℝ f) x v (roundCylinderCoordinateBasis i) at heq
    rw [← heq]
    exact (ContinuousMultilinearMap.le_opNorm _ v).trans
      (mul_le_mul_of_nonneg_right (hb i) hp)

theorem exists_normalized_pullback_covariant_fourJet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N : EpsilonNeck g), N.epsilon ≤ 1 / 4 →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j k : ℕ, j + k ≤ 4 → ∀ a : Fin (2 + k) → Fin 3,
        ‖iteratedFDeriv ℝ j (fun p => roundCylinderIteratedDerivative 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) N.normalized_pullback k p a)
          (0, s)‖ ≤ C * N.epsilon := by
  classical
  obtain ⟨J, hJ, hJbound⟩ := exists_roundCylinderChristoffel_threeJet_center_bound
  let L : ℝ := 3 * (1 + 144 * J)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  let B : ℕ → ℝ := fun r => 64 * L ^ r
  have hBpos (r : ℕ) : 0 < B r := by
    exact mul_pos (by norm_num) (pow_pos (lt_of_lt_of_le zero_lt_one hL) _)
  have hBmono : Monotone B := fun r s hrs =>
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hrs) (by norm_num)
  refine ⟨B 4, hBpos 4, ?_⟩
  intro M _ _ _ _ _ _ _ g N hε q s hs j k hjk a
  let T (k : ℕ) (a : Fin (2 + k) → Fin 3) (p : RoundCylinderCoordinates) :=
    roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      N.normalized_pullback k p a
  have hT (k : ℕ) (a : Fin (2 + k) → Fin 3) : ContDiffAt ℝ ∞ (T k a) (0, s) :=
    normalized_pullback_covariant_contDiffAt N q hs k a
  have hbound : ∀ r : ℕ, r ≤ 4 → ∀ j : ℕ, j ≤ r → ∀ k : ℕ, j + k ≤ 4 →
      ∀ a : Fin (2 + k) → Fin 3,
        ‖iteratedFDeriv ℝ j (T k a) (0, s)‖ ≤ B r * N.epsilon := by
    intro r
    induction r with
    | zero =>
        intro _ j hj k hk a
        have hj0 : j = 0 := by omega
        subst j
        rw [norm_iteratedFDeriv_zero]
        have h := N.abs_normalized_pullback_covariant_component_center_le q hs
          (k := k) (by have hfour := four_le_floor_inv_epsilon N hε; omega) a
        have hpow : (2 : ℝ) ^ (2 + k) ≤ 64 := by
          have h := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num)
            (show 2 + k ≤ 6 by omega)
          norm_num at h ⊢
          exact h
        exact h.trans ((mul_le_mul_of_nonneg_right hpow N.epsilon_pos.le).trans_eq
          (by simp [B]))
    | succ r ih =>
        intro hr j hj k hk a
        by_cases hjold : j ≤ r
        · exact (ih (by omega) j hjold k hk a).trans
            (mul_le_mul_of_nonneg_right (hBmono (Nat.le_succ r)) N.epsilon_pos.le)
        have hjeq : j = r + 1 := by omega
        subst j
        have hr3 : r ≤ 3 := by omega
        have hk4 : (k : ℝ) ≤ 4 := by exact_mod_cast (show k ≤ 4 by omega)
        have hlow (m : ℕ) (hm : m ≤ r) (b : Fin (2 + k) → Fin 3) :
            ‖iteratedFDeriv ℝ m (T k b) (0, s)‖ ≤ B r * N.epsilon :=
          ih (by omega) m hm k (by omega) b
        have hproduct (i b c : Fin 3) (a : Fin (2 + k) → Fin 3) :
            ‖iteratedFDeriv ℝ r (fun p => roundCylinderChristoffel 0
              (chartAt (EuclideanSpace ℝ (Fin 2)) q) p b i c * T k a p) (0, s)‖ ≤
              8 * J * B r * N.epsilon := by
          have h := Poincare.Analysis.Calculus.norm_iteratedFDeriv_smul_le_of_contDiffAt
            (contDiff_roundCylinderChristoffel (u := 0) (by norm_num) q b i c).contDiffAt
            (hT k a) r
          simp only [smul_eq_mul] at h
          apply h.trans
          have hchoose : (∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ)) = (2 : ℝ) ^ r := by
            exact_mod_cast Nat.sum_range_choose r
          have hpow : (2 : ℝ) ^ r ≤ 8 := by
            have h := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) hr3
            norm_num at h
            exact h
          calc
            _ ≤ ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ) * J *
                (B r * N.epsilon) := by
              apply Finset.sum_le_sum
              intro l hl
              exact mul_le_mul
                (mul_le_mul_of_nonneg_left
                  (hJbound q s l (by have := Finset.mem_range.mp hl; omega) b i c)
                  (Nat.cast_nonneg _))
                (hlow (r - l) (Nat.sub_le _ _) a) (norm_nonneg _)
                (mul_nonneg (Nat.cast_nonneg _) hJ.le)
            _ = (2 : ℝ) ^ r * J * (B r * N.epsilon) := by
              rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
            _ ≤ 8 * J * (B r * N.epsilon) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hJ.le)
                (mul_nonneg (hBpos r).le N.epsilon_pos.le)
            _ = _ := by ring
        have hdirection (i : Fin 3) :
            ‖iteratedFDeriv ℝ r (fun p => fderiv ℝ (T k a) p
              (roundCylinderCoordinateBasis i)) (0, s)‖ ≤
              (1 + 144 * J) * B r * N.epsilon := by
          let H (l : Fin (2 + k)) (b : Fin 3) (p : RoundCylinderCoordinates) :=
            roundCylinderChristoffel 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
              p b i (a l) * T k (Function.update a l b) p
          have hH (l : Fin (2 + k)) (b : Fin 3) : ContDiffAt ℝ ∞ (H l b) (0, s) :=
            (contDiff_roundCylinderChristoffel (u := 0) (by norm_num) q b i (a l)).contDiffAt.mul
              (hT k _)
          have hsumSmooth : ContDiffAt ℝ ∞ (fun p => ∑ l, ∑ b, H l b p) (0, s) :=
            ContDiffAt.sum (fun l _ => ContDiffAt.sum (fun b _ => hH l b))
          have hinner (l : Fin (2 + k)) :
              ‖iteratedFDeriv ℝ r (fun p => ∑ b, H l b p) (0, s)‖ ≤
                3 * (8 * J * B r * N.epsilon) := by
            simpa only [Fintype.card_fin, Nat.cast_ofNat] using
              CoordinateExponential.norm_iteratedFDeriv_sum_le_const
                (fun b => (hH l b).of_le (by exact_mod_cast le_top))
                (fun b => hproduct i b (a l) (Function.update a l b))
          have hsum : ‖iteratedFDeriv ℝ r (fun p => ∑ l, ∑ b, H l b p) (0, s)‖ ≤
              144 * J * B r * N.epsilon := by
            calc
              _ ≤ (2 + k : ℕ) * (3 * (8 * J * B r * N.epsilon)) := by
                simpa only [Fintype.card_fin] using
                  CoordinateExponential.norm_iteratedFDeriv_sum_le_const
                    (fun l => (ContDiffAt.sum (fun b _ => hH l b)).of_le
                      (by exact_mod_cast le_top)) hinner
              _ = (3 * (2 + (k : ℝ))) * (8 * J * B r * N.epsilon) := by
                push_cast
                ring
              _ ≤ 18 * (8 * J * B r * N.epsilon) :=
                mul_le_mul_of_nonneg_right (by linarith)
                  (by have := hBpos r; have := N.epsilon_pos; positivity)
              _ = _ := by ring
          have heq : (fun p => fderiv ℝ (T k a) p (roundCylinderCoordinateBasis i)) =
              fun p => T (k + 1) (Fin.cons i a) p + ∑ l, ∑ b, H l b p := by
            funext p
            dsimp only [T, H]
            simp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative,
              Fin.cons_zero, Fin.cons_succ]
            exact (sub_add_cancel _ _).symm
          rw [heq, fun_iteratedFDeriv_add_apply
            ((hT (k + 1) _).of_le (by exact_mod_cast le_top))
            (hsumSmooth.of_le (by exact_mod_cast le_top))]
          exact (norm_add_le _ _).trans
            ((add_le_add (ih (by omega) r le_rfl (k + 1) (by omega) _) hsum).trans_eq
              (by ring))
        have hnext := norm_iteratedFDeriv_succ_le_of_cylinder_basis_bound (hT k a) r
          (B := (1 + 144 * J) * B r * N.epsilon)
          (by have := hBpos r; have := N.epsilon_pos; positivity) hdirection
        exact hnext.trans_eq (by dsimp [B, L]; rw [pow_succ]; ring)
  exact hbound 4 le_rfl j (by omega) k hjk a

end PoincareConjecture.M32
