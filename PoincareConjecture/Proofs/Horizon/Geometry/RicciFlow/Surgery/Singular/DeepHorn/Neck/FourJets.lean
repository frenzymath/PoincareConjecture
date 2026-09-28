import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.Euclidean
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Operations










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.DeepHorn

private theorem norm_jet_succ_le_basis
    {f : RoundCylinderCoordinates → ℝ} {x : RoundCylinderCoordinates}
    (hf : ContDiffAt ℝ ∞ f x) (m : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i : Fin 3,
      ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (roundCylinderCoordinateBasis i)) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ (m + 1) f x‖ ≤ 3 * C := by
  rw [← norm_iteratedFDeriv_fderiv]
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hev (i : Fin 3) :
      (iteratedFDeriv ℝ m (fderiv ℝ f) x v) (roundCylinderCoordinateBasis i) =
        iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (roundCylinderCoordinateBasis i)) x v := by
    have h := (ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis i)).iteratedFDeriv_comp_left
      (hf.fderiv_right (m := ∞) (by simp)) (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞)
    exact (congrArg (fun T => T v) h).symm
  have h := norm_le_of_cylinder_basis_bound
    (iteratedFDeriv ℝ m (fderiv ℝ f) x v)
    (show 0 ≤ C * ∏ i, ‖v i‖ by positivity) (fun i => by
      rw [hev i]
      exact (ContinuousMultilinearMap.le_opNorm _ v).trans
        (mul_le_mul_of_nonneg_right (hb i) (Finset.prod_nonneg fun _ _ => norm_nonneg _)))
  exact h.trans_eq (by ring)

private theorem norm_jet_mul_le
    {f g : RoundCylinderCoordinates → ℝ} {x : RoundCylinderCoordinates}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (m : ℕ) {A B : ℝ} (hA : 0 ≤ A)
    (hfjet : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hgjet : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (fun y => f y * g y) x‖ ≤ (2 : ℝ) ^ m * A * B := by
  have h := norm_iteratedFDeriv_smul_le_of_contDiffAt hf hg m
  simp only [smul_eq_mul] at h
  refine h.trans ?_
  calc
    _ ≤ ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfjet j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
          (by positivity))
        (hgjet (m - j) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ m * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose m

private theorem norm_jet_sum_le
    {ι : Type*} [Fintype ι] {f : ι → RoundCylinderCoordinates → ℝ}
    {x : RoundCylinderCoordinates} (hf : ∀ i, ContDiffAt ℝ ∞ (f i) x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => ∑ i, f i y) x‖ ≤
      ∑ i, ‖iteratedFDeriv ℝ m (f i) x‖ := by
  have heq := iteratedFDeriv_sum_apply (u := Finset.univ) (n := m)
    (fun i _ => (hf i).of_le (by exact_mod_cast le_top))
  have hfun : (fun y => ∑ i, f i y) = ∑ i, f i := by
    funext y
    simp only [Finset.sum_apply]
  rw [hfun, heq]
  exact norm_sum_le _ _

theorem exists_model_connection_jets_center_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : UnitTwoSphere) (s : ℝ) (a b d : Fin 3)
      (j : ℕ), j ≤ m →
      ‖iteratedFDeriv ℝ j (fun p => roundCylinderChristoffel 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) (0, s)‖ ≤ C := by
  classical
  let q₀ : UnitTwoSphere := ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by simp⟩
  let A : Fin (m + 1) × Fin 3 × Fin 3 × Fin 3 → ℝ := fun a =>
    ‖iteratedFDeriv ℝ a.1.val (fun p => roundCylinderChristoffel 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q₀) p a.2.1 a.2.2.1 a.2.2.2) 0‖
  refine ⟨1 + ∑ a, A a, by positivity, ?_⟩
  intro q s a b d j hj
  have ht := iteratedFDeriv_comp_add_right (𝕜 := ℝ)
    (f := fun p => roundCylinderChristoffel 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) j (0, s) 0
  simp only [roundCylinderChristoffel_add_axial, zero_add] at ht
  rw [← ht, roundCylinderChristoffel_eq_chart_center 0 q₀ q]
  exact (Finset.single_le_sum (f := A) (fun _ _ => norm_nonneg _) (Finset.mem_univ
    (⟨j, Nat.lt_succ_of_le hj⟩, a, b, d))).trans (le_add_of_nonneg_left zero_le_one)

private theorem covariant_components_contDiffAt
    (q : UnitTwoSphere) {B : RoundCylinderTwoTensor} {x : RoundCylinderCoordinates}
    (hB : ∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b -
        roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) x)
    (k : ℕ) (a : Fin (2 + k) → Fin 3) :
    ContDiffAt ℝ ∞ (fun y => roundCylinderIteratedDerivative 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) B k y a) x := by
  induction k with
  | zero => exact hB (a 0) (a 1)
  | succ k ih =>
    exact (((ih (fun i => a i.succ)).fderiv_right (by simp)).clm_apply contDiffAt_const).sub
      (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
        (contDiff_roundCylinderChristoffel (by norm_num) q j (a 0) (a i.succ)).contDiffAt.mul
          (ih (Function.update (fun l => a l.succ) i j)))



theorem exists_covariant_coordinate_jets_center_bound (K m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g), K ≤ ⌊N.epsilon⁻¹⌋₊ →
      ∀ j : ℕ, j ≤ m → ∀ k : ℕ, k + j ≤ K →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ a : Fin (2 + k) → Fin 3,
        ‖iteratedFDeriv ℝ j (fun y => roundCylinderIteratedDerivative 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) N.normalized_pullback k y a) (0, s)‖ ≤
          C * N.epsilon := by
  classical
  induction m with
  | zero =>
    refine ⟨(2 : ℝ) ^ (2 + K), by positivity, ?_⟩
    intro M _ _ _ _ _ _ _ g N hK j hj k hk q s hs a
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact (N.abs_normalized_pullback_covariant_component_center_le q hs
      (by omega) a).trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)) N.epsilon_pos.le)
  | succ m ih =>
    obtain ⟨C, hC, hCb⟩ := ih
    obtain ⟨D, hD, hDb⟩ := exists_model_connection_jets_center_bound m
    let A : ℝ := C + ((2 + K : ℕ) : ℝ) * 3 * (2 : ℝ) ^ m * D * C
    have hA : 0 < A := by dsimp [A]; positivity
    refine ⟨C + 3 * A, by positivity, ?_⟩
    intro M _ _ _ _ _ _ _ g N hK j hj k hk q s hs a
    have hε := N.epsilon_pos
    by_cases hjm : j ≤ m
    · exact (hCb N hK j hjm k hk q hs a).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) N.epsilon_pos.le)
    have hjEq : j = m + 1 := by omega
    subst j
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
    let T := fun (b : Fin (2 + k) → Fin 3) y =>
      roundCylinderIteratedDerivative 0 c N.normalized_pullback k y b
    have herror (b d : Fin 3) : ContDiffAt ℝ ∞ (fun y =>
        roundCylinderTensorCoefficient N.normalized_pullback c y b d -
          roundCylinderGram 0 c y b d) (0, s) := by
      apply ((N.normalized_pullback_close.1 q b d).contDiffAt ?_).sub
        (contDiff_roundCylinderGram 0 q b d).contDiffAt
      rw [roundCylinder_sphereChart_target]
      exact (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hs⟩
    have hTs (b : Fin (2 + k) → Fin 3) : ContDiffAt ℝ ∞ (T b) (0, s) :=
      covariant_components_contDiffAt q herror k b
    have hTb (l : ℕ) (hl : l ≤ m) (b : Fin (2 + k) → Fin 3) :
        ‖iteratedFDeriv ℝ l (T b) (0, s)‖ ≤ C * N.epsilon :=
      hCb N hK l hl k (by omega) q hs b
    have hd (i : Fin 3) :
        ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ (T a) y
          (roundCylinderCoordinateBasis i)) (0, s)‖ ≤ A * N.epsilon := by
      let F := fun (b : Fin (2 + k)) (d : Fin 3) y =>
        roundCylinderChristoffel 0 c y d i (a b) * T (Function.update a b d) y
      have hFs (b : Fin (2 + k)) (d : Fin 3) : ContDiffAt ℝ ∞ (F b d) (0, s) :=
        (contDiff_roundCylinderChristoffel (by norm_num) q d i (a b)).contDiffAt.mul (hTs _)
      have hFb (b : Fin (2 + k)) (d : Fin 3) :
          ‖iteratedFDeriv ℝ m (F b d) (0, s)‖ ≤ (2 : ℝ) ^ m * D * (C * N.epsilon) :=
        norm_jet_mul_le
          (contDiff_roundCylinderChristoffel (by norm_num) q d i (a b)).contDiffAt
          (hTs _) m hD.le (hDb q s d i (a b)) (fun l hl => hTb l hl _)
      have hsum : ‖iteratedFDeriv ℝ m (fun y => ∑ b, ∑ d, F b d y) (0, s)‖ ≤
          ((2 + K : ℕ) : ℝ) * 3 * ((2 : ℝ) ^ m * D * (C * N.epsilon)) := by
        calc
          _ ≤ ∑ b, ‖iteratedFDeriv ℝ m (fun y => ∑ d, F b d y) (0, s)‖ :=
            norm_jet_sum_le (fun b => ContDiffAt.sum fun d _ => hFs b d) m
          _ ≤ ∑ b, ∑ d, ‖iteratedFDeriv ℝ m (F b d) (0, s)‖ :=
            Finset.sum_le_sum fun b _ => norm_jet_sum_le (hFs b) m
          _ ≤ ∑ _b : Fin (2 + k), ∑ _d : Fin 3,
              (2 : ℝ) ^ m * D * (C * N.epsilon) :=
            Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun d _ => hFb b d
          _ = ((2 + k : ℕ) : ℝ) * 3 * ((2 : ℝ) ^ m * D * (C * N.epsilon)) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
          _ ≤ _ := by
            gcongr
            omega
      let V := fun y => roundCylinderIteratedDerivative 0 c N.normalized_pullback
        (k + 1) y (Fin.cons i a)
      have hVs : ContDiffAt ℝ ∞ V (0, s) :=
        covariant_components_contDiffAt q herror (k + 1) (Fin.cons i a)
      have hVb : ‖iteratedFDeriv ℝ m V (0, s)‖ ≤ C * N.epsilon :=
        hCb N hK m le_rfl (k + 1) (by omega) q hs (Fin.cons i a)
      have hrec : (fun y => fderiv ℝ (T a) y (roundCylinderCoordinateBasis i)) =
          V + fun y => ∑ b, ∑ d, F b d y := by
        funext y
        dsimp [V, T, F, roundCylinderIteratedDerivative, roundCylinderTensorDerivative]
        simp only [Fin.cons_zero, Fin.cons_succ]
        ring
      rw [hrec, iteratedFDeriv_add_apply (hVs.of_le (by exact_mod_cast le_top))
        ((ContDiffAt.sum fun b _ => ContDiffAt.sum fun d _ => hFs b d).of_le
          (by exact_mod_cast le_top))]
      exact (norm_add_le _ _).trans ((add_le_add hVb hsum).trans_eq (by dsimp [A]; ring))
    have hbound := norm_jet_succ_le_basis (hTs a) m
      (show 0 ≤ A * N.epsilon by positivity) hd
    exact hbound.trans (by nlinarith [mul_pos hC N.epsilon_pos])

end PoincareConjecture.DeepHorn

namespace PoincareConjecture.EpsilonNeck



theorem exists_normalized_pullback_scalar_jet_bound (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g), K ≤ ⌊N.epsilon⁻¹⌋₊ →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ r : ℕ, r ≤ K → ∀ i j : Fin 3,
        ‖iteratedFDeriv ℝ r (fun p =>
          roundCylinderTensorCoefficient N.normalized_pullback
            (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j -
          roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j) (0, s)‖ ≤
            C * N.epsilon := by
  obtain ⟨C, hC, hbound⟩ := DeepHorn.exists_covariant_coordinate_jets_center_bound.{u} K K
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ g N hK q s hs r hr i j
  exact hbound N hK r hr 0 (by simpa using hr) q hs ![i, j]


theorem exists_normalizedEuclideanCoefficients_scalar_jet_bound (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g), K ≤ ⌊N.epsilon⁻¹⌋₊ →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ r : ℕ, r ≤ K → ∀ i j : Fin 3,
        ‖iteratedFDeriv ℝ r (fun x =>
          N.normalizedEuclideanCoefficients q s x
              (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
            roundCylinderEuclideanCoefficients x
              (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) 0‖ ≤
            C * N.epsilon := by
  obtain ⟨C, hC, hbound⟩ := exists_normalized_pullback_scalar_jet_bound.{u} K
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  let A := max 1 ‖T.toContinuousLinearMap‖
  have hA : 1 ≤ A := le_max_left _ _
  refine ⟨C * A ^ K, mul_pos hC (pow_pos (lt_of_lt_of_le zero_lt_one hA) _), ?_⟩
  intro M _ _ _ _ _ _ _ g N hK q s hs r hr i j
  have hε := N.epsilon_pos
  let E := fun p => roundCylinderTensorCoefficient N.normalized_pullback
    (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j -
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j
  have heq : (fun x => E ((0, s) + T x)) =ᶠ[𝓝 0]
      (fun x => N.normalizedEuclideanCoefficients q s x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
        roundCylinderEuclideanCoefficients x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) := by
    filter_upwards [N.normalizedEuclideanCoefficients_basis_eventuallyEq q hs i j]
      with x hx
    dsimp only [E, T]
    rw [hx, roundCylinderEuclideanCoefficients_basis q s]
  rw [← (heq.iteratedFDeriv ℝ r).self_of_nhds]
  have h := Poincare.Analysis.Calculus.norm_iteratedFDeriv_comp_continuousLinearEquiv_le
    T (fun p => E ((0, s) + p)) r 0
  simp only [map_zero, iteratedFDeriv_comp_add_left, add_zero] at h
  have hpow : ‖T.toContinuousLinearMap‖ ^ r ≤ A ^ K :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) r).trans
      (pow_le_pow_right₀ hA hr)
  exact h.trans ((mul_le_mul (hbound N hK q hs r hr i j) hpow
    (pow_nonneg (norm_nonneg _) _) (by positivity)).trans_eq (by ring))



theorem exists_normalizedEuclideanCoefficients_scalar_fourJet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g), N.epsilon ≤ 1 / 4 →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ r : ℕ, r ≤ 4 → ∀ i j : Fin 3,
        ‖iteratedFDeriv ℝ r (fun x =>
          N.normalizedEuclideanCoefficients q s x
              (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
            roundCylinderEuclideanCoefficients x
              (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) 0‖ ≤
            C * N.epsilon := by
  obtain ⟨C, hC, hbound⟩ := exists_normalizedEuclideanCoefficients_scalar_jet_bound.{u} 4
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ g N hsmall
  apply hbound N
  apply (Nat.le_floor_iff (inv_nonneg.mpr N.epsilon_pos.le)).mpr
  norm_num only [Nat.cast_ofNat]
  rw [← one_div, le_div_iff₀ N.epsilon_pos]
  linarith

end PoincareConjecture.EpsilonNeck
