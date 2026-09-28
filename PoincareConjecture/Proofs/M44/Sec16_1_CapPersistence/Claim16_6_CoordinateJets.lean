import PoincareConjecture.Proofs.M36.ComparisonCovariantJets
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.NormBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M44

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem exists_uniform_ordinary_jet_bound_of_covariant_components
    (G : ℕ → ℝ) (hG : ∀ l, 0 ≤ G l) (k j m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {g : RiemannianMetric 3 E} (D : LeviCivitaData g)
      (T : CovariantTensorEvaluation 3 E k),
      IsSmoothCovariantTensor T → ∀ rho : ℝ, 0 ≤ rho → ∀ x : E,
      (∀ l ≤ j, ∀ a b c : Fin 3,
        ‖iteratedFDeriv ℝ l (comparisonChristoffel g a b c) x‖ ≤ G l) →
      (∀ l : ℕ, l ≤ j + m → ∀ a : Fin (k + l) → Fin 3,
        |comparisonTensorComponent (D.iteratedCovariantTensorDerivative T l) a x| ≤ rho) →
      ∀ a : Fin (k + m) → Fin 3,
        ‖iteratedFDeriv ℝ j
          (comparisonTensorComponent (D.iteratedCovariantTensorDerivative T m) a) x‖ ≤
            C * rho := by
  classical
  induction j using Nat.strong_induction_on generalizing m with
  | h j ih =>
      cases j with
      | zero =>
          refine ⟨1, by norm_num, ?_⟩
          intro g D T hT rho hrho x hchrist hbase a
          simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, one_mul] using
            hbase m (by omega) a
      | succ j =>
          obtain ⟨A, hA, hAbound⟩ := ih j (by omega) (m + 1)
          choose C hC hCbound using fun l : Fin (j + 1) => ih l (by omega) m
          let D0 := 1 + ∑ l : Fin (j + 1), C l
          have hD0 : 0 < D0 := by
            have hsum : 0 ≤ ∑ l : Fin (j + 1), C l :=
              Finset.sum_nonneg (fun l _ => (hC l).le)
            dsimp [D0]
            linarith only [hsum]
          have hCle (l : Fin (j + 1)) : C l ≤ D0 := by
            have h := Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ l)
            dsimp [D0]
            linarith only [h]
          let S := ∑ l : Fin (j + 1), (j.choose l : ℝ) * G l * D0
          have hS : 0 ≤ S := by
            apply Finset.sum_nonneg
            intro l _
            exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hG l)) hD0.le
          refine ⟨3 * (A + (k + m : ℕ) * 3 * S), by positivity, ?_⟩
          intro g D T hT rho hrho x hchrist hbase a
          let Tm := D.iteratedCovariantTensorDerivative T m
          have hTm : IsSmoothCovariantTensor Tm :=
            D.iteratedCovariantTensorDerivative_isSmooth hT m
          have hlow (l : ℕ) (hl : l ≤ j) (b : Fin (k + m) → Fin 3) :
              ‖iteratedFDeriv ℝ l (comparisonTensorComponent Tm b) x‖ ≤ D0 * rho := by
            let l' : Fin (j + 1) := ⟨l, Nat.lt_succ_of_le hl⟩
            exact (hCbound l' D T hT rho hrho x
              (fun s hs => hchrist s (by dsimp [l'] at hs; omega)) (fun s hs b =>
              hbase s (by dsimp [l'] at hs; omega) b) b).trans
                (mul_le_mul_of_nonneg_right (hCle l') hrho)
          have hproduct (b c d : Fin 3) (t : Fin (k + m) → Fin 3) :
              ‖iteratedFDeriv ℝ j (fun y => comparisonChristoffel g b c d y *
                comparisonTensorComponent Tm t y) x‖ ≤ S * rho := by
            have h := Poincare.Analysis.Calculus.norm_iteratedFDeriv_smul_le_of_contDiffAt
              (x := x) (comparisonChristoffel_contDiff g b c d).contDiffAt
              (comparisonTensorComponent_contDiff hTm t).contDiffAt j
            simp only [smul_eq_mul] at h
            apply h.trans
            rw [← Fin.sum_univ_eq_sum_range]
            calc
              _ ≤ ∑ l : Fin (j + 1), (j.choose l : ℝ) * G l * (D0 * rho) := by
                apply Finset.sum_le_sum
                intro l _
                apply mul_le_mul
                · exact mul_le_mul_of_nonneg_left (hchrist l (by omega) b c d)
                    (Nat.cast_nonneg _)
                · exact hlow (j - l) (Nat.sub_le _ _) t
                · exact norm_nonneg _
                · exact mul_nonneg (Nat.cast_nonneg _) (hG l)
              _ = S * rho := by simp only [S, Finset.sum_mul, mul_assoc]
          have hcolumn (c : Fin 3) :
              ‖iteratedFDeriv ℝ j
                (fun y => fderiv ℝ (comparisonTensorComponent Tm a) y (e c)) x‖ ≤
                  (A + (k + m : ℕ) * 3 * S) * rho := by
            let H (i : Fin (k + m)) (b : Fin 3) (y : E) :=
              comparisonChristoffel g b c (a i) y *
                comparisonTensorComponent Tm (Function.update a i b) y
            have hH (i : Fin (k + m)) (b : Fin 3) : ContDiffAt ℝ ∞ (H i b) x :=
              (comparisonChristoffel_contDiff g b c (a i)).contDiffAt.mul
                (comparisonTensorComponent_contDiff hTm _).contDiffAt
            have hsum : ‖iteratedFDeriv ℝ j (fun y => ∑ i, ∑ b, H i b y) x‖ ≤
                (k + m : ℕ) * 3 * S * rho := by
              calc
                _ ≤ ∑ i : Fin (k + m), ‖iteratedFDeriv ℝ j (fun y => ∑ b, H i b y) x‖ :=
                  norm_iteratedFDeriv_finite_sum _
                    (fun i => ContDiffAt.sum (fun b _ => hH i b)) j
                _ ≤ ∑ i : Fin (k + m), ∑ b : Fin 3,
                    ‖iteratedFDeriv ℝ j (H i b) x‖ :=
                  Finset.sum_le_sum (fun i _ => norm_iteratedFDeriv_finite_sum _ (hH i) j)
                _ ≤ ∑ _i : Fin (k + m), ∑ _b : Fin 3, S * rho :=
                  Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun b _ =>
                    hproduct b c (a i) _))
                _ = _ := by simp; ring
            have heq : (fun y => fderiv ℝ (comparisonTensorComponent Tm a) y (e c)) =
                fun y => comparisonTensorComponent
                    (D.iteratedCovariantTensorDerivative T (m + 1)) (Fin.cons c a) y +
                  ∑ i, ∑ b, H i b y := by
              funext y
              have h := comparisonTensorComponent_covariant D hTm (Fin.cons c a) y
              simpa only [Fin.cons_zero, Fin.cons_succ, H, Tm,
                LeviCivitaData.iteratedCovariantTensorDerivative] using
                (eq_sub_iff_add_eq.mp h).symm
            have hc : ContDiffAt ℝ ∞ (comparisonTensorComponent
                (D.iteratedCovariantTensorDerivative T (m + 1)) (Fin.cons c a)) x :=
              (comparisonTensorComponent_contDiff
                (D.iteratedCovariantTensorDerivative_isSmooth hT (m + 1)) _).contDiffAt
            have hs : ContDiffAt ℝ ∞ (fun y => ∑ i, ∑ b, H i b y) x :=
              ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun b _ => hH i b))
            rw [heq, fun_iteratedFDeriv_add_apply
              (hc.of_le (by exact_mod_cast le_top)) (hs.of_le (by exact_mod_cast le_top))]
            exact (norm_add_le _ _).trans
              ((add_le_add (hAbound D T hT rho hrho x
                (fun l hl => hchrist l (by omega))
                (fun l hl b => hbase l (by omega) b) _) hsum).trans_eq (by ring))
          exact (norm_iteratedFDeriv_succ_le_basis
            (comparisonTensorComponent_contDiff hTm a).contDiffAt j).trans
              ((Finset.sum_le_sum (fun c _ => hcolumn c)).trans_eq (by simp; ring))

theorem exists_ordinary_jet_bound_of_covariant_components
    {g : RiemannianMetric 3 E} (D : LeviCivitaData g)
    {K : Set E} (hK : IsCompact K) (k j m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : CovariantTensorEvaluation 3 E k),
      IsSmoothCovariantTensor T → ∀ rho : ℝ, 0 ≤ rho → ∀ x ∈ K,
      (∀ l : ℕ, l ≤ j + m → ∀ a : Fin (k + l) → Fin 3,
        |comparisonTensorComponent (D.iteratedCovariantTensorDerivative T l) a x| ≤ rho) →
      ∀ a : Fin (k + m) → Fin 3,
        ‖iteratedFDeriv ℝ j
          (comparisonTensorComponent (D.iteratedCovariantTensorDerivative T m) a) x‖ ≤
            C * rho := by
  choose G hG hGbound using fun l => exists_comparisonChristoffel_jet_bound g hK l
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_ordinary_jet_bound_of_covariant_components G (fun l => (hG l).le) k j m
  refine ⟨C, hC, ?_⟩
  intro T hT rho hrho x hx hbase a
  exact hbound D T hT rho hrho x (fun l _ a b c => hGbound l a b c x hx) hbase a

theorem exists_basis_tangent_norm_bound (g : RiemannianMetric 3 E)
    {K : Set E} (hK : IsCompact K) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ a : Fin 3, g.tangentNorm x (e a) ≤ L := by
  classical
  have hg : Continuous g.euclideanCoefficients :=
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).continuous
  have hc (a : Fin 3) : Continuous (fun x : E => g.tangentNorm x (e a)) :=
    ((hg.clm_apply continuous_const).clm_apply continuous_const).sqrt
  choose A hA using fun a : Fin 3 => hK.exists_bound_of_continuousOn (hc a).continuousOn
  let L := 1 + ∑ a : Fin 3, max (A a) 0
  have hsum : 0 ≤ ∑ a : Fin 3, max (A a) 0 := by positivity
  refine ⟨L, by dsimp [L]; linarith only [hsum], ?_⟩
  intro x hx a
  have h := (le_abs_self (g.tangentNorm x (e a))).trans (hA a x hx)
  have hs := Finset.single_le_sum (fun b _ => le_max_right (A b) 0) (Finset.mem_univ a)
  exact h.trans ((le_max_left (A a) 0).trans (hs.trans (by dsimp [L]; linarith)))

theorem comparison_component_le_tangent_bound
    (g : RiemannianMetric 3 E) {k : ℕ} (T : CovariantTensorEvaluation 3 E k)
    (x : E) (hT : ∃ A : MultilinearMap ℝ (fun _ : Fin k => E) ℝ,
      ∀ v, T x v = A v) {L rho : ℝ} (_hL : 0 ≤ L) (hrho : 0 ≤ rho)
    (hbound : ∀ a : Fin 3, g.tangentNorm x (e a) ≤ L)
    (hN : g.tensorNorm T x ≤ rho) (a : Fin k → Fin 3) :
    |comparisonTensorComponent T a x| ≤ L ^ k * rho := by
  obtain ⟨A, hA⟩ := hT
  have h := abs_tensor_evaluation_le_tensorNorm g T x A hA (fun i => e (a i))
  have hprod : (∏ i : Fin k, g.tangentNorm x (e (a i))) ≤ L ^ k := by
    calc
      _ ≤ ∏ _i : Fin k, L :=
        Finset.prod_le_prod (fun _ _ => Real.sqrt_nonneg _) (fun i _ => hbound (a i))
      _ = _ := by simp
  exact h.trans ((mul_le_mul hN hprod
    (Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)) hrho).trans_eq (mul_comm _ _))

theorem exists_uniform_ordinary_jet_bound_of_covariant_norms
    (G : ℕ → ℝ) (hG : ∀ l, 0 ≤ G l) {L : ℝ} (hL : 0 < L) (k j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {g : RiemannianMetric 3 E} (D : LeviCivitaData g)
      (T : CovariantTensorEvaluation 3 E k),
      IsSmoothCovariantTensor T → ∀ rho : ℝ, 0 ≤ rho → ∀ x : E,
      (∀ a : Fin 3, g.tangentNorm x (e a) ≤ L) →
      (∀ l ≤ j, ∀ a b c : Fin 3,
        ‖iteratedFDeriv ℝ l (comparisonChristoffel g a b c) x‖ ≤ G l) →
      (∀ l : ℕ, l ≤ j → g.tensorNorm (D.iteratedCovariantTensorDerivative T l) x ≤ rho) →
      ∀ a : Fin k → Fin 3,
        ‖iteratedFDeriv ℝ j (comparisonTensorComponent T a) x‖ ≤ C * rho := by
  classical
  obtain ⟨A, hA, hAbound⟩ :=
    exists_uniform_ordinary_jet_bound_of_covariant_components G hG k j 0
  let B := ∑ l : Fin (j + 1), L ^ (k + l.val)
  have hB : 0 < B := Finset.sum_pos (fun l _ => pow_pos hL _) Finset.univ_nonempty
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro g D T hT rho hrho x hLbound hchrist hnorm a
  have hbase (l : ℕ) (hl : l ≤ j + 0) (b : Fin (k + l) → Fin 3) :
      |comparisonTensorComponent (D.iteratedCovariantTensorDerivative T l) b x| ≤ B * rho := by
    have hc := comparison_component_le_tangent_bound g
      (D.iteratedCovariantTensorDerivative T l) x
      ((D.iteratedCovariantTensorDerivative_isSmooth hT l).1 x) hL.le hrho
      hLbound (hnorm l (by omega)) b
    have hb : L ^ (k + l) ≤ B :=
      Finset.single_le_sum (f := fun i : Fin (j + 1) => L ^ (k + i.val))
        (fun i _ => (pow_pos hL _).le)
        (Finset.mem_univ (⟨l, by omega⟩ : Fin (j + 1)))
    exact hc.trans (mul_le_mul_of_nonneg_right hb hrho)
  exact (hAbound D T hT (B * rho) (mul_nonneg hB.le hrho) x hchrist hbase a).trans_eq
    (mul_assoc A B rho).symm

theorem exists_ordinary_jet_bound_of_covariant_norms
    {g : RiemannianMetric 3 E} (D : LeviCivitaData g)
    {K : Set E} (hK : IsCompact K) (k j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : CovariantTensorEvaluation 3 E k),
      IsSmoothCovariantTensor T → ∀ rho : ℝ, 0 ≤ rho → ∀ x ∈ K,
      (∀ l : ℕ, l ≤ j → g.tensorNorm (D.iteratedCovariantTensorDerivative T l) x ≤ rho) →
      ∀ a : Fin k → Fin 3,
        ‖iteratedFDeriv ℝ j (comparisonTensorComponent T a) x‖ ≤ C * rho := by
  choose G hG hGbound using fun l => exists_comparisonChristoffel_jet_bound g hK l
  obtain ⟨L, hL, hLbound⟩ := exists_basis_tangent_norm_bound g hK
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_ordinary_jet_bound_of_covariant_norms G (fun l => (hG l).le) hL k j
  refine ⟨C, hC, ?_⟩
  intro T hT rho hrho x hx hnorm a
  exact hbound D T hT rho hrho x (hLbound x hx)
    (fun l _ a b c => hGbound l a b c x hx) hnorm a

private theorem norm_bilinear_jet_le_components
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} (hB : ContDiff ℝ ∞ B)
    (j : ℕ) (x : E) {rho : ℝ} (hrho : 0 ≤ rho)
    (h : ∀ a b : Fin 3,
      ‖iteratedFDeriv ℝ j (fun y => B y (e a) (e b)) x‖ ≤ rho) :
    ‖iteratedFDeriv ℝ j B x‖ ≤ 9 * rho := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hp : 0 ≤ ∏ i, ‖v i‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have he (a b : Fin 3) :
      iteratedFDeriv ℝ j (fun y => B y (e a) (e b)) x v =
        iteratedFDeriv ℝ j B x v (e a) (e b) := by
    have h1 := iteratedFDerivWithin_clm_apply_const_apply
      (𝕜 := ℝ) uniqueDiffOn_univ hB.contDiffOn
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top) (Set.mem_univ x) (u := e a) (m := v)
    have h2 := iteratedFDerivWithin_clm_apply_const_apply
      (𝕜 := ℝ) uniqueDiffOn_univ (hB.clm_apply (contDiff_const (c := e a))).contDiffOn
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top) (Set.mem_univ x) (u := e b) (m := v)
    simp only [iteratedFDerivWithin_of_isOpen j isOpen_univ (Set.mem_univ x)] at h1 h2
    rw [h2, h1]
  have hc (a b : Fin 3) :
      ‖iteratedFDeriv ℝ j B x v (e a) (e b)‖ ≤ rho * ∏ i, ‖v i‖ := by
    rw [← he]
    exact (ContinuousMultilinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (h a b) hp)
  exact (euclideanThree_bilinear_norm_le _ (mul_nonneg hrho hp) hc).trans_eq (by ring)

theorem exists_uniform_local_bilinear_jet_bound_of_covariant_norms
    (G : ℕ → ℝ) (hG : ∀ l, 0 ≤ G l) {L : ℝ} (hL : 0 < L) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {g : RiemannianMetric 3 E} (D : LeviCivitaData g)
      (B : E → E →L[ℝ] E →L[ℝ] ℝ)
      (U : Set E), IsOpen U → ContDiffOn ℝ ∞ B U →
      ∀ rho : ℝ, 0 ≤ rho → ∀ x : E, x ∈ U →
      (∀ a : Fin 3, g.tangentNorm x (e a) ≤ L) →
      (∀ l ≤ j, ∀ a b c : Fin 3,
        ‖iteratedFDeriv ℝ l (comparisonChristoffel g a b c) x‖ ≤ G l) →
      (∀ l : ℕ, l ≤ j → g.tensorNorm (D.iteratedCovariantTensorDerivative (k := 2)
        (fun y v => B y (v 0) (v 1) - g.inner y (v 0) (v 1)) l) x ≤ rho) →
      ‖iteratedFDeriv ℝ j (B - g.euclideanCoefficients) x‖ ≤ C * rho := by
  obtain ⟨C, hC, hCbound⟩ :=
    exists_uniform_ordinary_jet_bound_of_covariant_norms G hG hL 2 j
  refine ⟨9 * C, by positivity, ?_⟩
  intro g D B U hU hB rho hrho x hxU hLbound hchrist hnorm
  have hg : ContDiff ℝ ∞ g.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  obtain ⟨A, hA, heq⟩ := exists_comparison_smooth_germ hU (hB.sub hg.contDiffOn) hxU
  let T : CovariantTensorEvaluation 3 E 2 := fun y v => A y (v 0) (v 1)
  have hT : IsSmoothCovariantTensor T := comparison_bilinear_isSmooth hA
  have hTeq : ∀ᶠ y in nhds x, T y =
      (fun v => B y (v 0) (v 1) - g.inner y (v 0) (v 1)) := by
    filter_upwards [heq] with y hy
    funext v
    change A y (v 0) (v 1) = _
    rw [hy]
    rfl
  have hTnorm (l : ℕ) (hl : l ≤ j) :
      g.tensorNorm (D.iteratedCovariantTensorDerivative T l) x ≤ rho := by
    have he := (comparison_iteratedCovariantTensorDerivative_eventuallyEq D hTeq l).self_of_nhds
    change Real.sqrt _ ≤ _
    simpa only [RiemannianMetric.tensorNorm, he] using hnorm l hl
  have hc (a b : Fin 3) : ‖iteratedFDeriv ℝ j (fun y => A y (e a) (e b)) x‖ ≤ C * rho := by
    exact hCbound D T hT rho hrho x hLbound hchrist hTnorm ![a, b]
  have hjet : iteratedFDeriv ℝ j A x =
      iteratedFDeriv ℝ j (B - g.euclideanCoefficients) x :=
    (heq.iteratedFDeriv ℝ j).self_of_nhds
  rw [← hjet]
  exact (norm_bilinear_jet_le_components hA j x (mul_nonneg hC.le hrho) hc).trans_eq (by ring)

theorem exists_local_bilinear_jet_bound_of_covariant_norms
    {g : RiemannianMetric 3 E} (D : LeviCivitaData g)
    {K : Set E} (hK : IsCompact K) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : E → E →L[ℝ] E →L[ℝ] ℝ)
      (U : Set E), IsOpen U → ContDiffOn ℝ ∞ B U →
      ∀ rho : ℝ, 0 ≤ rho → ∀ x ∈ K, x ∈ U →
      (∀ l : ℕ, l ≤ j → g.tensorNorm (D.iteratedCovariantTensorDerivative (k := 2)
        (fun y v => B y (v 0) (v 1) - g.inner y (v 0) (v 1)) l) x ≤ rho) →
      ‖iteratedFDeriv ℝ j (B - g.euclideanCoefficients) x‖ ≤ C * rho := by
  choose G hG hGbound using fun l => exists_comparisonChristoffel_jet_bound g hK l
  obtain ⟨L, hL, hLbound⟩ := exists_basis_tangent_norm_bound g hK
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_local_bilinear_jet_bound_of_covariant_norms G (fun l => (hG l).le) hL j
  refine ⟨C, hC, ?_⟩
  intro B U hU hB rho hrho x hx hxU hnorm
  exact hbound D B U hU hB rho hrho x hxU (hLbound x hx)
    (fun l _ a b c => hGbound l a b c x hx) hnorm

end PoincareConjecture.M44
