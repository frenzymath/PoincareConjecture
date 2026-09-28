import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.EvolvingModel
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Operations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology BigOperators
open Poincare.Analysis.Calculus

namespace PoincareConjecture
namespace TerminalNeck

private theorem norm_jet_directional_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v : E) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y v) x‖ ≤
      ‖ContinuousLinearMap.apply ℝ ℝ v‖ * ‖iteratedFDeriv ℝ (m + 1) f x‖ := by
  simpa only [norm_iteratedFDeriv_fderiv, Function.comp_def, ContinuousLinearMap.apply_apply] using
    (ContinuousLinearMap.apply ℝ ℝ v).norm_iteratedFDeriv_comp_left
      (hf.fderiv_right (m := ∞) (by simp)) (by exact_mod_cast le_top)

private theorem norm_jet_mul_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (m : ℕ) {A B : ℝ} (hA : 0 ≤ A)
    (hfjet : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hgjet : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (fun y => f y * g y) x‖ ≤ (2 : ℝ) ^ m * A * B := by
  have h := norm_iteratedFDeriv_smul_le_of_contDiffAt hf hg m
  simp only [smul_eq_mul] at h
  refine h.trans ?_
  calc
    ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j f x‖ * ‖iteratedFDeriv ℝ (m - j) g x‖ ≤
        ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * A * B := by
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

private theorem norm_jet_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f y - g y) x‖ ≤
      ‖iteratedFDeriv ℝ m f x‖ + ‖iteratedFDeriv ℝ m g x‖ := by
  change ‖iteratedFDeriv ℝ m (f - g) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply
    (hf.of_le (by exact_mod_cast le_top)) (hg.of_le (by exact_mod_cast le_top))]
  exact norm_sub_le _ _

private theorem norm_jet_sum_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] {f : ι → E → ℝ} {x : E}
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => ∑ i, f i y) x‖ ≤
      ∑ i, ‖iteratedFDeriv ℝ m (f i) x‖ := by
  have heq := iteratedFDeriv_sum_apply
    (u := Finset.univ) (n := m)
    (fun i _ => (hf i).of_le (by exact_mod_cast le_top))
  have hfun : (fun y => ∑ i, f i y) = ∑ i, f i := by
    funext y
    simp only [Finset.sum_apply]
  rw [hfun, heq]
  exact norm_sum_le _ _

theorem contDiffAt_evolvingCylinderIteratedDerivative
    (u : ℝ) (hu : u < 1) (q : UnitTwoSphere) {B : RoundCylinderTwoTensor} {x : RoundCylinderCoordinates}
    (hB : ∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b -
        roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) x)
    (k : ℕ) (a : Fin (2 + k) → Fin 3) :
    ContDiffAt ℝ ∞ (fun y => roundCylinderIteratedDerivative u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) B k y a) x := by
  induction k with
  | zero => exact hB (a 0) (a 1)
  | succ k ih =>
    exact (((ih (fun i => a i.succ)).fderiv_right (by simp)).clm_apply contDiffAt_const).sub
      (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
        (contDiff_roundCylinderChristoffel hu q j (a 0) (a i.succ)).contDiffAt.mul
          (ih (Function.update (fun l => a l.succ) i j)))

private theorem exists_covariant_jet_bound
    (q₀ : UnitTwoSphere) {K : Set RoundCylinderCoordinates} (hK : IsCompact K)
    (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Icc (-1 : ℝ) 0, ∀ (q : UnitTwoSphere) (B : RoundCylinderTwoTensor)
      (x : RoundCylinderCoordinates), x ∈ K → ∀ A : ℝ, 0 ≤ A →
      (∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun y =>
        roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b -
          roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) x) →
      (∀ j, j ≤ k + m → ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b -
            roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) x‖ ≤ A) →
      ∀ j, j ≤ m → ∀ a : Fin (2 + k) → Fin 3,
        ‖iteratedFDeriv ℝ j (fun y => roundCylinderIteratedDerivative u
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) B k y a) x‖ ≤ C * A := by
  classical
  induction k generalizing m with
  | zero =>
    refine ⟨1, zero_le_one, ?_⟩
    intro u hu q B x hx A hA hs hb j hj a
    simpa only [roundCylinderIteratedDerivative, one_mul] using hb j (by simpa using hj) (a 0) (a 1)
  | succ k ih =>
    obtain ⟨C, hC, hCb⟩ := ih (m + 1)
    obtain ⟨D, hD, hDb⟩ := exists_evolvingChristoffel_spatialJet_bound q₀ hK m
    let V : ℝ := ∑ i : Fin 3,
      ‖ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis i)‖
    have hV : 0 ≤ V := Finset.sum_nonneg fun i _ =>
      norm_nonneg (ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis i))
    refine ⟨(V + (2 + k : ℕ) * 3 * (2 : ℝ) ^ m * D) * C, by positivity, ?_⟩
    intro u hu q B x hx A hA hs hb j hj a
    have hu' : u < 1 := by linarith [hu.2]
    let T := fun (b : Fin (2 + k) → Fin 3) y =>
      roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q) B k y b
    have hTs (b : Fin (2 + k) → Fin 3) : ContDiffAt ℝ ∞ (T b) x :=
      contDiffAt_evolvingCylinderIteratedDerivative u hu' q hs k b
    have hTb (l : ℕ) (hl : l ≤ m + 1) (b : Fin (2 + k) → Fin 3) :
        ‖iteratedFDeriv ℝ l (T b) x‖ ≤ C * A :=
      hCb u hu q B x hx A hA hs (fun r hr => hb r (by omega)) l hl b
    let F := fun (i : Fin (2 + k)) (d : Fin 3) y =>
      roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) y d (a 0) (a i.succ) *
        T (Function.update (fun l => a l.succ) i d) y
    have hFs (i : Fin (2 + k)) (d : Fin 3) : ContDiffAt ℝ ∞ (F i d) x :=
      (contDiff_roundCylinderChristoffel hu' q d (a 0) (a i.succ)).contDiffAt.mul (hTs _)
    have hFb (i : Fin (2 + k)) (d : Fin 3) :
        ‖iteratedFDeriv ℝ j (F i d) x‖ ≤ ((2 : ℝ) ^ m * D * C) * A := by
      have hg (l : ℕ) (hl : l ≤ j) :
          ‖iteratedFDeriv ℝ l (fun y =>
            roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
              y d (a 0) (a i.succ)) x‖ ≤ D := by
        rw [roundCylinderChristoffel_eq_chart_center u q₀ q]
        exact hDb u hu l (hl.trans hj) d (a 0) (a i.succ) x hx
      have hmul := norm_jet_mul_le
        (contDiff_roundCylinderChristoffel hu' q d (a 0) (a i.succ)).contDiffAt
        (hTs (Function.update (fun l => a l.succ) i d)) j hD hg
        (fun l hl => hTb l (by omega) _)
      calc
        ‖iteratedFDeriv ℝ j (F i d) x‖ ≤ (2 : ℝ) ^ j * D * (C * A) := hmul
        _ ≤ (2 : ℝ) ^ m * D * (C * A) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) hj) hD)
            (mul_nonneg hC hA)
        _ = ((2 : ℝ) ^ m * D * C) * A := by ring
    have hsum :
        ‖iteratedFDeriv ℝ j (fun y => ∑ i, ∑ d, F i d y) x‖ ≤
          (2 + k : ℕ) * 3 * (((2 : ℝ) ^ m * D * C) * A) := by
      calc
        _ ≤ ∑ i, ‖iteratedFDeriv ℝ j (fun y => ∑ d, F i d y) x‖ :=
          norm_jet_sum_le (fun i => ContDiffAt.sum fun d _ => hFs i d) j
        _ ≤ ∑ i, ∑ d, ‖iteratedFDeriv ℝ j (F i d) x‖ :=
          Finset.sum_le_sum fun i _ => norm_jet_sum_le (hFs i) j
        _ ≤ ∑ _i : Fin (2 + k), ∑ _d : Fin 3, (((2 : ℝ) ^ m * D * C) * A) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun d _ => hFb i d
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have hd :
        ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ (T (fun i => a i.succ)) y
          (roundCylinderCoordinateBasis (a 0))) x‖ ≤ V * (C * A) := by
      apply (norm_jet_directional_le (hTs _) _ j).trans
      apply mul_le_mul
      · exact Finset.single_le_sum (fun i _ =>
          norm_nonneg (ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis i)))
          (Finset.mem_univ (a 0))
      · exact hTb (j + 1) (by omega) _
      · exact norm_nonneg _
      · exact hV
    have hsub := norm_jet_sub_le
      (f := fun y => fderiv ℝ (T (fun i => a i.succ)) y (roundCylinderCoordinateBasis (a 0)))
      (g := fun y => ∑ i, ∑ d, F i d y)
      (((hTs (fun i => a i.succ)).fderiv_right (by simp)).clm_apply contDiffAt_const)
      (ContDiffAt.sum fun i _ => ContDiffAt.sum fun d _ => hFs i d) j
    exact hsub.trans ((add_le_add hd hsum).trans_eq (by ring))

private theorem tensor_contraction_le
    {r : ℕ} (H : Matrix (Fin 3) (Fin 3) ℝ) (T : (Fin r → Fin 3) → ℝ)
    {D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hH : ∀ a b, ‖H a b‖ ≤ D) (hT : ∀ a, ‖T a‖ ≤ E) :
    (∑ a, ∑ b, (∏ i : Fin r, H (a i) (b i)) * T a * T b) ≤
      (∑ _a : Fin r → Fin 3, ∑ _b : Fin r → Fin 3, D ^ r) * E ^ 2 := by
  classical
  calc
    _ ≤ ∑ _a : Fin r → Fin 3, ∑ _b : Fin r → Fin 3, D ^ r * E ^ 2 := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      have hp : ‖∏ i : Fin r, H (a i) (b i)‖ ≤ D ^ r := by
        rw [norm_prod]
        calc
          _ ≤ ∏ _i : Fin r, D :=
            Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hH _ _)
          _ = _ := by simp
      calc
        _ ≤ ‖(∏ i : Fin r, H (a i) (b i)) * T a * T b‖ := le_abs_self _
        _ = ‖∏ i : Fin r, H (a i) (b i)‖ * ‖T a‖ * ‖T b‖ := by rw [norm_mul, norm_mul]
        _ ≤ D ^ r * E * E := mul_le_mul
          (mul_le_mul hp (hT a) (norm_nonneg _) (pow_nonneg hD _))
          (hT b) (norm_nonneg _) (mul_nonneg (pow_nonneg hD _) hE)
        _ = _ := by ring
    _ = _ := by simp only [Finset.sum_mul]

theorem exists_evolvingCylinder_finiteJet_bound
    {K : Set RoundCylinderCoordinates} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Icc (-1 : ℝ) 0,
      ∀ (q : UnitTwoSphere) (B : RoundCylinderTwoTensor)
      (x : RoundCylinderCoordinates), x ∈ K → ∀ A : ℝ, 0 ≤ A →
      (∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun y =>
        roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b -
          roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) x) →
      (∀ j, j ≤ m → ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b -
            roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) x‖ ≤ A) →
      (∑ k ∈ Finset.range (m + 1),
        roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) x
          (roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q) B k x))
        ≤ C * A ^ 2 := by
  classical
  rcases isEmpty_or_nonempty UnitTwoSphere with he | hn
  · let := he
    exact ⟨0, le_refl _, fun _ _ q => isEmptyElim q⟩
  let q₀ : UnitTwoSphere := hn.some
  obtain ⟨D, hD, hDb⟩ := exists_evolvingInverseGram_bound q₀ hK
  choose C hC hCb using fun k : ℕ => exists_covariant_jet_bound q₀ hK k 0
  let W : ℕ → ℝ := fun r => ∑ _a : Fin r → Fin 3, ∑ _b : Fin r → Fin 3, D ^ r
  have hW (r : ℕ) : 0 ≤ W r :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => pow_nonneg hD _
  refine ⟨∑ k ∈ Finset.range (m + 1), W (2 + k) * (C k) ^ 2,
    Finset.sum_nonneg (fun k _ => mul_nonneg (hW _) (sq_nonneg _)), ?_⟩
  intro u hu q B x hx A hA hs hb
  have hG (a b : Fin 3) :
      ‖(roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) x)⁻¹ a b‖ ≤ D := by
    rw [roundCylinderGram_eq_chart_center u q₀ q]
    exact hDb u hu a b x hx
  calc
    _ ≤ ∑ k ∈ Finset.range (m + 1), W (2 + k) * (C k * A) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      apply tensor_contraction_le _ _ hD (mul_nonneg (hC _) hA) hG
      intro a
      have ht := hCb k u hu q B x hx A hA hs
        (fun j hj => hb j (by have := Finset.mem_range.mp hk; omega)) 0 (le_refl _) a
      simpa only [norm_iteratedFDeriv_zero] using ht
    _ = (∑ k ∈ Finset.range (m + 1), W (2 + k) * (C k) ^ 2) * A ^ 2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem exists_evolvingCylinderJetErrorSquared_bound
    {J : Set ℝ} (hJ : IsCompact J) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Icc (-1 : ℝ) 0, ∀ (B : RoundCylinderTwoTensor) (z : RoundCylinderSpace),
      z.2 ∈ J → ∀ A : ℝ, 0 ≤ A →
      (∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun y =>
        roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
          roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)) →
      (∀ j, j ≤ m → ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
            roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)‖ ≤ A) →
      roundCylinderJetErrorSquared u B m z ≤ C * A ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_evolvingCylinder_finiteJet_bound
    ((isCompact_singleton (x := (0 : EuclideanSpace ℝ (Fin 2)))).prod hJ) m
  refine ⟨C, hC, ?_⟩
  intro u hu B z hz A hA hs hjet
  have h := hb u hu z.1 B (0, z.2) ⟨rfl, hz⟩ A hA hs hjet
  simpa only [roundCylinderJetErrorSquared,
    Poincare.Geometry.Riemannian.SpaceForm.sphere_chart_center] using h

end TerminalNeck
end PoincareConjecture
