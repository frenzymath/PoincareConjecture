import PoincareConjecture.Proofs.M35.Thm12_28.CylinderChristoffel
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderJetNorm
import PoincareConjecture.Proofs.M35.Mathlib.FiniteJetOperations










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.M35



theorem contDiffAt_roundCylinderIteratedDerivative {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (B : RoundCylinderTwoTensor) (p : RoundCylinderCoordinates)
    (hB : ∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) p)
    (n : ℕ) (a : Fin (2 + n) → Fin 3) :
    ContDiffAt ℝ ∞ (fun y => roundCylinderIteratedDerivative u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) B n y a) p := by
  induction n with
  | zero => exact (hB (a 0) (a 1)).sub (contDiff_roundCylinderGram u q _ _).contDiffAt
  | succ n ih =>
    apply ContDiffAt.sub
    · exact ((ih (fun i => a i.succ)).fderiv_right (by simp)).clm_apply contDiffAt_const
    · exact ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ =>
        (contDiff_roundCylinderChristoffel hu q j (a 0) (a i.succ)).contDiffAt.mul
          (ih (Function.update (fun k => a k.succ) i j))))

private theorem difference_succ_germ {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (B C : RoundCylinderTwoTensor) (p : RoundCylinderCoordinates)
    (hB : ∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) p)
    (hC : ∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient C (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) p)
    (n : ℕ) (a : Fin (2 + (n + 1)) → Fin 3) :
    (fun y => roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        B (n + 1) y a -
      roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q) C (n + 1) y a)
      =ᶠ[𝓝 p] (fun y =>
        fderiv ℝ (fun z => roundCylinderIteratedDerivative u
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) B n z (fun i => a i.succ) -
          roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
            C n z (fun i => a i.succ)) y (roundCylinderCoordinateBasis (a 0)) -
        ∑ i : Fin (2 + n), ∑ j : Fin 3,
          roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
            y j (a 0) (a i.succ) *
          (roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
              B n y (Function.update (fun k => a k.succ) i j) -
            roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
              C n y (Function.update (fun k => a k.succ) i j))) := by
  have hb := ((contDiffAt_roundCylinderIteratedDerivative hu q B p hB n
    (fun i => a i.succ)).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  have hc := ((contDiffAt_roundCylinderIteratedDerivative hu q C p hC n
    (fun i => a i.succ)).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  filter_upwards [hb, hc] with y hby hcy
  rw [fderiv_fun_sub (hby.differentiableAt (by simp)) (hcy.differentiableAt (by simp))]
  simp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative,
    sub_apply, mul_sub, Finset.sum_sub_distrib]
  exact sub_sub_sub_comm _ _ _ _




theorem roundCylinderIteratedDerivative_difference_jets_tendsto_zero
    (order : ℕ) (u : ℕ → ℝ) (hu : ∀ k, u k < 1) (q : ℕ → UnitTwoSphere)
    (B C : ℕ → RoundCylinderTwoTensor) (p : ℕ → RoundCylinderCoordinates)
    (p₀ : RoundCylinderCoordinates) (hp : Tendsto p atTop (𝓝 p₀))
    (hB : ∀ k a b, ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient
      (B k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y a b) (p k))
    (hC : ∀ k a b, ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient
      (C k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y a b) (p k))
    (hjet : ∀ m ≤ order, ∀ a b : Fin 3, Tendsto (fun k => iteratedFDeriv ℝ m
      (fun y => roundCylinderTensorCoefficient (B k)
        (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y a b -
        roundCylinderTensorCoefficient (C k)
          (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y a b) (p k)) atTop (𝓝 0))
    (n r : ℕ) (hnr : n + r ≤ order) (a : Fin (2 + n) → Fin 3) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun y =>
      roundCylinderIteratedDerivative (u k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k))
          (B k) n y a -
        roundCylinderIteratedDerivative (u k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k))
          (C k) n y a) (p k)) atTop (𝓝 0) := by
  let T (n k : ℕ) (a : Fin (2 + n) → Fin 3) (y : RoundCylinderCoordinates) :=
    roundCylinderIteratedDerivative (u k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k))
        (B k) n y a -
      roundCylinderIteratedDerivative (u k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k))
        (C k) n y a
  let G (a b d : Fin 3) (y : RoundCylinderCoordinates) :=
    roundCylinderChristoffel 0 (chartAt (EuclideanSpace ℝ (Fin 2)) (q 0)) y a b d
  have hG (a b d : Fin 3) : ContDiff ℝ ∞ (G a b d) :=
    contDiff_roundCylinderChristoffel zero_lt_one (q 0) a b d
  have hGeq (k : ℕ) (a b d : Fin 3) (y : RoundCylinderCoordinates) :
      roundCylinderChristoffel (u k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y a b d =
        G a b d y := by
    change _ = roundCylinderChristoffel 0 _ y a b d
    rw [roundCylinderChristoffel_eq (hu k), roundCylinderChristoffel_eq zero_lt_one]
  have hT (n k : ℕ) (a : Fin (2 + n) → Fin 3) : ContDiffAt ℝ ∞ (T n k a) (p k) :=
    (contDiffAt_roundCylinderIteratedDerivative (hu k) (q k) (B k) (p k) (hB k) n a).sub
      (contDiffAt_roundCylinderIteratedDerivative (hu k) (q k) (C k) (p k) (hC k) n a)
  change Tendsto (fun k => iteratedFDeriv ℝ r (T n k a) (p k)) atTop (𝓝 0)
  induction n generalizing r with
  | zero =>
    simpa only [T, roundCylinderIteratedDerivative, sub_sub_sub_cancel_right] using
      hjet r (by omega) (a 0) (a 1)
  | succ n ih =>
    let tail : Fin (2 + n) → Fin 3 := fun i => a i.succ
    let upd (i : Fin (2 + n)) (j : Fin 3) := Function.update tail i j
    let D (k : ℕ) (y : RoundCylinderCoordinates) :=
      fderiv ℝ (T n k tail) y (roundCylinderCoordinateBasis (a 0))
    let H (k : ℕ) (i : Fin (2 + n)) (j : Fin 3) (y : RoundCylinderCoordinates) :=
      G j (a 0) (a i.succ) y * T n k (upd i j) y
    have hD (k : ℕ) : ContDiffAt ℝ ∞ (D k) (p k) :=
      ((hT n k tail).fderiv_right (by simp)).clm_apply contDiffAt_const
    have hH (k : ℕ) (i : Fin (2 + n)) (j : Fin 3) :
        ContDiffAt ℝ ∞ (H k i j) (p k) :=
      (hG j (a 0) (a i.succ)).contDiffAt.mul (hT n k (upd i j))
    have hsum (k : ℕ) : ContDiffAt ℝ ∞
        (fun y => ∑ i : Fin (2 + n), ∑ j : Fin 3, H k i j y) (p k) :=
      ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ => hH k i j))
    have hrec (k : ℕ) : T (n + 1) k a =ᶠ[𝓝 (p k)]
        (fun y => D k y - ∑ i : Fin (2 + n), ∑ j : Fin 3, H k i j y) := by
      simpa only [T, D, H, tail, upd, hGeq] using
        difference_succ_germ (hu k) (q k) (B k) (C k) (p k) (hB k) (hC k) n a
    have hdlim : Tendsto (fun k => iteratedFDeriv ℝ r (D k) (p k)) atTop (𝓝 0) := by
      have h := tendsto_iteratedFDeriv_fderiv_apply_of_jet
        (f := fun k => T n k tail) (f₀ := fun _ => (0 : ℝ)) (p₀ := p₀)
        r (roundCylinderCoordinateBasis (a 0)) contDiffAt_const
        (Eventually.of_forall fun k => hT n k tail) (by
          simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using ih (r + 1) (by omega) tail)
      simpa using h
    have hhlim (i : Fin (2 + n)) (j : Fin 3) :
        Tendsto (fun k => iteratedFDeriv ℝ r (H k i j) (p k)) atTop (𝓝 0) := by
      have h := tendsto_iteratedFDeriv_mul_of_jets
        (f := fun _ => G j (a 0) (a i.succ)) (f₀ := G j (a 0) (a i.succ))
        (g := fun k => T n k (upd i j)) (g₀ := fun _ => (0 : ℝ)) (p₀ := p₀) r
        (hG j (a 0) (a i.succ)).contDiffAt contDiffAt_const
        (Eventually.of_forall fun _ => (hG j (a 0) (a i.succ)).contDiffAt)
        (Eventually.of_forall fun k => hT n k (upd i j))
        (fun m _ => ((hG j (a 0) (a i.succ)).contDiffAt.continuousAt_iteratedFDeriv
          (by exact_mod_cast le_top (a := (m : ℕ∞)))).tendsto.comp hp)
        (fun m hm => by
          simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using ih m (by omega) (upd i j))
      simpa only [mul_zero, iteratedFDeriv_fun_zero, Pi.zero_apply] using h
    have hsums : Tendsto (fun k => ∑ i : Fin (2 + n), ∑ j : Fin 3,
        iteratedFDeriv ℝ r (H k i j) (p k)) atTop
        (𝓝 (∑ _i : Fin (2 + n), ∑ _j : Fin 3,
          (0 : RoundCylinderCoordinates [×r]→L[ℝ] ℝ))) := by
      apply tendsto_finsetSum
      intro i _
      exact tendsto_finsetSum _ (fun j _ => hhlim i j)
    simp only [Finset.sum_const_zero] at hsums
    have heq (k : ℕ) : iteratedFDeriv ℝ r (T (n + 1) k a) (p k) =
        iteratedFDeriv ℝ r (D k) (p k) -
          ∑ i : Fin (2 + n), ∑ j : Fin 3, iteratedFDeriv ℝ r (H k i j) (p k) := by
      have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
      rw [((hrec k).iteratedFDeriv ℝ r).eq_of_nhds,
        fun_iteratedFDeriv_sub_apply ((hD k).of_le hr) ((hsum k).of_le hr),
        iteratedFDeriv_fun_sum_apply (fun i _ =>
          (ContDiffAt.sum (fun j _ => hH k i j)).of_le hr)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact iteratedFDeriv_fun_sum_apply (fun j _ => (hH k i j).of_le hr)
    have hout := hdlim.sub hsums
    simp only [sub_zero] at hout
    exact hout.congr' (Eventually.of_forall fun k => (heq k).symm)



noncomputable def roundCylinderJetDifferenceSquared (u : ℝ) (B C : RoundCylinderTwoTensor)
    (order : ℕ) (z : RoundCylinderSpace) : ℝ :=
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let p : RoundCylinderCoordinates := (c z.1, z.2)
  ∑ n ∈ Finset.range (order + 1), roundCylinderTensorNormSquared u c p
    (fun a => roundCylinderIteratedDerivative u c B n p a -
      roundCylinderIteratedDerivative u c C n p a)



theorem roundCylinderJetDifferenceSquared_nonneg {u : ℝ} (hu : u < 1)
    (B C : RoundCylinderTwoTensor) (order : ℕ) (z : RoundCylinderSpace) :
    0 ≤ roundCylinderJetDifferenceSquared u B C order z :=
  Finset.sum_nonneg (fun _ _ => roundCylinderTensorNormSquared_nonneg hu z.1 z.2 _)



theorem roundCylinderTensorNormSquared_le_twice {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (s : ℝ) {r : ℕ} (T S : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) T ≤
      2 * roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) S +
      2 * roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) (fun a => T a - S a) := by
  simp only [roundCylinderTensorNormSquared_center hu, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have hw : 0 ≤ ∏ i, ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] (a i) :=
    Finset.prod_nonneg (fun i _ => (roundCylinderInverseWeight_pos hu (a i)).le)
  have hs : (T a) ^ 2 ≤ 2 * (S a) ^ 2 + 2 * (T a - S a) ^ 2 := by
    nlinarith [sq_nonneg (T a - 2 * S a)]
  convert mul_le_mul_of_nonneg_left hs hw using 1
  ring




theorem roundCylinderJetErrorSquared_le_twice {u : ℝ} (hu : u < 1)
    (B C : RoundCylinderTwoTensor) (order : ℕ) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared u B order z ≤
      2 * roundCylinderJetErrorSquared u C order z +
        2 * roundCylinderJetDifferenceSquared u B C order z := by
  unfold roundCylinderJetErrorSquared roundCylinderJetDifferenceSquared
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ =>
    roundCylinderTensorNormSquared_le_twice hu z.1 z.2 _ _)




theorem roundCylinderJetDifferenceSquared_tendsto_zero
    (order : ℕ) (u : ℕ → ℝ) (hu : ∀ k, u k < 1) (u₀ : ℝ) (hu₀ : u₀ < 1)
    (hulim : Tendsto u atTop (𝓝 u₀)) (q : ℕ → UnitTwoSphere)
    (B C : ℕ → RoundCylinderTwoTensor) (s : ℕ → ℝ) (s₀ : ℝ)
    (hs : Tendsto s atTop (𝓝 s₀))
    (hB : ∀ k a b, ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient
      (B k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y a b) (0, s k))
    (hC : ∀ k a b, ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient
      (C k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y a b) (0, s k))
    (hjet : ∀ m ≤ order, ∀ a b : Fin 3, Tendsto (fun k => iteratedFDeriv ℝ m
      (fun y => roundCylinderTensorCoefficient (B k)
        (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y a b -
        roundCylinderTensorCoefficient (C k)
          (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y a b) (0, s k)) atTop (𝓝 0)) :
    Tendsto (fun k => roundCylinderJetDifferenceSquared (u k) (B k) (C k)
      order (q k, s k)) atTop (𝓝 0) := by
  have hw (a : Fin 3) : Tendsto
      (fun k => ![(2 * (1 - u k))⁻¹, (2 * (1 - u k))⁻¹, 1] a) atTop
      (𝓝 (![(2 * (1 - u₀))⁻¹, (2 * (1 - u₀))⁻¹, 1] a)) := by
    have hinv := (tendsto_const_nhds.mul (tendsto_const_nhds.sub hulim)).inv₀
      (show (2 : ℝ) * (1 - u₀) ≠ 0 by positivity)
    fin_cases a <;> first | exact hinv | exact tendsto_const_nhds
  have hcomponent (n : ℕ) (hn : n ≤ order) (a : Fin (2 + n) → Fin 3) :
      Tendsto (fun k => roundCylinderIteratedDerivative (u k)
        (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) (B k) n (0, s k) a -
        roundCylinderIteratedDerivative (u k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k))
          (C k) n (0, s k) a) atTop (𝓝 0) := by
    have h := roundCylinderIteratedDerivative_difference_jets_tendsto_zero order u hu q B C
      (fun k => (0, s k)) (0, s₀) (tendsto_const_nhds.prodMk_nhds hs)
      hB hC hjet n 0 (by omega) a
    have he := ((continuousMultilinearCurryFin0 ℝ RoundCylinderCoordinates ℝ).continuous.tendsto
      0).comp h
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply, map_zero] using he
  have hterm (n : ℕ) (hn : n ∈ Finset.range (order + 1)) :
      Tendsto (fun k => ∑ a : Fin (2 + n) → Fin 3,
        (∏ i, ![(2 * (1 - u k))⁻¹, (2 * (1 - u k))⁻¹, 1] (a i)) *
          (roundCylinderIteratedDerivative (u k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k))
              (B k) n (0, s k) a -
            roundCylinderIteratedDerivative (u k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k))
              (C k) n (0, s k) a) ^ 2) atTop (𝓝 0) := by
    have ht (a : Fin (2 + n) → Fin 3) :=
      (tendsto_finsetProd Finset.univ (fun i _ => hw (a i))).mul
        ((hcomponent n (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn) a).pow 2)
    have hz := tendsto_finsetSum Finset.univ (fun a _ => ht a)
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero] using hz
  have hsum := tendsto_finsetSum (Finset.range (order + 1)) hterm
  simp only [Finset.sum_const_zero] at hsum
  convert hsum using 1
  funext k
  unfold roundCylinderJetDifferenceSquared
  simp only [sphere_chart_center]
  apply Finset.sum_congr rfl
  intro n _
  simpa only [sphere_chart_center] using roundCylinderTensorNormSquared_center (hu k)
    (q k) (s k) (fun a => roundCylinderIteratedDerivative (u k)
      (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) (B k) n (0, s k) a -
        roundCylinderIteratedDerivative (u k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k))
          (C k) n (0, s k) a)

end PoincareConjecture.M35
