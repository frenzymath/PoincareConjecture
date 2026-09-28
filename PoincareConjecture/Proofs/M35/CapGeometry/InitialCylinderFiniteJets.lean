import PoincareConjecture.Proofs.M35.Thm12_28.NeckFiniteMetricJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M35

private theorem tendsto_coordinate_jet_of_components {r : ℕ}
    {F : ℕ → RoundCylinderCoordinates [×r]→L[ℝ] ℝ}
    (h : ∀ a : Fin r → Fin 3,
      Tendsto (fun k => F k (fun j => roundCylinderCoordinateBasis (a j)))
        atTop (𝓝 0)) : Tendsto F atTop (𝓝 0) := by
  let ev : (RoundCylinderCoordinates [×r]→L[ℝ] ℝ) →ₗ[ℝ]
      ((Fin r → Fin 3) → ℝ) :=
    { toFun := fun T a => T (fun j => roundCylinderCoordinateBasis (a j))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map cylinderCoordinateEquiv.toLinearEquiv
  have hb (i : Fin 3) : b i = roundCylinderCoordinateBasis i := cylinderCoordinateEquiv_basis i
  have hinj : Function.Injective ev := by
    intro T S hTS
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    apply Module.Basis.ext_multilinear (fun _ => b)
    intro a
    change T (fun j => b (a j)) = S (fun j => b (a j))
    simp only [hb]
    exact congrFun hTS a
  let : FiniteDimensional ℝ (RoundCylinderCoordinates [×r]→L[ℝ] ℝ) :=
    FiniteDimensional.of_injective ev hinj
  have hev := ev.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  apply hev.isInducing.tendsto_nhds_iff.mpr
  change Tendsto (fun (k : ℕ) (a : Fin r → Fin 3) =>
    F k (fun j => roundCylinderCoordinateBasis (a j)))
      atTop (𝓝 (fun _ : Fin r → Fin 3 => (0 : ℝ)))
  exact tendsto_pi_nhds.mpr h




theorem cylinder_covariant_error_jets_tendsto_zero
    (epsilon u s : ℕ → ℝ) (B : ℕ → RoundCylinderTwoTensor)
    (q : ℕ → UnitTwoSphere) (s₀ : ℝ) (M : ℕ)
    (he : ∀ k, 0 < epsilon k) (hlo : ∀ k, -1 ≤ u k) (hu : ∀ k, u k < 1)
    (hs : ∀ k, s k ∈ Ioo (-(epsilon k)⁻¹) (epsilon k)⁻¹)
    (hclose : ∀ k, RoundCylinderClose (epsilon k) (u k) (B k))
    (hdegree : ∀ k, M ≤ ⌊(epsilon k)⁻¹⌋₊)
    (hezero : Tendsto epsilon atTop (𝓝 0)) (hslim : Tendsto s atTop (𝓝 s₀))
    (r n : ℕ) (hnr : n + r ≤ M) (a : Fin (2 + n) → Fin 3) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun y : RoundCylinderCoordinates =>
      roundCylinderIteratedDerivative (u k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k))
        (B k) n y a) (0, s k)) atTop (𝓝 0) := by
  let T (n k : ℕ) (a : Fin (2 + n) → Fin 3) (y : RoundCylinderCoordinates) :=
    roundCylinderIteratedDerivative (u k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k))
      (B k) n y a
  let G (i j l : Fin 3) (y : RoundCylinderCoordinates) :=
    roundCylinderChristoffel 0 (chartAt (EuclideanSpace ℝ (Fin 2)) (q 0)) y i j l
  have hG (i j l : Fin 3) : ContDiff ℝ ∞ (G i j l) :=
    contDiff_roundCylinderChristoffel zero_lt_one (q 0) i j l
  have hGeq (k : ℕ) (y : RoundCylinderCoordinates) (i j l : Fin 3) :
      roundCylinderChristoffel (u k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y i j l =
        G i j l y := by
    change _ = roundCylinderChristoffel 0 (chartAt (EuclideanSpace ℝ (Fin 2)) (q 0)) y i j l
    rw [roundCylinderChristoffel_eq (hu k), roundCylinderChristoffel_eq zero_lt_one]
  have hp : Tendsto (fun k => ((0, s k) : RoundCylinderCoordinates)) atTop (𝓝 (0, s₀)) :=
    tendsto_const_nhds.prodMk_nhds hslim
  have hT (n k : ℕ) (a : Fin (2 + n) → Fin 3) : ContDiffAt ℝ ∞ (T n k a) (0, s k) :=
    contDiffAt_roundCylinderIteratedDerivative (hu k) (q k) (B k) (0, s k)
      (fun i j => (hclose k).contDiffAt_coefficient (q k) (0, s k) (hs k) i j) n a
  change Tendsto (fun k => iteratedFDeriv ℝ r (T n k a) (0, s k)) atTop (𝓝 0)
  induction r using Nat.strong_induction_on generalizing n with
  | h r ih =>
    cases r with
    | zero =>
      apply squeeze_zero_norm
        (fun k => ?_) (by simpa only [mul_zero] using hezero.const_mul ((2 : ℝ) ^ (2 + n)))
      have hn : n ≤ ⌊(epsilon k)⁻¹⌋₊ := (by omega : n ≤ M).trans (hdegree k)
      have h := (hclose k).component_abs_lt (he k) (hlo k) (hu k)
        (z := (q k, s k)) (hs k) hn a
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, T, sphere_chart_center] using h.le
    | succ r =>
      apply tendsto_coordinate_jet_of_components
      intro v
      let d := v (Fin.last r)
      let aa : Fin (2 + (n + 1)) → Fin 3 := Fin.cons d a
      let J (k : ℕ) (i : Fin (2 + n)) (j : Fin 3) (y : RoundCylinderCoordinates) :=
        G j d (a i) y * T n k (Function.update a i j) y
      have hJ (k : ℕ) (i : Fin (2 + n)) (j : Fin 3) :
          ContDiffAt ℝ ∞ (J k i j) (0, s k) :=
        (hG j d (a i)).contDiffAt.mul (hT n k (Function.update a i j))
      have hJlim (i : Fin (2 + n)) (j : Fin 3) :
          Tendsto (fun k => iteratedFDeriv ℝ r (J k i j) (0, s k)) atTop (𝓝 0) := by
        have h := tendsto_iteratedFDeriv_mul_of_jets
          (f := fun _ => G j d (a i)) (f₀ := G j d (a i))
          (g := fun k => T n k (Function.update a i j)) (g₀ := fun _ => (0 : ℝ))
          (p₀ := (0, s₀)) r (hG j d (a i)).contDiffAt contDiffAt_const
          (Eventually.of_forall fun _ => (hG j d (a i)).contDiffAt)
          (Eventually.of_forall fun k => hT n k (Function.update a i j))
          (fun m _ => ((hG j d (a i)).contDiffAt.continuousAt_iteratedFDeriv
            (by exact_mod_cast le_top (a := (m : ℕ∞)))).tendsto.comp hp)
          (fun m hm => by
            simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using
              ih m (by omega) n (by omega) (Function.update a i j))
        simpa only [mul_zero, iteratedFDeriv_fun_zero, Pi.zero_apply] using h
      have hrec (k : ℕ) : (fun y => fderiv ℝ (T n k a) y (roundCylinderCoordinateBasis d)) =
          fun y => T (n + 1) k aa y + ∑ i : Fin (2 + n), ∑ j : Fin 3, J k i j y := by
        funext y
        simp only [T, aa, roundCylinderIteratedDerivative, roundCylinderTensorDerivative,
          Fin.cons_zero, Fin.cons_succ, J, hGeq]
        exact (sub_add_cancel _ _).symm
      have hderiv : Tendsto (fun k => iteratedFDeriv ℝ r
          (fun y => fderiv ℝ (T n k a) y (roundCylinderCoordinateBasis d)) (0, s k))
          atTop (𝓝 0) := by
        have hsum : Tendsto (fun k => ∑ i : Fin (2 + n), ∑ j : Fin 3,
            iteratedFDeriv ℝ r (J k i j) (0, s k)) atTop
            (𝓝 (∑ _i : Fin (2 + n), ∑ _j : Fin 3,
              (0 : RoundCylinderCoordinates [×r]→L[ℝ] ℝ))) :=
          tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => hJlim i j))
        simp only [Finset.sum_const_zero] at hsum
        have hlim := (ih r (Nat.lt_succ_self r) (n + 1) (by omega) aa).add hsum
        simp only [add_zero] at hlim
        apply hlim.congr'
        apply Eventually.of_forall
        intro k
        have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
        change iteratedFDeriv ℝ r (T (n + 1) k aa) (0, s k) +
          ∑ i : Fin (2 + n), ∑ j : Fin 3, iteratedFDeriv ℝ r (J k i j) (0, s k) =
          iteratedFDeriv ℝ r
          (fun y => fderiv ℝ (T n k a) y (roundCylinderCoordinateBasis d)) (0, s k)
        rw [hrec k, fun_iteratedFDeriv_add_apply ((hT (n + 1) k aa).of_le hr)
          ((ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => hJ k i j).of_le hr),
          iteratedFDeriv_fun_sum_apply (fun i _ =>
            (ContDiffAt.sum fun j _ => hJ k i j).of_le hr)]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [iteratedFDeriv_fun_sum_apply (fun j _ => (hJ k i j).of_le hr)]
      apply squeeze_zero_norm (fun k => ?_) (by simpa only [norm_zero] using hderiv.norm)
      rw [iteratedFDeriv_directional_apply r (hT n k a)]
      have h := (iteratedFDeriv ℝ r
        (fun y => fderiv ℝ (T n k a) y (roundCylinderCoordinateBasis d)) (0, s k)).le_opNorm
          (Fin.init (fun j => roundCylinderCoordinateBasis (v j)))
      have hb (i : Fin 3) : ‖roundCylinderCoordinateBasis i‖ = 1 := by
        fin_cases i <;> simp [roundCylinderCoordinateBasis, Prod.norm_def]
      simpa only [Fin.init_def, hb, Finset.prod_const_one, mul_one] using h



theorem cylinder_metric_error_jets_tendsto_zero
    (epsilon u s : ℕ → ℝ) (B : ℕ → RoundCylinderTwoTensor)
    (q : ℕ → UnitTwoSphere) (s₀ : ℝ) (M : ℕ)
    (he : ∀ k, 0 < epsilon k) (hlo : ∀ k, -1 ≤ u k) (hu : ∀ k, u k < 1)
    (hs : ∀ k, s k ∈ Ioo (-(epsilon k)⁻¹) (epsilon k)⁻¹)
    (hclose : ∀ k, RoundCylinderClose (epsilon k) (u k) (B k))
    (hdegree : ∀ k, M ≤ ⌊(epsilon k)⁻¹⌋₊)
    (hezero : Tendsto epsilon atTop (𝓝 0)) (hslim : Tendsto s atTop (𝓝 s₀))
    (r : ℕ) (hr : r ≤ M) (i j : Fin 3) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun y : RoundCylinderCoordinates =>
      roundCylinderTensorCoefficient (B k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y i j -
        roundCylinderGram (u k) (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y i j)
          (0, s k)) atTop (𝓝 0) := by
  exact cylinder_covariant_error_jets_tendsto_zero epsilon u s B q s₀ M he hlo hu hs
    hclose hdegree hezero hslim r 0 (by omega) ![i, j]

end PoincareConjecture.M35
