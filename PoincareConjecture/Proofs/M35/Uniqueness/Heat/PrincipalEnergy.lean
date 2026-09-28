import PoincareConjecture.Proofs.M35.Uniqueness.Heat.DirichletInitialHeat
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawPrincipalExtension
import PoincareConjecture.Proofs.M03.Existence.DeTurckGeneratorRegularityNative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Topology SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

def dirichletPartial (K : Set V) (i : Fin n) : dirichletForm K →L[ℝ] L2 :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => L2) i).comp (dirichletGradient K)

@[simp] theorem dirichletPartial_into (K : Set V) (i : Fin n) (f : supportedTests K) :
    dirichletPartial K i (intoDirichletForm K f) =
      (∂_{EuclideanSpace.single i (1 : ℝ)} (f : 𝓢(V, ℝ))).toLp 2 volume := rfl

def principalEnergy (K : Set V) (A : Fin n → Fin n → 𝓢(V, ℝ))
    (u v : dirichletForm K) : ℝ :=
  ∑ i, ∑ j, inner ℝ (schwartzMultiplier (A i j) (dirichletPartial K i u))
    (dirichletPartial K j v)

theorem principalEnergy_continuous (K : Set V) (A : Fin n → Fin n → 𝓢(V, ℝ)) :
    Continuous (fun p : dirichletForm K × dirichletForm K => principalEnergy K A p.1 p.2) := by
  unfold principalEnergy
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact ((schwartzMultiplier (A i j)).continuous.comp
    ((dirichletPartial K i).continuous.comp continuous_fst)).inner
      ((dirichletPartial K j).continuous.comp continuous_snd)

theorem principalEnergy_symmetric (K : Set V) (A : Fin n → Fin n → 𝓢(V, ℝ))
    (hA : ∀ i j x, A i j x = A j i x) (u v : dirichletForm K) :
    principalEnergy K A u v = principalEnergy K A v u := by
  unfold principalEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have he : A i j = A j i := by ext x; exact hA i j x
  rw [he, schwartzMultiplier_selfAdjoint, real_inner_comm]

theorem dirichletForm_norm_sq (K : Set V) (u : dirichletForm K) :
    ‖u‖ ^ 2 = ‖dirichletInclusion K u‖ ^ 2 +
      ∑ i, ‖dirichletPartial K i u‖ ^ 2 := by
  change ‖(u : DirichletAmbient K)‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖dirichletInclusion K u‖ ^ 2 + ‖dirichletGradient K u‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

private theorem principalEnergy_coercive_test {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) {ell : ℝ}
    (hell : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (f : supportedTests K) :
    ell * (∑ i, ‖dirichletPartial K i (intoDirichletForm K f)‖ ^ 2) ≤
      principalEnergy K A (intoDirichletForm K f) (intoDirichletForm K f) := by
  let w : Fin n → 𝓢(V, ℝ) := fun i => ∂_{EuclideanSpace.single i (1 : ℝ)} (f : 𝓢(V, ℝ))
  have hp (x : V) : ell * (∑ i, (w i x) ^ 2) ≤
      ∑ i, ∑ j, A i j x * w i x * w j x := by
    by_cases hx : x ∈ K
    · exact hell x hx (fun i => w i x)
    · have hz (i : Fin n) : w i x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        exact fun h => hx ((SchwartzMap.tsupport_lineDerivOp_subset _ _).trans
          (supportedTests_tsupport_subset hK f) h)
      simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, Finset.sum_const_zero, le_refl]
  simpa only [principalEnergy, dirichletPartial_into, w] using
    schwartz_coercive_energy A w ell hp

theorem principalEnergy_coercive {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) {ell : ℝ}
    (hell : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (u : dirichletForm K) :
    ell * (∑ i, ‖dirichletPartial K i u‖ ^ 2) ≤ principalEnergy K A u u := by
  have hleft : Continuous (fun v : dirichletForm K =>
      ell * (∑ i, ‖dirichletPartial K i v‖ ^ 2)) := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro i _
    exact (dirichletPartial K i).continuous.norm.pow 2
  have hright : Continuous (fun v : dirichletForm K => principalEnergy K A v v) := by
    unfold principalEnergy
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact ((schwartzMultiplier (A i j)).continuous.comp
      (dirichletPartial K i).continuous).inner (dirichletPartial K j).continuous
  exact (intoDirichletForm_denseRange K).induction_on
    (p := fun v => ell * (∑ i, ‖dirichletPartial K i v‖ ^ 2) ≤ principalEnergy K A v v) u
    (isClosed_le hleft hright) (principalEnergy_coercive_test hK A hell)

def principalFormPairing (K : Set V) (A : Fin n → Fin n → 𝓢(V, ℝ))
    (u v : dirichletForm K) : ℝ :=
  inner ℝ (dirichletInclusion K u) (dirichletInclusion K v) + principalEnergy K A u v

theorem principalFormPairing_continuous (K : Set V) (A : Fin n → Fin n → 𝓢(V, ℝ)) :
    Continuous (fun p : dirichletForm K × dirichletForm K =>
      principalFormPairing K A p.1 p.2) :=
  (((dirichletInclusion K).continuous.comp continuous_fst).inner
    ((dirichletInclusion K).continuous.comp continuous_snd)).add
      (principalEnergy_continuous K A)

theorem principalFormPairing_coercive {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) {ell : ℝ}
    (hell : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (u : dirichletForm K) :
    min 1 ell * ‖u‖ ^ 2 ≤ principalFormPairing K A u u := by
  have hgrad := principalEnergy_coercive hK A hell u
  have hs : 0 ≤ ∑ i : Fin n, ‖dirichletPartial K i u‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hv := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) ell)
    (sq_nonneg ‖dirichletInclusion K u‖)
  have hd := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) ell) hs
  rw [dirichletForm_norm_sq]
  unfold principalFormPairing
  rw [real_inner_self_eq_norm_sq]
  nlinarith only [hv, hd, hgrad]

theorem exists_raw_coercive_dirichlet_energy (g : RiemannianMetric n V)
    {K : Set V} (hK : IsCompact K) :
    ∃ A : Fin n → Fin n → 𝓢(V, ℝ), ∃ c : ℝ, 0 < c ∧
      (∀ i j x, A i j x = A j i x) ∧
      (∀ i j x, x ∈ K → A i j x = (rawCoordinateGram g x)⁻¹ i j) ∧
      ∀ u : dirichletForm K, c * ‖u‖ ^ 2 ≤ principalFormPairing K A u u := by
  obtain ⟨A, ell, hEll, hA, hAK, hell⟩ := exists_raw_principal_schwartz_coefficients g hK
  exact ⟨A, min 1 ell, lt_min zero_lt_one hEll, hA, hAK,
    principalFormPairing_coercive hK.isClosed A hell⟩

end PoincareConjecture.M35.Uniqueness.Heat
