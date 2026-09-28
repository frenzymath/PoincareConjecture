import PoincareConjecture.Proofs.M03.Existence.EuclideanLocalIntegrationByPartsNative

set_option autoImplicit false
set_option maxHeartbeats 1400000

open MeasureTheory Set Filter LineDeriv
open scoped Topology SchwartzMap LineDeriv ContDiff

noncomputable section

namespace PoincareConjecture.EuclideanDerivativeNative

variable {n : ℕ} {iota : Type*} [Fintype iota]

local notation "E" => EuclideanSpace ℝ (Fin n)

def coefficientFirstOrder (a : iota → E → ℝ) (v : iota → E) (f : E → ℝ) (x : E) : ℝ :=
  ∑ i, a i x * fderiv ℝ f x (v i)

def densityDivergence (ρ : E → ℝ) (a : iota → E → ℝ) (v : iota → E) (x : E) : ℝ :=
  (ρ x)⁻¹ * ∑ i, fderiv ℝ (fun y => ρ y * a i y) x (v i)

def densityAdjointTest (ρ : E → ℝ) (a : iota → E → ℝ) (v : iota → E)
    (η : E → ℝ) (x : E) : ℝ :=
  -(ρ x)⁻¹ * ∑ i, fderiv ℝ (fun y => η y * (ρ y * a i y)) x (v i)

theorem coefficientFirstOrder_contDiffOn {U : Set E} (hU : IsOpen U)
    {a : iota → E → ℝ} (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U)
    (v : iota → E) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (coefficientFirstOrder a v f) U :=
  ContDiffOn.sum (fun i _ => (ha i).mul
    ((hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const))

theorem densityDivergence_contDiffOn {U : Set E} (hU : IsOpen U)
    {ρ : E → ℝ} (hρ : ContDiffOn ℝ ∞ ρ U) (hρpos : ∀ x ∈ U, 0 < ρ x)
    {a : iota → E → ℝ} (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (v : iota → E) :
    ContDiffOn ℝ ∞ (densityDivergence ρ a v) U :=
  (hρ.inv (fun x hx => (hρpos x hx).ne')).mul
    (ContDiffOn.sum (fun i _ =>
      (((hρ.mul (ha i)).fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const)))

theorem densityAdjointTest_eq {U : Set E} (hU : IsOpen U)
    {ρ : E → ℝ} (hρ : ContDiffOn ℝ ∞ ρ U) (hρpos : ∀ x ∈ U, 0 < ρ x)
    {a : iota → E → ℝ} (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (v : iota → E)
    {η : E → ℝ} (hη : ContDiffOn ℝ ∞ η U) {x : E} (hx : x ∈ U) :
    densityAdjointTest ρ a v η x =
      -coefficientFirstOrder a v η x - densityDivergence ρ a v x * η x := by
  classical
  have hηdiff := (hη.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hdiff (i : iota) := ((hρ.mul (ha i)).contDiffAt (hU.mem_nhds hx)).differentiableAt
    (by simp)
  have hsum : (∑ i, fderiv ℝ (fun y => η y * (ρ y * a i y)) x (v i)) =
      η x * (∑ i, fderiv ℝ (fun y => ρ y * a i y) x (v i)) +
        ρ x * (∑ i, a i x * fderiv ℝ η x (v i)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [fderiv_fun_mul hηdiff (hdiff i)]
    change η x * fderiv ℝ (fun y => ρ y * a i y) x (v i) +
        (ρ x * a i x) * fderiv ℝ η x (v i) = _
    ring
  unfold densityAdjointTest coefficientFirstOrder densityDivergence
  rw [hsum]
  field_simp [(hρpos x hx).ne']
  ring

theorem densityAdjointTest_contDiffOn {U : Set E} (hU : IsOpen U)
    {ρ : E → ℝ} (hρ : ContDiffOn ℝ ∞ ρ U) (hρpos : ∀ x ∈ U, 0 < ρ x)
    {a : iota → E → ℝ} (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (v : iota → E)
    {η : E → ℝ} (hη : ContDiffOn ℝ ∞ η U) :
    ContDiffOn ℝ ∞ (densityAdjointTest ρ a v η) U := by
  apply (((coefficientFirstOrder_contDiffOn hU ha v hη).neg).sub
    ((densityDivergence_contDiffOn hU hρ hρpos ha v).mul hη)).congr
  intro x hx
  exact densityAdjointTest_eq hU hρ hρpos ha v hη hx

theorem integral_weightedFirstOrder_eq_adjoint (η : 𝓢(E, ℝ)) (hη : HasCompactSupport η)
    {U : Set E} (hU : IsOpen U) (hηU : tsupport η ⊆ U)
    {ρ : E → ℝ} (hρ : ContDiffOn ℝ ∞ ρ U) (hρpos : ∀ x ∈ U, 0 < ρ x)
    {a : iota → E → ℝ} (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (v : iota → E)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    (∫ x, ρ x * coefficientFirstOrder a v f x * η x) =
      ∫ x, ρ x * f x * densityAdjointTest ρ a v η x := by
  classical
  let θ : iota → 𝓢(E, ℝ) := fun i =>
    cutoffSchwartz η hη hU hηU (fun x => ρ x * a i x) (hρ.mul (ha i))
  have hθ (i : iota) : HasCompactSupport (θ i) := hη.mul_right
  have hθsub (i : iota) : tsupport (θ i) ⊆ tsupport η := tsupport_mul_subset_left
  have hθU (i : iota) : tsupport (θ i) ⊆ U := (hθsub i).trans hηU
  have hleftI (i : iota) : Integrable (fun x => fderiv ℝ f x (v i) * θ i x) volume :=
    integrable_local_mul_schwartz (θ i) (hθ i) hU (hθU i)
      ((hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const)
  have hrightI (i : iota) : Integrable (fun x => f x * fderiv ℝ (θ i) x (v i)) volume :=
    integrable_local_mul_schwartz (∂_{v i} (θ i))
      (hasCompactSupport_schwartzLineDeriv (θ i) (hθ i) (v i)) hU
      ((SchwartzMap.tsupport_lineDerivOp_subset (v i) (θ i)).trans (hθU i)) hf
  have hpair (i : iota) :
      (∫ x, fderiv ℝ f x (v i) * θ i x) = -(∫ x, f x * fderiv ℝ (θ i) x (v i)) := by
    have h := local_integral_mul_fderiv (θ i) (hθ i) hU (hθU i) hf (v i)
    linarith
  have hleft (x : E) : ρ x * coefficientFirstOrder a v f x * η x =
      ∑ i, fderiv ℝ f x (v i) * θ i x := by
    unfold coefficientFirstOrder
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    change ρ x * (a i x * fderiv ℝ f x (v i)) * η x =
      fderiv ℝ f x (v i) * (η x * (ρ x * a i x))
    ring
  have hright (x : E) : ρ x * f x * densityAdjointTest ρ a v η x =
      -(∑ i, f x * fderiv ℝ (θ i) x (v i)) := by
    change ρ x * f x * (-(ρ x)⁻¹ * ∑ i, fderiv ℝ (θ i) x (v i)) = _
    rw [← Finset.mul_sum]
    by_cases hx : x ∈ U
    · field_simp [(hρpos x hx).ne']
    · have hsum : (∑ i, fderiv ℝ (θ i) x (v i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [fderiv_of_notMem_tsupport ℝ (fun hxt => hx (hθU i hxt)), ContinuousLinearMap.zero_apply]
      rw [hsum]
      ring
  calc
    _ = ∫ x, ∑ i, fderiv ℝ f x (v i) * θ i x :=
      integral_congr_ae (Eventually.of_forall hleft)
    _ = -(∫ x, ∑ i, f x * fderiv ℝ (θ i) x (v i)) := by
      rw [integral_finsetSum Finset.univ (fun i _ => hleftI i),
        integral_finsetSum Finset.univ (fun i _ => hrightI i), ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => hpair i)
    _ = _ := by
      rw [← integral_neg]
      exact integral_congr_ae (Eventually.of_forall (fun x => (hright x).symm))

end PoincareConjecture.EuclideanDerivativeNative
