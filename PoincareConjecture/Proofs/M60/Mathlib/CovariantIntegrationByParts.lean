import PoincareConjecture.Proofs.M60.Mathlib.CovariantPairing
import PoincareConjecture.Proofs.M60.Mathlib.MapMetricBochner
import PoincareConjecture.Proofs.M60.Mathlib.CoordinateEnergyVariation
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M60

open Poincare.Riemannian.RadialTransport ConnectionVariation ConjugateVariation

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_of_support_subset_closed
    {f : P → E} {K O : Set P} {n : ℕ∞ω}
    (hK : IsClosed K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hf : ContDiffOn ℝ n f O) (hsupp : Function.support f ⊆ K) :
    ContDiff ℝ n f := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ K
  · exact hf.contDiffAt (hO.mem_nhds (hKO hx))
  · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    exact Function.notMem_support.mp (fun hy' => hy (hsupp hy'))

variable [FiniteDimensional ℝ P] [MeasurableSpace P] [BorelSpace P]
  {μ : Measure P} [Measure.IsAddHaarMeasure μ]

theorem integral_fderiv_eq_zero_of_hasCompactSupport
    {q : P → ℝ} (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q) (d : P) :
    ∫ x, fderiv ℝ q x d ∂μ = 0 := by
  have hqi : Integrable q μ := hq.continuous.integrable_of_hasCompactSupport hqc
  have hdi : Integrable (fun x => fderiv ℝ q x d) μ :=
    ((hq.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
      |>.integrable_of_hasCompactSupport (hqc.fderiv_apply ℝ d)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ) (f := fun _ : P => (1 : ℝ)) (g := q) (v := d)
    (by simp) (by simpa using hdi)
    (by simpa using hqi) (fun _ _ => differentiableAt_const (1 : ℝ))
    (fun x _ => hq.differentiable (by simp) x)
  simpa using h

omit [FiniteDimensional ℝ P] [MeasurableSpace P] [BorelSpace P] in

theorem support_covariantDerivative_subset
    (A : P → P →L[ℝ] E →L[ℝ] E) (V : P → E) (d : P) :
    Function.support (fun x => covariantDerivative A V x d) ⊆ tsupport V := by
  intro x hx
  by_contra h
  have hV := image_eq_zero_of_notMem_tsupport h
  have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) h
  exact hx (by simp [covariantDerivative, hV, hd])

omit [FiniteDimensional ℝ P] in

theorem integrable_covariant_pairings
    {A : P → P →L[ℝ] E →L[ℝ] E}
    {G : P → E →L[ℝ] E →L[ℝ] ℝ} {V W : P → E} {O : Set P}
    (hO : IsOpen O) (hA : ContDiffOn ℝ ∞ A O) (hG : ContDiffOn ℝ ∞ G O)
    (hV : ContDiffOn ℝ ∞ V O) (hW : ContDiffOn ℝ ∞ W O)
    (hVc : HasCompactSupport V) (hVO : tsupport V ⊆ O) (d : P) :
    Integrable (fun x => G x (covariantDerivative A V x d) (W x)) μ ∧
      Integrable (fun x => G x (V x) (covariantDerivative A W x d)) μ := by
  have hDV : ContDiffOn ℝ ∞ (fun x => covariantDerivative A V x d) O := by
    intro x hx
    exact (contDiffAt_covariantDerivative
      (hA.contDiffAt (hO.mem_nhds hx)) (hV.contDiffAt (hO.mem_nhds hx)) d).contDiffWithinAt
  have hDW : ContDiffOn ℝ ∞ (fun x => covariantDerivative A W x d) O := by
    intro x hx
    exact (contDiffAt_covariantDerivative
      (hA.contDiffAt (hO.mem_nhds hx)) (hW.contDiffAt (hO.mem_nhds hx)) d).contDiffWithinAt
  have hsL : Function.support (fun x => G x (covariantDerivative A V x d) (W x))
      ⊆ tsupport V := by
    intro x hx
    apply support_covariantDerivative_subset A V d
    intro hz
    exact hx (by simp [hz])
  have hsR : Function.support (fun x => G x (V x) (covariantDerivative A W x d))
      ⊆ tsupport V := by
    intro x hx
    apply subset_tsupport
    intro hz
    exact hx (by simp [hz])
  constructor
  · exact (contDiff_of_support_subset_closed (isClosed_tsupport V) hO hVO
      ((hG.clm_apply hDV).clm_apply hW) hsL).continuous
      |>.integrable_of_hasCompactSupport (hVc.mono' hsL)
  · exact (contDiff_of_support_subset_closed (isClosed_tsupport V) hO hVO
      ((hG.clm_apply hV).clm_apply hDW) hsR).continuous
      |>.integrable_of_hasCompactSupport (hVc.mono' hsR)

theorem integral_covariant_pairing_eq_neg
    {A : P → P →L[ℝ] E →L[ℝ] E}
    {G : P → E →L[ℝ] E →L[ℝ] ℝ} {V W : P → E} {O : Set P}
    (hO : IsOpen O) (hA : ContDiffOn ℝ ∞ A O) (hG : ContDiffOn ℝ ∞ G O)
    (hV : ContDiffOn ℝ ∞ V O) (hW : ContDiffOn ℝ ∞ W O)
    (hVc : HasCompactSupport V) (hVO : tsupport V ⊆ O)
    (hcompat : ∀ x ∈ O, ∀ d : P, ∀ a b : E,
      fderiv ℝ (fun z => G z a b) x d = G x (A x d a) b + G x a (A x d b))
    (d : P) :
    ∫ x, G x (covariantDerivative A V x d) (W x) ∂μ =
      - ∫ x, G x (V x) (covariantDerivative A W x d) ∂μ := by
  let q : P → ℝ := fun x => G x (V x) (W x)
  have hqs : Function.support q ⊆ tsupport V := by
    intro x hx
    apply subset_tsupport
    intro hz
    exact hx (by simp [q, hz])
  have hq : ContDiff ℝ ∞ q := contDiff_of_support_subset_closed
    (isClosed_tsupport V) hO hVO ((hG.clm_apply hV).clm_apply hW) hqs
  have hprod (x : P) : fderiv ℝ q x d =
      G x (covariantDerivative A V x d) (W x) +
        G x (V x) (covariantDerivative A W x d) := by
    by_cases hx : x ∈ tsupport V
    · exact fderiv_metric_pairing
        ((hG.contDiffAt (hO.mem_nhds (hVO hx))).differentiableAt (by simp))
        ((hV.contDiffAt (hO.mem_nhds (hVO hx))).differentiableAt (by simp))
        ((hW.contDiffAt (hO.mem_nhds (hVO hx))).differentiableAt (by simp))
        (hcompat x (hVO hx)) d
    · have hqx : x ∉ tsupport q := fun hxq => hx (closure_minimal hqs (isClosed_tsupport V) hxq)
      have hVx := image_eq_zero_of_notMem_tsupport hx
      simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hqx,
        covariantDerivative, hVx, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]
  have hi := integrable_covariant_pairings (μ := μ) hO hA hG hV hW hVc hVO d
  have hz := integral_fderiv_eq_zero_of_hasCompactSupport (μ := μ) hq (hVc.mono' hqs) d
  simp_rw [hprod] at hz
  rw [integral_add hi.1 hi.2] at hz
  linarith

theorem covDerivAlong_trace_integration_by_parts
    {ι : Type*} [Fintype ι] (e : ι → P)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {u V : P → E} {O : Set P}
    (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O) (hV : ContDiffOn ℝ ∞ V O)
    (hB : ∀ x ∈ O, ContDiffAt ℝ ∞ B (u x))
    (hΓ : ∀ x ∈ O, ContDiffAt ℝ ∞ Γ (u x))
    (hcompat : ∀ x ∈ O, IsMetricCompatibleAt B Γ (u x))
    (hVc : HasCompactSupport V) (hVO : tsupport V ⊆ O) :
    Integrable (fun x => ∑ i, B (u x) (covDerivAlong Γ u V (e i) x)
      (fderiv ℝ u x (e i))) μ ∧
    Integrable (fun x => B (u x) (V x)
      (∑ i, covDerivAlong Γ u (fun y => fderiv ℝ u y (e i)) (e i) x)) μ ∧
    (∫ x, ∑ i, B (u x) (covDerivAlong Γ u V (e i) x) (fderiv ℝ u x (e i)) ∂μ) =
      - ∫ x, B (u x) (V x)
        (∑ i, covDerivAlong Γ u (fun y => fderiv ℝ u y (e i)) (e i) x) ∂μ := by
  let A := mapConnectionCoefficients Γ u
  let G : P → E →L[ℝ] E →L[ℝ] ℝ := fun x => B (u x)
  have hA : ContDiffOn ℝ ∞ A O := by
    intro x hx
    exact (contDiffAt_mapConnectionCoefficients (hΓ x hx)
      (hu.contDiffAt (hO.mem_nhds hx))).contDiffWithinAt
  have hG : ContDiffOn ℝ ∞ G O := by
    intro x hx
    exact ((hB x hx).comp x (hu.contDiffAt (hO.mem_nhds hx))).contDiffWithinAt
  have hW (i : ι) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ u x (e i)) O :=
    (hu.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have hcompat' (x : P) (hx : x ∈ O) (d : P) (a b : E) :
      fderiv ℝ (fun z => G z a b) x d = G x (A x d a) b + G x a (A x d b) := by
    simpa [covDerivAlong_def, G, A, mapConnectionCoefficients] using
      (fderiv_metricAlong (hcompat x hx) ((hB x hx).differentiableAt (by simp))
        ((hu.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
        (differentiableAt_const a) (differentiableAt_const b) d)
  have hi (i : ι) := integrable_covariant_pairings (μ := μ)
    hO hA hG hV (hW i) hVc hVO (e i)
  have heq (i : ι) := integral_covariant_pairing_eq_neg (μ := μ)
    hO hA hG hV (hW i) hVc hVO hcompat' (e i)
  change Integrable (fun x => ∑ i, G x (covariantDerivative A V x (e i))
      (fderiv ℝ u x (e i))) μ ∧
    Integrable (fun x => G x (V x)
      (∑ i, covariantDerivative A (fun y => fderiv ℝ u y (e i)) x (e i))) μ ∧ _
  refine ⟨integrable_finsetSum _ (fun i _ => (hi i).1), ?_, ?_⟩
  · simp_rw [map_sum]
    exact integrable_finsetSum _ (fun i _ => (hi i).2)
  · change (∫ x, ∑ i, G x (covariantDerivative A V x (e i))
        (fderiv ℝ u x (e i)) ∂μ) =
      - ∫ x, G x (V x)
        (∑ i, covariantDerivative A (fun y => fderiv ℝ u y (e i)) x (e i)) ∂μ
    simp_rw [map_sum]
    rw [integral_finsetSum _ (fun i _ => (hi i).1),
      integral_finsetSum _ (fun i _ => (hi i).2)]
    simp_rw [heq]
    simp only [Finset.sum_neg_distrib]

end PoincareConjecture.M60
