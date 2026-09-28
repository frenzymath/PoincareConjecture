import PoincareConjecture.Proofs.M03.LocalizedDivergenceFlux
import PoincareConjecture.Proofs.M34.Mathlib.QuantitativeEllipticEnergy











set_option autoImplicit false

open scoped ContDiff Topology BigOperators
open MeasureTheory Set PoincareConjecture.Proofs.M03

set_option maxHeartbeats 1800000 in




theorem exists_uniform_coordinate_integral_rate_bound_of_entries
    {n : ℕ} {I : Type*} [Fintype I]
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφV : tsupport φ ⊆ V) {lambda M CU CR : ℝ}
    (hlambda : 0 < lambda) (hM : 0 ≤ M) (hCU : 0 ≤ CU) (hCR : 0 ≤ CR) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ,
      (∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) V) →
      (∀ x ∈ tsupport φ, ∀ z : Fin n → ℝ,
        lambda * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, a x i j * z i * z j) →
      (∀ x ∈ tsupport φ, ∀ i j, |a x i j| ≤ M) →
      ∀ f : I → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ i, ContDiffOn ℝ 2 (f i) V) →
      ∀ U : I → EuclideanSpace ℝ (Fin n) → Fin n → ℝ,
      (∀ i j, ContDiffOn ℝ 1 (fun x => U i x j) V) →
      ∀ (eta : ℝ) (W v : I → EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ i, ContinuousOn (W i) V) →
      ∀ rho : EuclideanSpace ℝ (Fin n) → ℝ, ContinuousOn rho V →
      (∀ x ∈ tsupport φ, 0 ≤ rho x) →
      (∀ x ∈ tsupport φ, (∑ i, f i x ^ 2) ≤ rho x) →
      (∀ x ∈ tsupport φ, (∑ i, ∑ j, (U i x j) ^ 2) ≤ CU * rho x) →
      (∀ x ∈ tsupport φ, (∑ i, 2 * f i x * W i x) ≤
        eta * (∑ i, ∑ j,
          (fderiv ℝ (f i) x (EuclideanSpace.single j 1)) ^ 2) + CR * rho x) →
      (∀ i, ∀ x ∈ V, v i x =
        (∑ j, fderiv ℝ
          (fun y => ∑ k, a y j k * fderiv ℝ (f i) y (EuclideanSpace.single k 1))
          x (EuclideanSpace.single j 1)) +
        (∑ j, fderiv ℝ (fun y => U i y j) x (EuclideanSpace.single j 1)) + W i x) →
      (∑ i, ∫ x, 2 * φ x ^ 2 * f i x * v i x) ≤
        C * (∫ x in tsupport φ, rho x) - (3 * lambda / 4 - eta) *
          (∑ i, ∫ x, φ x ^ 2 * ∑ j,
            (fderiv ℝ (f i) x (EuclideanSpace.single j 1)) ^ 2) := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  classical
  obtain ⟨C0, hC0, hC0bound⟩ := exists_uniform_cutoff_contraction_bound hφ hφc hM
  let CE := (2 / lambda) * C0
  have hCE : 0 ≤ CE := by dsimp [CE]; positivity
  obtain ⟨CD, hCD, hdiv⟩ := exists_localized_divergence_flux_bound hV hφ hφc hφV
  obtain ⟨b, hb⟩ := hφc.exists_bound_of_continuousOn (hφ.continuous.pow 2).continuousOn
  let B := max b 0
  have hB : 0 ≤ B := le_max_right _ _
  have hBbound (x) (hx : x ∈ tsupport φ) : φ x ^ 2 ≤ B :=
    (le_abs_self _).trans ((hb x hx).trans (le_max_left _ _))
  let cU := 1 + 1 / (4 * (lambda / 8))
  have hcU : 0 ≤ cU := by dsimp [cU]; positivity
  let C := 2 * (CE + CD) + (2 * cU * CU + CR) * B
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro a ha haell hab f hf U hU eta W v hW rho hrho hrho0 hfs hUs hWs heq
  let e (j : Fin n) := EuclideanSpace.single j (1 : ℝ)
  let q (i : I) (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :=
    ∑ k, a x j k * fderiv ℝ (f i) x (e k)
  let El (i : I) (x : EuclideanSpace ℝ (Fin n)) :=
    φ x ^ 2 * f i x * ∑ j, fderiv ℝ (fun y => q i y j) x (e j)
  let Di (i : I) (x : EuclideanSpace ℝ (Fin n)) :=
    φ x ^ 2 * f i x * ∑ j, fderiv ℝ (fun y => U i y j) x (e j)
  let Re (i : I) (x : EuclideanSpace ℝ (Fin n)) :=
    φ x ^ 2 * (2 * f i x * W i x)
  let Gr (i : I) (x : EuclideanSpace ℝ (Fin n)) :=
    φ x ^ 2 * ∑ j, (fderiv ℝ (f i) x (e j)) ^ 2
  let Fl (i : I) (x : EuclideanSpace ℝ (Fin n)) := φ x ^ 2 * ∑ j, (U i x j) ^ 2
  let Z (x : EuclideanSpace ℝ (Fin n)) := φ x ^ 2 * rho x
  have hpatch (Q : EuclideanSpace ℝ (Fin n) → ℝ) (hQ : ContinuousOn Q V)
      (hzero : ∀ x ∉ tsupport φ, Q x = 0) : Integrable Q := by
    have hQc : HasCompactSupport Q := by
      apply hφc.mono'
      intro x hx
      by_contra hxφ
      exact hx (hzero x hxφ)
    have hQc' : Continuous Q := by
      apply continuous_iff_continuousAt.mpr
      intro x
      by_cases hx : x ∈ V
      · exact hQ.continuousAt (hV.mem_nhds hx)
      · apply (show ContinuousAt (fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ)) x from
          continuousAt_const).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds
          (show x ∉ tsupport φ from fun h => hx (hφV h))] with y hy
        exact hzero y hy
    exact hQc'.integrable_of_hasCompactSupport hQc
  have hpartial (i : I) (j : Fin n) : ContDiffOn ℝ 1
      (fun x => fderiv ℝ (f i) x (e j)) V :=
    ((hf i).fderiv_of_isOpen hV (by norm_num)).clm_apply contDiffOn_const
  have hq (i : I) (j : Fin n) : ContDiffOn ℝ 1 (fun x => q i x j) V :=
    ContDiffOn.sum (fun k _ => (ha j k).mul (hpartial i k))
  have hEl (i : I) : Integrable (El i) := hpatch _
    (((hφ.continuous.continuousOn.pow 2).mul (hf i).continuousOn).mul
      (continuousOn_finsetSum _ (fun j _ =>
        ((hq i j).continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const)))
    (fun x hx => by simp [El, image_eq_zero_of_notMem_tsupport hx])
  have hDi (i : I) : Integrable (Di i) := hpatch _
    (((hφ.continuous.continuousOn.pow 2).mul (hf i).continuousOn).mul
      (continuousOn_finsetSum _ (fun j _ =>
        ((hU i j).continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const)))
    (fun x hx => by simp [Di, image_eq_zero_of_notMem_tsupport hx])
  have hRe (i : I) : Integrable (Re i) := hpatch _
    ((hφ.continuous.continuousOn.pow 2).mul
      ((continuousOn_const.mul (hf i).continuousOn).mul (hW i)))
    (fun x hx => by simp [Re, image_eq_zero_of_notMem_tsupport hx])
  have hGr (i : I) : Integrable (Gr i) := hpatch _
    ((hφ.continuous.continuousOn.pow 2).mul
      (continuousOn_finsetSum _ (fun j _ => (hpartial i j).continuousOn.pow 2)))
    (fun x hx => by simp [Gr, image_eq_zero_of_notMem_tsupport hx])
  have hFl (i : I) : Integrable (Fl i) := hpatch _
    ((hφ.continuous.continuousOn.pow 2).mul
      (continuousOn_finsetSum _ (fun j _ => (hU i j).continuousOn.pow 2)))
    (fun x hx => by simp [Fl, image_eq_zero_of_notMem_tsupport hx])
  have hZ : Integrable Z := hpatch _
    ((hφ.continuous.continuousOn.pow 2).mul hrho)
    (fun x hx => by simp [Z, image_eq_zero_of_notMem_tsupport hx])
  have hrhoi : IntegrableOn rho (tsupport φ) :=
    ContinuousOn.integrableOn_compact hφc (hrho.mono hφV)
  have hfi (i : I) : IntegrableOn (fun x => f i x ^ 2) (tsupport φ) :=
    ContinuousOn.integrableOn_compact hφc (((hf i).continuousOn.pow 2).mono hφV)
  let G := ∑ i, ∫ x, Gr i x
  let H := ∑ i, ∫ x in tsupport φ, f i x ^ 2
  let Rho := ∫ x in tsupport φ, rho x
  have hH : H ≤ Rho := by
    dsimp only [H, Rho]
    rw [← integral_finsetSum _ (fun i _ => hfi i)]
    exact setIntegral_mono_on (integrable_finsetSum _ (fun i _ => hfi i))
      hrhoi (isClosed_tsupport φ).measurableSet hfs
  have hZbound : (∫ x, Z x) ≤ B * Rho := by
    have hi := hrhoi.integrable_indicator (isClosed_tsupport φ).measurableSet
    have hpoint (x) : Z x ≤ B * (tsupport φ).indicator rho x := by
      by_cases hx : x ∈ tsupport φ
      · rw [indicator_of_mem hx]
        exact mul_le_mul_of_nonneg_right (hBbound x hx) (hrho0 x hx)
      · simp [Z, indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
    have h := integral_mono hZ (hi.const_mul B) hpoint
    simpa only [integral_const_mul, integral_indicator (isClosed_tsupport φ).measurableSet,
      Rho] using h
  have hFlux : (∑ i, ∫ x, Fl i x) ≤ CU * ∫ x, Z x := by
    have hpoint (x) : (∑ i, Fl i x) ≤ CU * Z x := by
      by_cases hx : x ∈ tsupport φ
      · have h := mul_le_mul_of_nonneg_left (hUs x hx) (sq_nonneg (φ x))
        simpa only [Fl, Z, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h
      · simp [Fl, Z, image_eq_zero_of_notMem_tsupport hx]
    have h := integral_mono (integrable_finsetSum _ (fun i _ => hFl i))
      (hZ.const_mul CU) hpoint
    simpa only [integral_finsetSum _ (fun i _ => hFl i), integral_const_mul] using h
  have hReaction : (∑ i, ∫ x, Re i x) ≤ eta * G + CR * ∫ x, Z x := by
    have hpoint (x) : (∑ i, Re i x) ≤ eta * (∑ i, Gr i x) + CR * Z x := by
      by_cases hx : x ∈ tsupport φ
      · have h := mul_le_mul_of_nonneg_left (hWs x hx) (sq_nonneg (φ x))
        simpa only [Re, Gr, Z, e, mul_add, Finset.mul_sum,
          mul_assoc, mul_left_comm, mul_comm] using h
      · simp [Re, Gr, Z, image_eq_zero_of_notMem_tsupport hx]
    have h := integral_mono (integrable_finsetSum _ (fun i _ => hRe i))
      (((integrable_finsetSum _ (fun i _ => hGr i)).const_mul _).add
        (hZ.const_mul CR)) hpoint
    simpa only [Pi.add_apply, integral_finsetSum _ (fun i _ => hRe i), integral_add
      ((integrable_finsetSum _ (fun i _ => hGr i)).const_mul eta)
      (hZ.const_mul CR), integral_const_mul,
      integral_finsetSum _ (fun i _ => hGr i), G] using h
  have hElliptic : (∑ i, ∫ x, El i x) ≤ -(lambda / 2) * G + CE * H := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      localized_elliptic_energy_le_of_cutoff_bound hV ha hφ hφc hφV hlambda haell
        (hC0bound a hab) (hf i))
    simpa only [El, q, Gr, e, G, H, CE, Finset.sum_add_distrib, Finset.mul_sum] using h
  have hDivergence : (∑ i, ∫ x, Di i x) ≤ lambda / 8 * G + CD * H +
      cU * (∑ i, ∫ x, Fl i x) := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      hdiv (lambda / 8) (by positivity) (f i) ((hf i).of_le (by norm_num))
        (U i) (hU i))
    simpa only [Di, Gr, Fl, e, G, H, cU,
      Finset.sum_add_distrib, Finset.mul_sum] using h
  have hRate : (∑ i, ∫ x, 2 * φ x ^ 2 * f i x * v i x) =
      2 * (∑ i, ∫ x, El i x) + 2 * (∑ i, ∫ x, Di i x) +
        (∑ i, ∫ x, Re i x) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hsum : Integrable (fun x => 2 * El i x + 2 * Di i x) :=
      ((hEl i).const_mul 2).add ((hDi i).const_mul 2)
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hEl i).const_mul 2) ((hDi i).const_mul 2),
      ← integral_add hsum (hRe i)]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport φ
    · rw [heq i x (hφV hx)]
      dsimp only [El, Di, Re, q, e]
      ring
    · simp [El, Di, Re, image_eq_zero_of_notMem_tsupport hx]
  rw [hRate]
  change _ ≤ C * Rho - (3 * lambda / 4 - eta) * G
  have hHF := mul_le_mul_of_nonneg_left hH
    (show 0 ≤ 2 * (CE + CD) by positivity)
  have hUF := mul_le_mul_of_nonneg_left hFlux (show 0 ≤ 2 * cU by positivity)
  have hZF := mul_le_mul_of_nonneg_left hZbound
    (show 0 ≤ 2 * cU * CU + CR by positivity)
  dsimp only [C]
  nlinarith only [hElliptic, hDivergence, hReaction, hHF, hUF, hZF]
