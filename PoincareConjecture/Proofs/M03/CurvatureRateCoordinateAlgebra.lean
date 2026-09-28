import PoincareConjecture.Proofs.M03.ScalarEnergyComparison
import PoincareConjecture.Proofs.M03.LocalizedDivergenceFlux
import PoincareConjecture.Proofs.M03.UniformLocalizedEllipticEnergy
import PoincareConjecture.Proofs.M03.CurvatureDifferenceTime
import PoincareConjecture.Proofs.M03.CurvatureFluxVectorDivergence
import PoincareConjecture.Proofs.M03.CurvatureRateAlgebra

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold MeasureTheory Set

universe u

namespace PoincareConjecture.Proofs.M03

theorem curvature_rate_absorb_shared_gradient
    {epsilon lambda A B C KH KU G H U Idiv Iell E : ℝ}
    (_hepsilon : 0 < epsilon)
    (hepsilon_lambda : epsilon ≤ lambda / 4)
    (_hlambda : 0 < lambda)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (_hKH : 0 ≤ KH) (_hKU : 0 ≤ KU) (hG : 0 ≤ G)
    (hH : H ≤ KH * E) (hU : U ≤ KU * E)
    (hdiv : Idiv ≤ epsilon * G + A * H + B * U)
    (hell : Iell ≤ -(lambda / 2) * G + C * H) :
    Idiv + Iell ≤
      -(lambda / 4) * G + ((A + C) * KH + B * KU) * E := by
  have hAC : 0 ≤ A + C := add_nonneg hA hC
  have hgrad_coeff : epsilon - lambda / 2 ≤ -(lambda / 4) := by
    linarith
  have hgrad : (epsilon - lambda / 2) * G ≤ -(lambda / 4) * G :=
    mul_le_mul_of_nonneg_right hgrad_coeff hG
  have hH' : (A + C) * H ≤ (A + C) * (KH * E) :=
    mul_le_mul_of_nonneg_left hH hAC
  have hU' : B * U ≤ B * (KU * E) :=
    mul_le_mul_of_nonneg_left hU hB
  calc
    Idiv + Iell ≤
        (epsilon * G + A * H + B * U) +
          (-(lambda / 2) * G + C * H) := add_le_add hdiv hell
    _ = (epsilon - lambda / 2) * G + (A + C) * H + B * U := by ring
    _ ≤ -(lambda / 4) * G + (A + C) * (KH * E) + B * U := by
      exact add_le_add (add_le_add hgrad hH') (le_refl _)
    _ ≤ -(lambda / 4) * G + (A + C) * (KH * E) + B * (KU * E) := by
      exact add_le_add_right hU' _
    _ = -(lambda / 4) * G + ((A + C) * KH + B * KU) * E := by ring

theorem exists_uniform_curvature_coordinate_integral_rate_bound
    {n : ℕ} {I X : Type*} [Fintype I] [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
    {a : X → EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ}
    (hac : ∀ i j, ContinuousOn
      (fun p : X × EuclideanSpace ℝ (Fin n) => a p.1 p.2 i j) (K ×ˢ V))
    (ha : ∀ t ∈ K, ∀ i j, ContDiffOn ℝ 1 (fun x => a t x i j) V)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφV : tsupport φ ⊆ V) {lambda CU CR : ℝ}
    (hlambda : 0 < lambda) (hCU : 0 ≤ CU) (hCR : 0 ≤ CR)
    (haell : ∀ t ∈ K, ∀ x ∈ tsupport φ, ∀ z : Fin n → ℝ,
      lambda * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, a t x i j * z i * z j) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ K,
      ∀ f : I → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ i, ContDiffOn ℝ 2 (f i) V) →
      ∀ U : I → EuclideanSpace ℝ (Fin n) → Fin n → ℝ,
      (∀ i j, ContDiffOn ℝ 1 (fun x => U i x j) V) →
      ∀ W v : I → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ i, ContinuousOn (W i) V) → (∀ i, ContinuousOn (v i) V) →
      ∀ rho : EuclideanSpace ℝ (Fin n) → ℝ, ContinuousOn rho V →
      (∀ x ∈ tsupport φ, 0 ≤ rho x) →
      (∀ x ∈ tsupport φ, (∑ i, f i x ^ 2) ≤ rho x) →
      (∀ x ∈ tsupport φ, (∑ i, ∑ j, (U i x j) ^ 2) ≤ CU * rho x) →
      (∀ x ∈ tsupport φ, (∑ i, 2 * f i x * W i x) ≤
        lambda / 4 * (∑ i, ∑ j,
          (fderiv ℝ (f i) x (EuclideanSpace.single j 1)) ^ 2) + CR * rho x) →
      (∀ i, ∀ x ∈ V, v i x =
        (∑ j, fderiv ℝ
          (fun y => ∑ k, a t y j k * fderiv ℝ (f i) y (EuclideanSpace.single k 1))
          x (EuclideanSpace.single j 1)) +
        (∑ j, fderiv ℝ (fun y => U i y j) x (EuclideanSpace.single j 1)) + W i x) →
      (∑ i, ∫ x, 2 * φ x ^ 2 * f i x * v i x) ≤
        C * (∫ x in tsupport φ, rho x) - lambda / 4 *
          (∑ i, ∫ x, φ x ^ 2 * ∑ j,
            (fderiv ℝ (f i) x (EuclideanSpace.single j 1)) ^ 2) := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  classical
  obtain ⟨CE, hCE, hell⟩ := exists_uniform_localized_elliptic_energy_bound
    hK hV hac ha hφ hφc hφV hlambda haell
  obtain ⟨CD, hCD, hdiv⟩ := exists_localized_divergence_flux_bound hV hφ hφc hφV
  obtain ⟨b, hb⟩ := hφc.exists_bound_of_continuousOn (hφ.continuous.pow 2).continuousOn
  let B := max b 0
  have hB : 0 ≤ B := le_max_right _ _
  have hBbound (x) (hx : x ∈ tsupport φ) : φ x ^ 2 ≤ B :=
    (le_abs_self _).trans ((hb x hx).trans (le_max_left _ _))
  let cU := 1 + 1 / lambda
  have hcU : 0 ≤ cU := by dsimp [cU]; positivity
  let C := 2 * (CE + CD) + (2 * cU * CU + CR) * B
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro t ht f hf U hU W v hW hv rho hrho hrho0 hfs hUs hWs heq
  let e (j : Fin n) := EuclideanSpace.single j (1 : ℝ)
  let q (i : I) (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :=
    ∑ k, a t x j k * fderiv ℝ (f i) x (e k)
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
      · apply continuousAt_const.congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds
          (show x ∉ tsupport φ from fun h => hx (hφV h))] with y hy
        exact hzero y hy
    exact hQc'.integrable_of_hasCompactSupport hQc
  have hpartial (i : I) (j : Fin n) : ContDiffOn ℝ 1
      (fun x => fderiv ℝ (f i) x (e j)) V :=
    ((hf i).fderiv_of_isOpen hV (by norm_num)).clm_apply contDiffOn_const
  have hq (i : I) (j : Fin n) : ContDiffOn ℝ 1 (fun x => q i x j) V :=
    ContDiffOn.sum (fun k _ => (ha t ht j k).mul (hpartial i k))
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
  have hReaction : (∑ i, ∫ x, Re i x) ≤ lambda / 4 * G + CR * ∫ x, Z x := by
    have hpoint (x) : (∑ i, Re i x) ≤ lambda / 4 * (∑ i, Gr i x) + CR * Z x := by
      by_cases hx : x ∈ tsupport φ
      · have h := mul_le_mul_of_nonneg_left (hWs x hx) (sq_nonneg (φ x))
        simpa only [Re, Gr, Z, e, mul_add, Finset.mul_sum,
          mul_assoc, mul_left_comm, mul_comm] using h
      · simp [Re, Gr, Z, image_eq_zero_of_notMem_tsupport hx]
    have h := integral_mono (integrable_finsetSum _ (fun i _ => hRe i))
      (((integrable_finsetSum _ (fun i _ => hGr i)).const_mul _).add
        (hZ.const_mul CR)) hpoint
    simpa only [Pi.add_apply, integral_finsetSum _ (fun i _ => hRe i), integral_add
      ((integrable_finsetSum _ (fun i _ => hGr i)).const_mul (lambda / 4))
      (hZ.const_mul CR), integral_const_mul,
      integral_finsetSum _ (fun i _ => hGr i), G] using h
  have hElliptic : (∑ i, ∫ x, El i x) ≤ -(lambda / 2) * G + CE * H := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hell t ht (f i) (hf i))
    simpa only [El, q, Gr, e, G, H, Finset.sum_add_distrib, Finset.mul_sum] using h
  have hDivergence : (∑ i, ∫ x, Di i x) ≤ lambda / 4 * G + CD * H +
      cU * (∑ i, ∫ x, Fl i x) := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      hdiv (lambda / 4) (by positivity) (f i) ((hf i).of_le (by norm_num))
        (U i) (hU i))
    have hfour : 4 * (lambda / 4) = lambda := by ring
    simpa only [hfour, Di, Gr, Fl, e, G, H, cU,
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
  change _ ≤ C * Rho - lambda / 4 * G
  have hHF := mul_le_mul_of_nonneg_left hH
    (show 0 ≤ 2 * (CE + CD) by positivity)
  have hUF := mul_le_mul_of_nonneg_left hFlux (show 0 ≤ 2 * cU by positivity)
  have hZF := mul_le_mul_of_nonneg_left hZbound
    (show 0 ≤ 2 * cU * CU + CR by positivity)
  dsimp only [C]
  nlinarith only [hElliptic, hDivergence, hReaction, hHF, hUF, hZF]

theorem hasDerivAt_ricciFlow_curvature_coordinates
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame b
    let theta := e.localFrameCoeff (𝓡 n) b
    let D := F.connection t
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.connection Q y (P y)
    let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.curvatureOnFields A B C y
    let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      N P (R A B C) y - R (N P A) B C y -
        R A (N P B) C y - R A B (N P C) y
    let G := fun y : M =>
      ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
        (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
        x0 y x0 y ((F.metric t).inner y)
    let a := fun (y : M) (i d : Fin n) =>
      (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj d)) i
    let W := fun (i : Fin n) (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      ∑ d, a y i d • K (E d) A B C y
    let Gamma := fun (y : M) (i j l : Fin n) => theta l y (N (E i) (E j) y)
    let v := fun (z : V) (i l j k m : Fin n) =>
      theta l (c.symm z) (W i (E j) (E k) (E m) (c.symm z))
    ∀ z ∈ c.target, ∀ l j k m : Fin n,
      let x := c.symm z
      let u := E j x
      let v0 := E k x
      let w := E m x
      let Rp := D.curvature x
      let L := fun r s : TangentSpace (𝓡 n) x =>
        Rp (Rp u v0 r) s w - (2 : ℝ) • Rp v0 r (Rp s u w) +
          (2 : ℝ) • Rp r u (Rp v0 s w) + D.ricci x (Rp u v0 w) r • s -
          D.ricci x u r • Rp s v0 w - D.ricci x v0 r • Rp u s w -
          D.ricci x w r • Rp u v0 s
      HasDerivAt (fun s => theta l x ((F.connection s).curvature x u v0 w))
        ((∑ i, (fderiv ℝ (fun y => v y i l j k m) z (EuclideanSpace.single i 1) +
          ∑ p, (Gamma x i p i * v z p l j k m +
            Gamma x i p l * v z i p j k m - Gamma x i j p * v z i l p k m -
            Gamma x i k p * v z i l j p m - Gamma x i m p * v z i l j k p))) +
          theta l x (∑ i : Fin n, ∑ d : Fin n, a x i d • L (E i x) (E d x))) t := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame b
  let theta := e.localFrameCoeff (𝓡 n) b
  let D := F.connection t
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.connection Q y (P y)
  let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.curvatureOnFields A B C y
  let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    N P (R A B C) y - R (N P A) B C y -
      R A (N P B) C y - R A B (N P C) y
  let H := fun (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    N P (K Q A B C) y - K (N P Q) A B C y -
      K Q (N P A) B C y - K Q A (N P B) C y - K Q A B (N P C) y
  let G := fun y : M =>
    ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
      x0 y x0 y ((F.metric t).inner y)
  let a := fun (y : M) (i d : Fin n) =>
    (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj d)) i
  let W := fun (i : Fin n) (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    ∑ d, a y i d • K (E d) A B C y
  let Gamma := fun (y : M) (i j l : Fin n) => theta l y (N (E i) (E j) y)
  let Div := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    ∑ i, (N (E i) (W i A B C) y - W i (N (E i) A) B C y -
      W i A (N (E i) B) C y - W i A B (N (E i) C) y +
      ∑ p, Gamma y i p i • W p A B C y)
  let v := fun (z : V) (i l j k m : Fin n) =>
    theta l (c.symm z) (W i (E j) (E k) (E m) (c.symm z))
  intro z hz l j k m
  let x := c.symm z
  have hx : x ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  have hE (i : Fin n) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
      (T% (E i)) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b i
  let bn := (F.metric t).orthonormalBasis x
  let ext := fun u : TangentSpace (𝓡 n) x => FiberBundle.extend V u
  let u := E j x
  let v0 := E k x
  let w := E m x
  let Rp := D.curvature x
  let P := fun u : TangentSpace (𝓡 n) x => ∑ r, D.ricci x u (bn r) • bn r
  let Q := (∑ r, (Rp (Rp u v0 (bn r)) (bn r) w -
      (2 : ℝ) • Rp v0 (bn r) (Rp (bn r) u w) +
      (2 : ℝ) • Rp (bn r) u (Rp v0 (bn r) w))) +
    P (Rp u v0 w) - Rp (P u) v0 w - Rp u (P v0) w - Rp u v0 (P w)
  let L := fun r s : TangentSpace (𝓡 n) x =>
    Rp (Rp u v0 r) s w - (2 : ℝ) • Rp v0 r (Rp s u w) +
      (2 : ℝ) • Rp r u (Rp v0 s w) + D.ricci x (Rp u v0 w) r • s -
      D.ricci x u r • Rp s v0 w - D.ricci x v0 r • Rp u s w -
      D.ricci x w r • Rp u v0 s
  have htrace : (∑ r, H (ext (bn r)) (ext (bn r)) (ext u) (ext v0) (ext w) x) =
      ∑ i, ∑ d, a x i d • H (E i) (E d) (E j) (E k) (E m) x :=
    curvature_hessian_trace_localFrame D x0 hx (E j) (E k) (E m) (hE j) (hE k) (hE m)
  have hdiv : (∑ i, ∑ d, a x i d • H (E i) (E d) (E j) (E k) (E m) x) =
      Div (E j) (E k) (E m) x :=
    curvature_hessian_contraction_eq_covariant_divergence D x0 z hz
      (E j) (E k) (E m) (hE j) (hE k) (hE m)
  have hcoord : theta l x (Div (E j) (E k) (E m) x) =
      ∑ i, (fderiv ℝ (fun y => v y i l j k m) z (EuclideanSpace.single i 1) +
        ∑ p, (Gamma x i p i * v z p l j k m +
          Gamma x i p l * v z i p j k m - Gamma x i j p * v z i l p k m -
          Gamma x i k p * v z i l j p m - Gamma x i m p * v z i l j k p)) :=
    curvature_raised_divergence_coordinates D x0 z hz l j k m
  have hQ : Q = ∑ i : Fin n, ∑ d : Fin n, a x i d • L (E i x) (E d x) :=
    curvature_reaction_eq_inverse_frame_sum D x0 x hx u v0 w
  have htime := hasDerivAt_ricciFlow_curvature_diffusion_reaction F ht x u v0 w
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ V (TangentSpace (𝓡 n)) x
  have hs := (theta l x).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t htime
  change HasDerivAt (fun s => theta l x ((F.connection s).curvature x u v0 w))
    (theta l x ((∑ r, H (ext (bn r)) (ext (bn r)) (ext u) (ext v0) (ext w) x) + Q)) t at hs
  rw [htrace, hdiv, map_add, hcoord, hQ] at hs
  exact hs

theorem exists_ricciFlow_coordinate_ellipticity
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) {K : Set ℝ}
    (hK : IsCompact K) (hKJ : K ⊆ J) (x0 : M)
    {Q : Set (EuclideanSpace ℝ (Fin n))} (hQ : IsCompact Q)
    (hQchart : Q ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x0).target) :
    let V := EuclideanSpace ℝ (Fin n)
    let c := chartAt V x0
    let G := fun (t : ℝ) (z : V) =>
      ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
        (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
        x0 (c.symm z) x0 (c.symm z) ((F.metric t).inner (c.symm z))
    let a := fun (t : ℝ) (z : V) (i j : Fin n) =>
      ((G t z).inverse (EuclideanSpace.proj j)) i
    ∃ lambda : ℝ, 0 < lambda ∧ ∀ t ∈ K, ∀ z ∈ Q, ∀ v : Fin n → ℝ,
      lambda * (∑ i, v i ^ 2) ≤ ∑ i, ∑ j, a t z i j * v i * v j := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let G := fun (p : ℝ × V) =>
    ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      x0 (c.symm p.2) x0 (c.symm p.2) ((F.metric p.1).inner (c.symm p.2))
  have hbase (z : V) (hz : z ∈ Q) : c.symm z ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target (hQchart hz)
  have hGc : ContinuousOn G (K ×ˢ Q) :=
    (contMDiffOn_family_metric_frame_inverse F.smooth x0).2.1.continuousOn.comp
      (continuousOn_fst.prodMk ((c.continuousOn_symm.mono hQchart).comp
        continuousOn_snd (fun p hp => hp.2)))
      (fun p hp => ⟨hKJ hp.1, hbase p.2 hp.2⟩)
  have hmetric (p : ℝ × V) (hp : p ∈ K ×ˢ Q) (v w : V) :
      G p v w = (F.metric p.1).inner (c.symm p.2)
        (e.symmL ℝ (c.symm p.2) v) (e.symmL ℝ (c.symm p.2) w) := by
    dsimp only [G]
    rw [inCoordinates_apply_eq₂
      (F₁ := V) (F₂ := V) (F₃ := ℝ)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun _ : M => ℝ) (hbase p.2 hp.2) (hbase p.2 hp.2) (by simp)]
    rw [← Trivialization.symmL_apply (R := ℝ) e (hbase p.2 hp.2) v,
      ← Trivialization.symmL_apply (R := ℝ) e (hbase p.2 hp.2) w]
    simp only [Trivial.fiberBundle_trivializationAt',
      Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq]
  have hpos (p : ℝ × V) (hp : p ∈ K ×ˢ Q) (v : V) (hv : v ≠ 0) :
      0 < G p v v := by
    rw [hmetric p hp]
    apply (F.metric p.1).pos
    intro hzero
    have h := congrArg (e.continuousLinearMapAt ℝ (c.symm p.2)) hzero
    rw [Trivialization.continuousLinearMapAt_symmL e (hbase p.2 hp.2), map_zero] at h
    exact hv h
  obtain ⟨lambda, C, hlambda, hC, hbound⟩ :=
    exists_pos_uniform_bilinear_inverse_bounds (hK.prod hQ) hGc hpos
  refine ⟨lambda, hlambda, ?_⟩
  intro t ht z hz v
  let l : V →L[ℝ] ℝ := ∑ i : Fin n, v i • EuclideanSpace.proj i
  have hl : l = innerSL ℝ (WithLp.toLp 2 v) := by
    ext w
    simp only [l, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, EuclideanSpace.coe_proj, innerSL_apply_apply]
    change (∑ i, v i * w i) = inner ℝ (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) w
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply, WithLp.ofLp_toLp]
  have hnorm : ‖l‖ ^ 2 = ∑ i, v i ^ 2 := by
    rw [hl, innerSL_apply_norm, EuclideanSpace.real_norm_sq_eq]
  have heval : l ((G (t, z)).inverse l) =
      ∑ i : Fin n, ∑ j : Fin n,
        ((G (t, z)).inverse (EuclideanSpace.proj j)) i * v i * v j := by
    have hlapply (w : V) : l w = ∑ i, v i * (EuclideanSpace.proj i) w := by
      simp only [l, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
    rw [hlapply]
    simp only [l, map_sum, map_smul, smul_eq_mul, Finset.mul_sum,
      EuclideanSpace.coe_proj]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h := ((hbound (t, z) ⟨ht, hz⟩).2.2 l).1
  rw [hnorm, heval] at h
  exact h

theorem hasDerivAt_ricciFlow_curvature_difference_divergence
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J J' : Set ℝ} (F : RicciFlow n M J) (F' : RicciFlow n M J')
    {t : ℝ} (ht : t ∈ interior J) (ht' : t ∈ interior J') (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame b
    let theta := e.localFrameCoeff (𝓡 n) b
    let N := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
        (P Q : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.connection Q y (P y)
    let R := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
        (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.curvatureOnFields A B C y
    let K := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
        (P A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      N D P (R D A B C) y - R D (N D P A) B C y -
        R D A (N D P B) C y - R D A B (N D P C) y
    let G := fun (g : RiemannianMetric n M) (z : V) =>
      ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
        (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
        x0 (c.symm z) x0 (c.symm z) (g.inner (c.symm z))
    let a := fun (g : RiemannianMetric n M) (z : V) (i d : Fin n) =>
      ((G g z).inverse (EuclideanSpace.proj d)) i
    let Gamma := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
        (z : V) (i j l : Fin n) =>
      theta l (c.symm z) (N D (E i) (E j) (c.symm z))
    let rho := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
        (z : V) (l j k m : Fin n) =>
      theta l (c.symm z) (R D (E j) (E k) (E m) (c.symm z))
    let v := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
        (z : V) (i l j k m : Fin n) =>
      theta l (c.symm z) (∑ d, a g z i d •
        K D (E d) (E j) (E k) (E m) (c.symm z))
    let sigma := fun (s : ℝ) (z : V) (l j k m : Fin n) =>
      rho (F.connection s) z l j k m - rho (F'.connection s) z l j k m
    let P := fun (z : V) (i l j k m : Fin n) =>
      ∑ d, a (F.metric t) z i d * fderiv ℝ
        (fun y => sigma t y l j k m) z (EuclideanSpace.single d 1)
    let U := fun (z : V) (i l j k m : Fin n) =>
      v (F.connection t) z i l j k m - v (F'.connection t) z i l j k m - P z i l j k m
    let action := fun (B : Fin n → Fin n → Fin n → ℝ)
        (w : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) (l j k m : Fin n) =>
      ∑ i, ∑ p, (B i p i * w p l j k m + B i p l * w i p j k m -
        B i j p * w i l p k m - B i k p * w i l j p m - B i m p * w i l j k p)
    let Q := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
        (z : V) (l j k m : Fin n) =>
      let x := c.symm z
      let T := D.curvature x
      let u := E j x
      let v0 := E k x
      let w := E m x
      theta l x (∑ i : Fin n, ∑ d : Fin n, a g z i d •
        (T (T u v0 (E i x)) (E d x) w - (2 : ℝ) • T v0 (E i x) (T (E d x) u w) +
          (2 : ℝ) • T (E i x) u (T v0 (E d x) w) +
          D.ricci x (T u v0 w) (E i x) • E d x -
          D.ricci x u (E i x) • T (E d x) v0 w -
          D.ricci x v0 (E i x) • T u (E d x) w -
          D.ricci x w (E i x) • T u v0 (E d x)))
    let W := fun (z : V) (l j k m : Fin n) =>
      action (Gamma (F.connection t) z)
        (fun i l j k m => P z i l j k m + U z i l j k m) l j k m +
      action (fun i j l => Gamma (F.connection t) z i j l -
        Gamma (F'.connection t) z i j l) (v (F'.connection t) z) l j k m +
      Q (F.connection t) z l j k m - Q (F'.connection t) z l j k m
    ∀ z ∈ c.target, ∀ l j k m : Fin n,
      HasDerivAt (fun s => sigma s z l j k m)
        ((∑ i, fderiv ℝ (fun y => P y i l j k m) z (EuclideanSpace.single i 1)) +
          (∑ i, fderiv ℝ (fun y => U y i l j k m) z (EuclideanSpace.single i 1)) +
          W z l j k m) t := by
  classical
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame b
  let theta := e.localFrameCoeff (𝓡 n) b
  let N := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
      (P Q : (y : M) → TangentSpace (𝓡 n) y) (y : M) => D.connection Q y (P y)
  let R := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
      (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) => D.curvatureOnFields A B C y
  let K := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
      (P A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    N D P (R D A B C) y - R D (N D P A) B C y -
      R D A (N D P B) C y - R D A B (N D P C) y
  let G := fun (g : RiemannianMetric n M) (z : V) =>
    ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      x0 (c.symm z) x0 (c.symm z) (g.inner (c.symm z))
  let a := fun (g : RiemannianMetric n M) (z : V) (i d : Fin n) =>
    ((G g z).inverse (EuclideanSpace.proj d)) i
  let Gamma := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
      (z : V) (i j l : Fin n) => theta l (c.symm z) (N D (E i) (E j) (c.symm z))
  let rho := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
      (z : V) (l j k m : Fin n) => theta l (c.symm z) (R D (E j) (E k) (E m) (c.symm z))
  let v := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
      (z : V) (i l j k m : Fin n) => theta l (c.symm z)
        (∑ d, a g z i d • K D (E d) (E j) (E k) (E m) (c.symm z))
  let sigma := fun (s : ℝ) (z : V) (l j k m : Fin n) =>
    rho (F.connection s) z l j k m - rho (F'.connection s) z l j k m
  let P := fun (z : V) (i l j k m : Fin n) =>
    ∑ d, a (F.metric t) z i d * fderiv ℝ
      (fun y => sigma t y l j k m) z (EuclideanSpace.single d 1)
  let U := fun (z : V) (i l j k m : Fin n) =>
    v (F.connection t) z i l j k m - v (F'.connection t) z i l j k m - P z i l j k m
  let action := fun (B : Fin n → Fin n → Fin n → ℝ)
      (w : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) (l j k m : Fin n) =>
    ∑ i, ∑ p, (B i p i * w p l j k m + B i p l * w i p j k m -
      B i j p * w i l p k m - B i k p * w i l j p m - B i m p * w i l j k p)
  let Q := fun {g : RiemannianMetric n M} (D : LeviCivitaData g)
      (z : V) (l j k m : Fin n) =>
    let x := c.symm z
    let T := D.curvature x
    let u := E j x
    let v0 := E k x
    let w := E m x
    theta l x (∑ i : Fin n, ∑ d : Fin n, a g z i d •
      (T (T u v0 (E i x)) (E d x) w - (2 : ℝ) • T v0 (E i x) (T (E d x) u w) +
        (2 : ℝ) • T (E i x) u (T v0 (E d x) w) +
        D.ricci x (T u v0 w) (E i x) • E d x - D.ricci x u (E i x) • T (E d x) v0 w -
        D.ricci x v0 (E i x) • T u (E d x) w - D.ricci x w (E i x) • T u v0 (E d x)))
  have hbase (z : V) (hz : z ∈ c.target) : c.symm z ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  let Smooth := fun Y : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% Y) e.baseSet
  have hE (i : Fin n) : Smooth (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b i
  have hN {g : RiemannianMetric n M} (D : LeviCivitaData g)
      (A B : (y : M) → TangentSpace (𝓡 n) y) (hA : Smooth A) (hB : Smooth B) :
      Smooth (N D A B) := D.contMDiffOn_connection_apply e.open_baseSet A B hA hB
  letI : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  letI : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  have hR {g : RiemannianMetric n M} (D : LeviCivitaData g)
      (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : Smooth A) (hB : Smooth B) (hC : Smooth C) : Smooth (R D A B C) := by
    have hbr : Smooth (VectorField.mlieBracket (𝓡 n) A B) := by
      intro y hy
      exact ((hA.contMDiffAt (e.open_baseSet.mem_nhds hy)).mlieBracket_vectorField
        (hB.contMDiffAt (e.open_baseSet.mem_nhds hy)) (m := ⊤) (n := ⊤)
        (by simp)).contMDiffWithinAt
    exact ((hN D A _ hA (hN D B C hB hC)).sub_section
      (hN D B _ hB (hN D A C hA hC))).sub_section (hN D _ C hbr hC)
  have hK {g : RiemannianMetric n M} (D : LeviCivitaData g)
      (d j k m : Fin n) : Smooth (K D (E d) (E j) (E k) (E m)) :=
    (((hN D _ _ (hE d) (hR D _ _ _ (hE j) (hE k) (hE m))).sub_section
      (hR D _ _ _ (hN D _ _ (hE d) (hE j)) (hE k) (hE m))).sub_section
      (hR D _ _ _ (hE j) (hN D _ _ (hE d) (hE k)) (hE m))).sub_section
      (hR D _ _ _ (hE j) (hE k) (hN D _ _ (hE d) (hE m)))
  have hscalar (f : M → ℝ) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.baseSet) :
      ContDiffOn ℝ ∞ (fun z => f (c.symm z)) c.target :=
    (hf.comp (contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0)) hbase).contDiffOn
  have hcoef (Y : (y : M) → TangentSpace (𝓡 n) y) (hY : Smooth Y) (l : Fin n) :
      ContDiffOn ℝ ∞ (fun z => theta l (c.symm z) (Y (c.symm z))) c.target :=
    hscalar _ (contMDiffOn_localFrameCoeff b e.open_baseSet subset_rfl hY l)
  have ha (g : RiemannianMetric n M) (i d : Fin n) :
      ContDiffOn ℝ ∞ (fun z => a g z i d) c.target := by
    have hf : RiemannianMetric.IsSmoothFamilyOn (fun _ : ℝ => g) univ :=
      (g.contMDiff.comp contMDiff_snd).contMDiffOn
    have hi := (contMDiffOn_family_metric_frame_inverse hf x0).2.2
    have hs := hi.comp
      (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M => ((0 : ℝ), y)) e.baseSet from
        contMDiffOn_const.prodMk contMDiffOn_id) (fun y hy => ⟨mem_univ (0 : ℝ), hy⟩)
    exact hscalar _ ((contMDiffOn_const (c := EuclideanSpace.proj i)).clm_apply
      (hs.clm_apply (contMDiffOn_const (c := EuclideanSpace.proj d))))
  have hv {g : RiemannianMetric n M} (D : LeviCivitaData g) (i l j k m : Fin n) :
      ContDiffOn ℝ ∞ (fun z => v D z i l j k m) c.target := by
    have hs := ContDiffOn.sum (s := Finset.univ) (fun d _ =>
      (ha g i d).mul (hcoef _ (hK D d j k m) l))
    simpa only [v, map_sum, map_smul, smul_eq_mul] using hs
  have hr {g : RiemannianMetric n M} (D : LeviCivitaData g) (l j k m : Fin n) :
      ContDiffOn ℝ ∞ (fun z => rho D z l j k m) c.target :=
    hcoef _ (hR D _ _ _ (hE j) (hE k) (hE m)) l
  have hP (i l j k m : Fin n) : ContDiffOn ℝ ∞ (fun z => P z i l j k m) c.target := by
    apply ContDiffOn.sum
    intro d _
    exact (ha _ i d).mul
      ((((hr (F.connection t) l j k m).sub (hr (F'.connection t) l j k m)).fderiv_of_isOpen
        c.open_target (by simp)).clm_apply contDiffOn_const)
  intro z hz l j k m
  have htime {I : Set ℝ} (FF : RicciFlow n M I) (htF : t ∈ interior I) :
      HasDerivAt (fun s => rho (FF.connection s) z l j k m)
        ((∑ i, fderiv ℝ (fun y => v (FF.connection t) y i l j k m) z
          (EuclideanSpace.single i 1)) +
          action (Gamma (FF.connection t) z) (v (FF.connection t) z) l j k m +
          Q (FF.connection t) z l j k m) t := by
    have hs := hasDerivAt_ricciFlow_curvature_coordinates FF htF x0 z hz l j k m
    have hf (s : ℝ) : rho (FF.connection s) z l j k m =
        theta l (c.symm z) ((FF.connection s).curvature (c.symm z)
          (E j (c.symm z)) (E k (c.symm z)) (E m (c.symm z))) := by
      exact congrArg (theta l (c.symm z))
        (curvature_eq_curvatureOnFields (FF.connection s) e.open_baseSet
          (E j) (E k) (E m) (hE j) (hE k) (hE m) (hbase z hz)).symm
    have hs' := hs.congr_of_eventuallyEq (Filter.Eventually.of_forall hf)
    simpa only [action, Finset.sum_add_distrib, Q, v, Gamma, a, G, K, N, R,
      theta, E, b, e, c, V] using hs'
  have hdiv (i : Fin n) :
      fderiv ℝ (fun y => v (F.connection t) y i l j k m) z (EuclideanSpace.single i 1) -
        fderiv ℝ (fun y => v (F'.connection t) y i l j k m) z (EuclideanSpace.single i 1) =
      fderiv ℝ (fun y => P y i l j k m) z (EuclideanSpace.single i 1) +
        fderiv ℝ (fun y => U y i l j k m) z (EuclideanSpace.single i 1) := by
    have hv0 := ((hv (F.connection t) i l j k m).contDiffAt
      (c.open_target.mem_nhds hz)).differentiableAt (by simp)
    have hv1 := ((hv (F'.connection t) i l j k m).contDiffAt
      (c.open_target.mem_nhds hz)).differentiableAt (by simp)
    have hp := ((hP i l j k m).contDiffAt
      (c.open_target.mem_nhds hz)).differentiableAt (by simp)
    dsimp only [U]
    have huv : fderiv ℝ
        (fun y => v (F.connection t) y i l j k m -
          v (F'.connection t) y i l j k m) z =
        fderiv ℝ (fun y => v (F.connection t) y i l j k m) z -
          fderiv ℝ (fun y => v (F'.connection t) y i l j k m) z :=
      fderiv_fun_sub hv0 hv1
    have hup : fderiv ℝ
        (fun y => (v (F.connection t) y i l j k m -
          v (F'.connection t) y i l j k m) - P y i l j k m) z =
        fderiv ℝ (fun y => v (F.connection t) y i l j k m -
          v (F'.connection t) y i l j k m) z -
          fderiv ℝ (fun y => P y i l j k m) z :=
      fderiv_fun_sub (hv0.sub hv1) hp
    rw [hup, huv]
    simp only [sub_apply]
    ring
  have haction :
      action (Gamma (F.connection t) z) (v (F.connection t) z) l j k m -
        action (Gamma (F'.connection t) z) (v (F'.connection t) z) l j k m =
      action (Gamma (F.connection t) z)
        (fun i l j k m => P z i l j k m + U z i l j k m) l j k m +
      action (fun i j l => Gamma (F.connection t) z i j l -
        Gamma (F'.connection t) z i j l) (v (F'.connection t) z) l j k m := by
    dsimp only [action]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    dsimp only [U]
    ring
  have hs := (htime F ht).sub (htime F' ht')
  have hds : (∑ i, fderiv ℝ (fun y => v (F.connection t) y i l j k m) z
          (EuclideanSpace.single i 1)) -
        (∑ i, fderiv ℝ (fun y => v (F'.connection t) y i l j k m) z
          (EuclideanSpace.single i 1)) =
        (∑ i, fderiv ℝ (fun y => P y i l j k m) z (EuclideanSpace.single i 1)) +
          (∑ i, fderiv ℝ (fun y => U y i l j k m) z (EuclideanSpace.single i 1)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hdiv i)
  change HasDerivAt (fun s => sigma s z l j k m)
    ((∑ i, fderiv ℝ (fun y => P y i l j k m) z (EuclideanSpace.single i 1)) +
      (∑ i, fderiv ℝ (fun y => U y i l j k m) z (EuclideanSpace.single i 1)) +
      (action (Gamma (F.connection t) z)
        (fun i l j k m => P z i l j k m + U z i l j k m) l j k m +
       action (fun i j l => Gamma (F.connection t) z i j l -
         Gamma (F'.connection t) z i j l) (v (F'.connection t) z) l j k m +
       Q (F.connection t) z l j k m - Q (F'.connection t) z l j k m)) t
  have heq :
      (∑ i, fderiv ℝ (fun y => P y i l j k m) z (EuclideanSpace.single i 1)) +
        (∑ i, fderiv ℝ (fun y => U y i l j k m) z (EuclideanSpace.single i 1)) +
        (action (Gamma (F.connection t) z)
          (fun i l j k m => P z i l j k m + U z i l j k m) l j k m +
         action (fun i j l => Gamma (F.connection t) z i j l -
           Gamma (F'.connection t) z i j l) (v (F'.connection t) z) l j k m +
         Q (F.connection t) z l j k m - Q (F'.connection t) z l j k m) =
      ((∑ i, fderiv ℝ (fun y => v (F.connection t) y i l j k m) z
          (EuclideanSpace.single i 1)) +
        action (Gamma (F.connection t) z) (v (F.connection t) z) l j k m +
        Q (F.connection t) z l j k m) -
      ((∑ i, fderiv ℝ (fun y => v (F'.connection t) y i l j k m) z
          (EuclideanSpace.single i 1)) +
        action (Gamma (F'.connection t) z) (v (F'.connection t) z) l j k m +
        Q (F'.connection t) z l j k m) := by linarith only [haction, hds]
  rw [heq]
  exact hs

section CurvatureBundleCoordinates

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000

private def curvatureRawContraction {n : ℕ}
    (theta : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (Fin n → Fin n → Fin n → Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun T := ∑ l, ∑ j, ∑ k, ∑ m, theta l j k m * T l j k m
  map_add' T U := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c T := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro m _
    ring

theorem curvature_contract_model_coordinate_expand {n d : ℕ} :
    let V := EuclideanSpace ℝ (Fin n)
    letI : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
    letI : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
    let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
    ∀ (qS : FS ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (T : FS) (alpha : Fin d),
      let e := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
      let B := fun l j k m : Fin n => (EuclideanSpace.proj j).smulRight
        ((EuclideanSpace.proj k).smulRight ((EuclideanSpace.proj m).smulRight (e l)))
      (∑ l, ∑ j, ∑ k, ∑ m, qS (B l j k m) alpha * (T (e j) (e k) (e m)) l) = qS T alpha := by
  let V := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
  classical
  dsimp only
  intro qS T alpha
  let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
  let e := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
  let B : Fin n → Fin n → Fin n → Fin n → FS := fun l j k m =>
    (EuclideanSpace.proj j).smulRight
      ((EuclideanSpace.proj k).smulRight ((EuclideanSpace.proj m).smulRight (e l)))
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hBeval (l j k m : Fin n) (u v w : V) :
      B l j k m u v w = u j • v k • w m • e l := rfl
  have hTensor : T = ∑ l, ∑ j, ∑ k, ∑ m, (T (e j) (e k) (e m)) l • B l j k m := by
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro j0
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro k0
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro m0
    ext l0
    change (EuclideanSpace.proj l0) (T (b j0) (b k0) (b m0)) = (EuclideanSpace.proj l0)
      ((∑ l, ∑ j, ∑ k, ∑ m, (T (e j) (e k) (e m)) l • B l j k m)
        (b j0) (b k0) (b m0))
    simp only [b, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      sum_apply, smul_apply, map_sum, map_smul, hBeval, smul_eq_mul]
    simp [e, EuclideanSpace.coe_proj, EuclideanSpace.single, PiLp.single_apply,
      mul_ite, ite_mul]
  have hq := congrArg (fun U : FS => (EuclideanSpace.proj alpha) (qS U)) hTensor
  simp only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.coe_proj] at hq
  simpa only [B, e, mul_comm] using hq.symm

theorem curvature_contract_principal_algebra {n d : ℕ}
    (theta : Fin n → Fin n → Fin n → Fin n → ℝ)
    (basis : Fin d → Fin n → Fin n → Fin n → Fin n → ℝ)
    (alpha : Fin d)
    (hbasis : ∀ beta, curvatureRawContraction theta (basis beta) =
      if beta = alpha then 1 else 0)
    (a : Fin n → ℝ) (df : Fin d → Fin n → ℝ) :
    (∑ l, ∑ j, ∑ k, ∑ m, theta l j k m *
      (∑ i, a i * ∑ beta, basis beta l j k m * df beta i)) =
      ∑ i, a i * df alpha i := by
  classical
  let L := curvatureRawContraction theta
  have hsum :
      (fun l j k m => ∑ i, a i * ∑ beta, basis beta l j k m * df beta i) =
      ∑ i, a i • ∑ beta, df beta i • basis beta := by
    funext l j k m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [mul_comm]
  change L (fun l j k m => ∑ i, a i * ∑ beta, basis beta l j k m * df beta i) = _
  rw [hsum, map_sum]
  simp only [map_smul, map_sum, smul_eq_mul]
  change (∑ i, a i * ∑ beta, df beta i * curvatureRawContraction theta (basis beta)) = _
  simp only [hbasis, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem curvature_contract_fderiv_algebra {n : ℕ}
    (theta : Fin n → Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (x v : EuclideanSpace ℝ (Fin n))
    (hf : ∀ l j k m, DifferentiableAt ℝ (f l j k m) x) :
    fderiv ℝ (fun y => ∑ l, ∑ j, ∑ k, ∑ m, theta l j k m * f l j k m y) x v =
      ∑ l, ∑ j, ∑ k, ∑ m, theta l j k m * fderiv ℝ (f l j k m) x v := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
        HasFDerivAt.fun_sum (u := Finset.univ) (fun m _ =>
          (hf l j k m).hasFDerivAt.const_mul (theta l j k m)))))
  have heq := congrArg (fun L => L v) h.fderiv
  simpa only [sum_apply, smul_apply, smul_eq_mul] using heq

theorem curvature_contract_divergence_algebra {n : ℕ}
    (theta : Fin n → Fin n → Fin n → Fin n → ℝ)
    (f : Fin n → Fin n → Fin n → Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (hf : ∀ i l j k m, DifferentiableAt ℝ (f i l j k m) x) :
    (∑ l, ∑ j, ∑ k, ∑ m, theta l j k m *
      ∑ i, fderiv ℝ (f i l j k m) x (EuclideanSpace.single i 1)) =
    ∑ i, fderiv ℝ (fun y => ∑ l, ∑ j, ∑ k, ∑ m, theta l j k m * f i l j k m y)
      x (EuclideanSpace.single i 1) := by
  classical
  let L := curvatureRawContraction theta
  let T := fun i l j k m => fderiv ℝ (f i l j k m) x (EuclideanSpace.single i 1)
  calc
    _ = L (∑ i, T i) := by
      simp only [L, curvatureRawContraction, LinearMap.coe_mk, AddHom.coe_mk,
        Finset.sum_apply, T]
    _ = ∑ i, L (T i) := map_sum L _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (curvature_contract_fderiv_algebra theta (f i) x
        (EuclideanSpace.single i 1) (hf i)).symm

end CurvatureBundleCoordinates

end PoincareConjecture.Proofs.M03
