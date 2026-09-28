import PoincareConjecture.Proofs.M03.Existence.DeTurckGeneratorRegularityNative
import Mathlib.Topology.Constructions

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Metric
open scoped Topology SchwartzMap ContDiff LineDeriv

noncomputable section

namespace PoincareConjecture.DeTurckHigherDomainNative

open EuclideanTranslationNative EuclideanDerivativeNative DeTurckDomainRegularityNative
  DeTurckGeneratorRegularityNative

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

def HasWeakSchwartzDerivative (u d : ScalarL2 n) (v : E) : Prop :=
  ∀ φ : 𝓢(E, ℝ), inner ℝ d (φ.toLp 2 volume) =
    -inner ℝ u ((∂_{v} φ).toLp 2 volume)

theorem hasWeakSchwartzDerivative_of_integral (u d : ScalarL2 n) (v : E)
    (hd : ∀ φ : 𝓢(E, ℝ), inner ℝ d (φ.toLp 2 volume) =
      -(∫ x, u x * fderiv ℝ φ x v)) : HasWeakSchwartzDerivative u d v := by
  intro φ
  rw [inner_schwartz u (∂_{v} φ)]
  exact hd φ

def schwartzProduct (a φ : 𝓢(E, ℝ)) : 𝓢(E, ℝ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) a φ

@[simp] theorem schwartzProduct_apply (a φ : 𝓢(E, ℝ)) (x : E) :
    schwartzProduct a φ x = a x * φ x := rfl

theorem schwartzProduct_toLp (a φ : 𝓢(E, ℝ)) :
    (schwartzProduct a φ).toLp 2 volume = schwartzMultiplier a (φ.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(schwartzProduct a φ).coeFn_toLp 2 volume,
    schwartzMultiplier_coe a (φ.toLp 2 volume), φ.coeFn_toLp 2 volume]
    with x hleft hright hφ
  rw [hleft, hright, hφ, schwartzProduct_apply]

theorem lineDeriv_schwartzProduct (a φ : 𝓢(E, ℝ)) (v : E) :
    ∂_{v} (schwartzProduct a φ) =
      schwartzProduct a (∂_{v} φ) + schwartzProduct (∂_{v} a) φ := by
  ext x
  change fderiv ℝ (fun y => a y * φ y) x v =
    a x * fderiv ℝ φ x v + fderiv ℝ a x v * φ x
  rw [fderiv_fun_mul a.differentiableAt φ.differentiableAt]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

theorem lineDeriv_schwartzProduct_toLp (a φ : 𝓢(E, ℝ)) (v : E) :
    (∂_{v} (schwartzProduct a φ)).toLp 2 volume =
      schwartzMultiplier a ((∂_{v} φ).toLp 2 volume) +
        schwartzMultiplier (∂_{v} a) (φ.toLp 2 volume) := by
  rw [lineDeriv_schwartzProduct]
  change SchwartzMap.toLpCLM ℝ ℝ 2 volume (_ + _) = _
  rw [map_add]
  simp only [SchwartzMap.toLpCLM_apply, schwartzProduct_toLp]

theorem HasWeakSchwartzDerivative.mul (u d : ScalarL2 n) (v : E)
    (hd : HasWeakSchwartzDerivative u d v) (a : 𝓢(E, ℝ)) :
    HasWeakSchwartzDerivative (schwartzMultiplier a u)
      (schwartzMultiplier a d + schwartzMultiplier (∂_{v} a) u) v := by
  intro φ
  have h := hd (schwartzProduct a φ)
  rw [schwartzProduct_toLp, lineDeriv_schwartzProduct_toLp, inner_add_right] at h
  rw [inner_add_left, schwartzMultiplier_selfAdjoint,
    schwartzMultiplier_selfAdjoint, schwartzMultiplier_selfAdjoint]
  linarith only [h]

theorem HasWeakSchwartzDerivative.unique {u d e : ScalarL2 n} {v : E}
    (hd : HasWeakSchwartzDerivative u d v) (he : HasWeakSchwartzDerivative u e v) :
    d = e := by
  apply (SchwartzMap.denseRange_toLpCLM (F := ℝ)
    (μ := (volume : Measure E)) (by norm_num : (2 : ENNReal) ≠ ⊤)).eq_of_inner_left ℝ
  intro φ
  exact (hd φ).trans (he φ).symm

theorem HasWeakSchwartzDerivative.cutoff_fixed {u d : ScalarL2 n} {v : E}
    (hd : HasWeakSchwartzDerivative u d v) {K U : Set E} (hU : IsOpen U) (hKU : K ⊆ U)
    (huK : ∀ᵐ x ∂volume, x ∉ K → u x = 0)
    (η : 𝓢(E, ℝ)) (hη : ∀ x ∈ U, η x = 1) : schwartzMultiplier η d = d := by
  have hηD (x : E) (hx : x ∈ K) : (∂_{v} η) x = 0 := by
    have heq : (η : E → ℝ) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [hU.mem_nhds (hKU hx)] with y hy
      exact hη y hy
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, heq.fderiv_eq,
      fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply]
  have hfix : schwartzMultiplier η u = u := by
    apply Lp.ext
    filter_upwards [schwartzMultiplier_coe η u, huK] with x hmul hz
    rw [hmul]
    by_cases hx : x ∈ K
    · rw [hη x (hKU hx), one_mul]
    · rw [hz hx, mul_zero]
  have hzero : schwartzMultiplier (∂_{v} η) u = 0 := by
    apply Lp.ext
    filter_upwards [schwartzMultiplier_coe (∂_{v} η) u, huK,
      Lp.coeFn_zero ℝ 2 (volume : Measure E)] with x hmul hz h0
    rw [hmul, h0, Pi.zero_apply]
    by_cases hx : x ∈ K
    · rw [hηD x hx, zero_mul]
    · rw [hz hx, mul_zero]
  have hprod := HasWeakSchwartzDerivative.mul u d v hd η
  rw [hfix, hzero, add_zero] at hprod
  exact hprod.unique hd

theorem integrable_of_cutoff_fixed (u : ScalarL2 n) (η : 𝓢(E, ℝ))
    (hfix : schwartzMultiplier η u = u) : Integrable (u : E → ℝ) volume := by
  have hprod : Integrable (fun x => η x * u x) volume :=
    (η.memLp 2 volume).integrable_mul (Lp.memLp u)
  have heq := schwartzMultiplier_coe η u
  rw [hfix] at heq
  exact hprod.congr heq.symm

theorem HasWeakSchwartzDerivative.integrable_of_ae_compact_support
    {u d : ScalarL2 n} {v : E} (hd : HasWeakSchwartzDerivative u d v)
    {K : Set E} (hK : IsCompact K) (huK : ∀ᵐ x ∂volume, x ∉ K → u x = 0) :
    Integrable (d : E → ℝ) volume := by
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  let b : ContDiffBump (0 : E) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  let η : 𝓢(E, ℝ) := b.hasCompactSupport.toSchwartzMap b.contDiff
  have hKU : K ⊆ ball (0 : E) (R + 1) := by
    intro x hx
    rw [mem_ball, dist_zero_right]
    exact (hbound x hx).trans_lt (by linarith)
  have hone : ∀ x ∈ ball (0 : E) (R + 1), η x = 1 := by
    intro x hx
    exact b.one_of_mem_closedBall (ball_subset_closedBall hx)
  exact integrable_of_cutoff_fixed d η
    (hd.cutoff_fixed isOpen_ball hKU huK η hone)

theorem ae_support_of_cutoff_fixed (u : ScalarL2 n) (η : 𝓢(E, ℝ))
    (hfix : schwartzMultiplier η u = u) :
    ∀ᵐ x ∂volume, x ∉ tsupport η → u x = 0 := by
  have heq := schwartzMultiplier_coe η u
  rw [hfix] at heq
  filter_upwards [heq] with x hx
  intro hη
  rw [hx, image_eq_zero_of_notMem_tsupport hη, zero_mul]

theorem HasWeakSchwartzDerivative.exists_ae_compact_support
    {u d : ScalarL2 n} {v : E} (hd : HasWeakSchwartzDerivative u d v)
    {K : Set E} (hK : IsCompact K) (huK : ∀ᵐ x ∂volume, x ∉ K → u x = 0) :
    ∃ K' : Set E, IsCompact K' ∧ ∀ᵐ x ∂volume, x ∉ K' → d x = 0 := by
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  let b : ContDiffBump (0 : E) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  let η : 𝓢(E, ℝ) := b.hasCompactSupport.toSchwartzMap b.contDiff
  have hKU : K ⊆ ball (0 : E) (R + 1) := by
    intro x hx
    rw [mem_ball, dist_zero_right]
    exact (hbound x hx).trans_lt (by linarith)
  have hone : ∀ x ∈ ball (0 : E) (R + 1), η x = 1 := by
    intro x hx
    exact b.one_of_mem_closedBall (ball_subset_closedBall hx)
  exact ⟨tsupport η, b.hasCompactSupport,
    ae_support_of_cutoff_fixed d η (hd.cutoff_fixed isOpen_ball hKU huK η hone)⟩

theorem lineDeriv_schwartz_comm (φ : 𝓢(E, ℝ)) (v w : E) :
    ∂_{v} (∂_{w} φ) = ∂_{w} (∂_{v} φ) := by
  ext x
  have hD : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((φ.smooth 2).contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  change fderiv ℝ (fun y => fderiv ℝ φ y w) x v =
    fderiv ℝ (fun y => fderiv ℝ φ y v) x w
  rw [fderiv_clm_apply hD (differentiableAt_const w),
    fderiv_clm_apply hD (differentiableAt_const v)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, fderiv_fun_const, Pi.zero_apply,
    ContinuousLinearMap.zero_apply,
    map_zero, zero_add]
  exact ((φ.smooth 2).contDiffAt.isSymmSndFDerivAt (by norm_num)).eq v w

theorem weakSecond_symmetric (u : ScalarL2 n) (D : Fin n → ScalarL2 n)
    (W : Fin n → Fin n → ScalarL2 n)
    (hD : ∀ i, HasWeakSchwartzDerivative u (D i) (EuclideanSpace.single i (1 : ℝ)))
    (hW : ∀ i j, HasWeakSchwartzDerivative (D i) (W i j)
      (EuclideanSpace.single j (1 : ℝ))) (i j : Fin n) : W i j = W j i := by
  apply (SchwartzMap.denseRange_toLpCLM (F := ℝ)
    (μ := (volume : Measure E)) (by norm_num : (2 : ENNReal) ≠ ⊤)).eq_of_inner_left ℝ
  intro φ
  change inner ℝ (W i j) (φ.toLp 2 volume) = inner ℝ (W j i) (φ.toLp 2 volume)
  rw [hW i j φ, hW j i φ, hD i, hD j, neg_neg, neg_neg,
    lineDeriv_schwartz_comm φ (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single j (1 : ℝ))]

def differentiatedSource (A : Fin n → Fin n → 𝓢(E, ℝ))
    (D : Fin n → ScalarL2 n) (W : Fin n → Fin n → ScalarL2 n)
    (Gk : ScalarL2 n) (k : Fin n) : ScalarL2 n :=
  Gk + ∑ i, ∑ j,
    (schwartzMultiplier
      (∂_{EuclideanSpace.single j (1 : ℝ)} (∂_{EuclideanSpace.single k (1 : ℝ)} (A i j)))
      (D i) + schwartzMultiplier (∂_{EuclideanSpace.single k (1 : ℝ)} (A i j)) (W i j))

theorem differentiated_divergence_equation
    (A : Fin n → Fin n → 𝓢(E, ℝ)) (D : Fin n → ScalarL2 n)
    (W : Fin n → Fin n → ScalarL2 n) (G Gk : ScalarL2 n) (k : Fin n)
    (hW : ∀ i j, HasWeakSchwartzDerivative (D i) (W i j)
      (EuclideanSpace.single j (1 : ℝ)))
    (hG : HasWeakSchwartzDerivative G Gk (EuclideanSpace.single k (1 : ℝ)))
    {U : Set E}
    (heq : ∀ (φ : 𝓢(E, ℝ)), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i, ∑ j, inner ℝ (schwartzMultiplier (A i j) (D i))
        ((∂_{EuclideanSpace.single j (1 : ℝ)} φ).toLp 2 volume)) =
          inner ℝ G (φ.toLp 2 volume))
    (φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∑ i, ∑ j, inner ℝ (schwartzMultiplier (A i j) (W i k))
      ((∂_{EuclideanSpace.single j (1 : ℝ)} φ).toLp 2 volume)) =
        inner ℝ (differentiatedSource A D W Gk k) (φ.toLp 2 volume) := by
  let v : E := EuclideanSpace.single k (1 : ℝ)
  have hφD : HasCompactSupport ((∂_{v} φ : 𝓢(E, ℝ)) : E → ℝ) :=
    hφ.of_isClosed_subset (isClosed_tsupport _) (SchwartzMap.tsupport_lineDerivOp_subset v φ)
  have htest := heq (∂_{v} φ) hφD
    ((SchwartzMap.tsupport_lineDerivOp_subset _ _).trans hφU)
  have hproduct (i j : Fin n) :
      inner ℝ (schwartzMultiplier (A i j) (W i k))
        ((∂_{EuclideanSpace.single j (1 : ℝ)} φ).toLp 2 volume) +
      inner ℝ (schwartzMultiplier (∂_{v} (A i j)) (D i))
        ((∂_{EuclideanSpace.single j (1 : ℝ)} φ).toLp 2 volume) =
        -inner ℝ (schwartzMultiplier (A i j) (D i))
          ((∂_{EuclideanSpace.single j (1 : ℝ)} (∂_{v} φ)).toLp 2 volume) := by
    have h := HasWeakSchwartzDerivative.mul (D i) (W i k) v (hW i k) (A i j)
      (∂_{EuclideanSpace.single j (1 : ℝ)} φ)
    simpa only [inner_add_left, lineDeriv_schwartz_comm φ v
      (EuclideanSpace.single j (1 : ℝ))] using h
  have hcorrection (i j : Fin n) :
      inner ℝ
        (schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} (∂_{v} (A i j))) (D i) +
          schwartzMultiplier (∂_{v} (A i j)) (W i j)) (φ.toLp 2 volume) =
        -inner ℝ (schwartzMultiplier (∂_{v} (A i j)) (D i))
          ((∂_{EuclideanSpace.single j (1 : ℝ)} φ).toLp 2 volume) := by
    have h := HasWeakSchwartzDerivative.mul (D i) (W i j)
      (EuclideanSpace.single j (1 : ℝ)) (hW i j) (∂_{v} (A i j)) φ
    simpa only [add_comm] using h
  have htotal := congrArg (fun f : Fin n → Fin n → ℝ => ∑ i, ∑ j, f i j)
    (funext (fun i => funext (fun j => hproduct i j)))
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib] at htotal
  rw [htest, ← hG φ] at htotal
  have hcorrectionTotal := congrArg (fun f : Fin n → Fin n → ℝ => ∑ i, ∑ j, f i j)
    (funext (fun i => funext (fun j => hcorrection i j)))
  simp only [inner_add_left, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    at hcorrectionTotal
  dsimp only [v] at htotal hcorrectionTotal
  simp only [differentiatedSource, inner_add_left, sum_inner, Finset.sum_add_distrib]
  linarith only [htotal, hcorrectionTotal]

theorem norm_differentiatedSource_le (A : Fin n → Fin n → 𝓢(E, ℝ))
    (D : Fin n → ScalarL2 n) (W : Fin n → Fin n → ScalarL2 n)
    (Gk : ScalarL2 n) (k : Fin n) :
    ‖differentiatedSource A D W Gk k‖ ≤ ‖Gk‖ + ∑ i, ∑ j,
      (‖schwartzMultiplier
        (∂_{EuclideanSpace.single j (1 : ℝ)} (∂_{EuclideanSpace.single k (1 : ℝ)} (A i j)))‖ *
          ‖D i‖ +
        ‖schwartzMultiplier (∂_{EuclideanSpace.single k (1 : ℝ)} (A i j))‖ * ‖W i j‖) := by
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  exact (norm_add_le _ _).trans
    (add_le_add ((schwartzMultiplier _).le_opNorm _) ((schwartzMultiplier _).le_opNorm _))

theorem exists_secondDerivatives_of_approximation
    (S : ℕ → 𝓢(E, ℝ)) (u : ScalarL2 n) (D : Fin n → ScalarL2 n)
    (hS : Tendsto (fun m => (S m).toLp 2 volume) atTop (𝓝 u))
    (hD : ∀ i, Tendsto (fun m =>
      (∂_{EuclideanSpace.single i (1 : ℝ)} (S m)).toLp 2 volume) atTop (𝓝 (D i)))
    (A : Fin n → Fin n → 𝓢(E, ℝ)) {K : Set E}
    (hcompact : ∀ m, HasCompactSupport (S m)) (hSK : ∀ m, tsupport (S m) ⊆ K)
    {r ell B : ℝ} (hr : 0 < r) (hEll : 0 < ell) (hB : 0 ≤ B)
    (hell : ∀ x ∈ cthickening (r + r) K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (hAB : ∀ i j x, ‖fderiv ℝ (A i j) x‖ ≤ B)
    (G : ScalarL2 n) (hL1 : ∀ i, Integrable (D i : E → ℝ) volume)
    (heq : ∀ (φ : 𝓢(E, ℝ)), HasCompactSupport φ →
      tsupport φ ⊆ cthickening (r + r) K →
      (∑ i, ∑ j, inner ℝ (schwartzMultiplier (A i j) (D i))
        ((∂_{EuclideanSpace.single j (1 : ℝ)} φ).toLp 2 volume)) =
          inner ℝ G (φ.toLp 2 volume)) :
    ∃ W : Fin n → Fin n → ScalarL2 n, ∀ i k,
      ‖W i k‖ ≤ (‖G‖ + (n : ℝ) * B * (∑ j, ‖D j‖)) / ell ∧
        HasWeakSchwartzDerivative (D i) (W i k) (EuclideanSpace.single k (1 : ℝ)) := by
  let J : ℕ → ScalarL2 n × (Fin n → ScalarL2 n) := fun m =>
    ((S m).toLp 2 volume, fun i =>
      (∂_{EuclideanSpace.single i (1 : ℝ)} (S m)).toLp 2 volume)
  let β := closure (range J)
  let e : ℕ → β := Set.inclusion subset_closure ∘ Set.rangeFactorization J
  have he : DenseRange e :=
    ((denseRange_inclusion_iff subset_closure).2 Subset.rfl).comp
      rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)
  have hJ : Tendsto J atTop (𝓝 (u, D)) :=
    hS.prodMk_nhds (tendsto_pi_nhds.mpr hD)
  have hz : (u, D) ∈ closure (range J) :=
    mem_closure_of_tendsto hJ (Eventually.of_forall (fun m => mem_range_self m))
  let z : β := ⟨(u, D), hz⟩
  obtain ⟨W, hW⟩ := exists_secondDerivatives_of_weak_equation_integrable
    e he S (fun y : β => y.val.1) (fun i y => y.val.2 i)
    (continuous_fst.comp continuous_subtype_val)
    (fun i => (continuous_apply i).comp (continuous_snd.comp continuous_subtype_val))
    (fun _ => rfl) (fun _ _ => rfl) A hSK hr hEll hB hell hAB G z hL1
    (fun k h hh m => heq (quotientTestSchwartz (S m) (EuclideanSpace.single k (1 : ℝ)) h)
      (quotientTestSchwartz_hasCompactSupport _ (hcompact m) _ _)
      (tsupport_quotientTestSchwartz_subset _ _ _ (hSK m) hr.le hh))
  refine ⟨W, ?_⟩
  intro i k
  exact ⟨(hW i k).1, hasWeakSchwartzDerivative_of_integral _ _ _ (hW i k).2⟩

theorem exists_secondDerivatives_of_weak_first
    (u : ScalarL2 n) (D : Fin n → ScalarL2 n)
    (hD : ∀ i, HasWeakSchwartzDerivative u (D i) (EuclideanSpace.single i (1 : ℝ)))
    {K : Set E} (hK : IsCompact K) (huK : ∀ᵐ x ∂volume, x ∉ K → u x = 0)
    (A : Fin n → Fin n → 𝓢(E, ℝ)) {r ell B : ℝ}
    (hr : 0 < r) (hEll : 0 < ell) (hB : 0 ≤ B)
    (hell : ∀ x ∈ cthickening (3 * r) K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (hAB : ∀ i j x, ‖fderiv ℝ (A i j) x‖ ≤ B) (G : ScalarL2 n)
    (heq : ∀ (φ : 𝓢(E, ℝ)), HasCompactSupport φ →
      tsupport φ ⊆ cthickening (3 * r) K →
      (∑ i, ∑ j, inner ℝ (schwartzMultiplier (A i j) (D i))
        ((∂_{EuclideanSpace.single j (1 : ℝ)} φ).toLp 2 volume)) =
          inner ℝ G (φ.toLp 2 volume)) :
    ∃ W : Fin n → Fin n → ScalarL2 n, ∀ i k,
      ‖W i k‖ ≤ (‖G‖ + (n : ℝ) * B * (∑ j, ‖D j‖)) / ell ∧
        HasWeakSchwartzDerivative (D i) (W i k) (EuclideanSpace.single k (1 : ℝ)) := by
  let q : List (Fin n) → ScalarL2 n
    | [] => u
    | i :: _ => D i
  have hqweak : ∀ w : List (Fin n), w.length < 1 → ∀ i (φ : 𝓢(E, ℝ)),
      inner ℝ (q (i :: w)) (φ.toLp 2 volume) =
        -(∫ x, q w x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) := by
    intro w hw i φ
    have hwzero : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst w
    simpa only [q, inner_schwartz, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hD i φ
  obtain ⟨S, hSsupport, hSjet⟩ := exists_schwartz_approximation_of_finite_weak_jets
    q 1 hK huK hqweak hr
  have hSu : Tendsto (fun m => (S m).toLp 2 volume) atTop (𝓝 u) := by
    simpa only [orderedSchwartzDerivative, q] using hSjet [] (by simp)
  have hSD (i : Fin n) : Tendsto (fun m =>
      (∂_{EuclideanSpace.single i (1 : ℝ)} (S m)).toLp 2 volume) atTop (𝓝 (D i)) := by
    simpa only [orderedSchwartzDerivative, q] using hSjet [i] (by simp)
  have hthick : cthickening (r + r) (cthickening r K) ⊆ cthickening (3 * r) K := by
    simpa only [show r + r + r = 3 * r by ring] using
      cthickening_cthickening_subset (add_nonneg hr.le hr.le) hr.le K
  exact exists_secondDerivatives_of_approximation S u D hSu hSD A
    (fun m => (hSsupport m).1) (fun m => (hSsupport m).2) hr hEll hB
    (fun x hx => hell x (hthick hx)) hAB G
    (fun i => (hD i).integrable_of_ae_compact_support hK huK)
    (fun φ hφ hφK => heq φ hφ (hφK.trans hthick))

theorem exists_thirdDerivatives_of_weak_second
    (u : ScalarL2 n) (D : Fin n → ScalarL2 n)
    (W : Fin n → Fin n → ScalarL2 n)
    (hD : ∀ i, HasWeakSchwartzDerivative u (D i) (EuclideanSpace.single i (1 : ℝ)))
    (hW : ∀ i j, HasWeakSchwartzDerivative (D i) (W i j)
      (EuclideanSpace.single j (1 : ℝ)))
    {K : Set E} (hK : IsCompact K) (huK : ∀ᵐ x ∂volume, x ∉ K → u x = 0)
    (A : Fin n → Fin n → 𝓢(E, ℝ)) {r ell B : ℝ}
    (hr : 0 < r) (hEll : 0 < ell) (hB : 0 ≤ B)
    (hell : ∀ x ∈ cthickening (3 * r) K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (hAB : ∀ i j x, ‖fderiv ℝ (A i j) x‖ ≤ B)
    (G : ScalarL2 n) (Gk : Fin n → ScalarL2 n)
    (hGk : ∀ k, HasWeakSchwartzDerivative G (Gk k) (EuclideanSpace.single k (1 : ℝ)))
    (heq : ∀ (φ : 𝓢(E, ℝ)), HasCompactSupport φ →
      tsupport φ ⊆ cthickening (3 * r) K →
      (∑ i, ∑ j, inner ℝ (schwartzMultiplier (A i j) (D i))
        ((∂_{EuclideanSpace.single j (1 : ℝ)} φ).toLp 2 volume)) =
          inner ℝ G (φ.toLp 2 volume)) :
    ∃ V : Fin n → Fin n → Fin n → ScalarL2 n, ∀ k i j,
      ‖V k i j‖ ≤ (‖Gk k‖ + ∑ a, ∑ b,
        (‖schwartzMultiplier
          (∂_{EuclideanSpace.single b (1 : ℝ)} (∂_{EuclideanSpace.single k (1 : ℝ)} (A a b)))‖ *
            ‖D a‖ +
          ‖schwartzMultiplier (∂_{EuclideanSpace.single k (1 : ℝ)} (A a b))‖ * ‖W a b‖) +
        (n : ℝ) * B * (∑ l, ‖W l k‖)) / ell ∧
        HasWeakSchwartzDerivative (W i k) (V k i j) (EuclideanSpace.single j (1 : ℝ)) := by
  let q : List (Fin n) → ScalarL2 n
    | [] => u
    | [i] => D i
    | i :: j :: _ => W j i
  have hqweak : ∀ w : List (Fin n), w.length < 2 → ∀ i (φ : 𝓢(E, ℝ)),
      inner ℝ (q (i :: w)) (φ.toLp 2 volume) =
        -(∫ x, q w x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) := by
    intro w hw i φ
    cases w with
    | nil =>
      simpa only [q, inner_schwartz, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hD i φ
    | cons j w =>
      have hwzero : w = [] := List.eq_nil_of_length_eq_zero
        (by simp only [List.length_cons] at hw; omega)
      subst w
      simpa only [q, inner_schwartz, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hW j i φ
  obtain ⟨S, hSsupport, hSjet⟩ := exists_schwartz_approximation_of_finite_weak_jets
    q 2 hK huK hqweak hr
  have hSu (k : Fin n) : Tendsto (fun m =>
      (∂_{EuclideanSpace.single k (1 : ℝ)} (S m)).toLp 2 volume) atTop (𝓝 (D k)) := by
    simpa only [orderedSchwartzDerivative, q] using hSjet [k] (by simp)
  have hSD (k i : Fin n) : Tendsto (fun m =>
      (∂_{EuclideanSpace.single i (1 : ℝ)} (∂_{EuclideanSpace.single k (1 : ℝ)} (S m))).toLp
        2 volume) atTop (𝓝 (W i k)) := by
    have h := hSjet [i, k] (by simp)
    simpa only [orderedSchwartzDerivative, q, weakSecond_symmetric u D W hD hW k i] using h
  have hWint (i k : Fin n) : Integrable (W i k : E → ℝ) volume := by
    obtain ⟨K', hK', hDK⟩ := (hD i).exists_ae_compact_support hK huK
    exact (hW i k).integrable_of_ae_compact_support hK' hDK
  have hthick : cthickening (r + r) (cthickening r K) ⊆ cthickening (3 * r) K := by
    simpa only [show r + r + r = 3 * r by ring] using
      cthickening_cthickening_subset (add_nonneg hr.le hr.le) hr.le K
  have hthird (k : Fin n) : ∃ V : Fin n → Fin n → ScalarL2 n, ∀ i j,
      ‖V i j‖ ≤ (‖differentiatedSource A D W (Gk k) k‖ +
        (n : ℝ) * B * (∑ l, ‖W l k‖)) / ell ∧
        HasWeakSchwartzDerivative (W i k) (V i j) (EuclideanSpace.single j (1 : ℝ)) := by
    apply exists_secondDerivatives_of_approximation
      (fun m => ∂_{EuclideanSpace.single k (1 : ℝ)} (S m)) (D k) (fun i => W i k)
      (hSu k) (hSD k) A
      (fun m => (hSsupport m).1.of_isClosed_subset (isClosed_tsupport _)
        (SchwartzMap.tsupport_lineDerivOp_subset _ _))
      (fun m => (SchwartzMap.tsupport_lineDerivOp_subset _ _).trans (hSsupport m).2)
      hr hEll hB (fun x hx => hell x (hthick hx)) hAB
      (differentiatedSource A D W (Gk k) k) (fun i => hWint i k)
    intro φ hφ hφK
    exact differentiated_divergence_equation A D W G (Gk k) k hW (hGk k)
      heq φ hφ (hφK.trans hthick)
  choose V hV using hthird
  refine ⟨V, ?_⟩
  intro k i j
  exact ⟨(hV k i j).1.trans (div_le_div_of_nonneg_right
    (add_le_add (norm_differentiatedSource_le A D W (Gk k) k) le_rfl) hEll.le),
    (hV k i j).2⟩

def IsWeakSchwartzJet (q : List (Fin n) → ScalarL2 n) (m : ℕ) : Prop :=
  ∀ w, w.length < m → ∀ i,
    HasWeakSchwartzDerivative (q w) (q (i :: w)) (EuclideanSpace.single i (1 : ℝ))

theorem IsWeakSchwartzJet.exists_ae_compact_support
    {q : List (Fin n) → ScalarL2 n} {m : ℕ} (hq : IsWeakSchwartzJet q m)
    {K : Set E} (hK : IsCompact K) (hqK : ∀ᵐ x ∂volume, x ∉ K → q [] x = 0)
    (w : List (Fin n)) (hw : w.length ≤ m) :
    ∃ K' : Set E, IsCompact K' ∧ ∀ᵐ x ∂volume, x ∉ K' → q w x = 0 := by
  revert hw
  induction w with
  | nil => intro _; exact ⟨K, hK, hqK⟩
  | cons i w ih =>
    intro hw
    have hwm : w.length < m := by simp only [List.length_cons] at hw; omega
    obtain ⟨K', hK', hqK'⟩ := ih hwm.le
    exact (hq w hwm i).exists_ae_compact_support hK' hqK'

theorem tsupport_orderedSchwartzDerivative_subset (w : List (Fin n)) (φ : 𝓢(E, ℝ)) :
    tsupport (orderedSchwartzDerivative w φ) ⊆ tsupport φ := by
  induction w with
  | nil => exact Subset.rfl
  | cons i w ih =>
    exact (SchwartzMap.tsupport_lineDerivOp_subset _ _).trans ih

theorem HasWeakSchwartzDerivative.zero (v : E) :
    HasWeakSchwartzDerivative (0 : ScalarL2 n) 0 v := by
  intro φ
  simp

theorem HasWeakSchwartzDerivative.add {u d f e : ScalarL2 n} {v : E}
    (hu : HasWeakSchwartzDerivative u d v) (hf : HasWeakSchwartzDerivative f e v) :
    HasWeakSchwartzDerivative (u + f) (d + e) v := by
  intro φ
  simp only [inner_add_left, hu φ, hf φ, neg_add_rev]
  ring

theorem HasWeakSchwartzDerivative.sum (u d : Fin n → ScalarL2 n) (v : E)
    (h : ∀ i, HasWeakSchwartzDerivative (u i) (d i) v) :
    HasWeakSchwartzDerivative (∑ i, u i) (∑ i, d i) v := by
  intro φ
  simp only [sum_inner]
  calc
    _ = ∑ i, -inner ℝ (u i) ((∂_{v} φ).toLp 2 volume) :=
      Finset.sum_congr rfl (fun i _ => h i φ)
    _ = _ := by rw [Finset.sum_neg_distrib]

inductive JetExpression (n : ℕ) where
  | zero : JetExpression n
  | term : 𝓢(EuclideanSpace ℝ (Fin n), ℝ) → List (Fin n) → JetExpression n
  | add : JetExpression n → JetExpression n → JetExpression n
  | sum : (Fin n → JetExpression n) → JetExpression n

def JetExpression.eval : JetExpression n → (List (Fin n) → ScalarL2 n) → ScalarL2 n
  | .zero, _ => 0
  | .term a w, q => schwartzMultiplier a (q w)
  | .add e f, q => e.eval q + f.eval q
  | .sum f, q => ∑ i, (f i).eval q

def JetExpression.orderLE : JetExpression n → ℕ → Prop
  | .zero, _ => True
  | .term _ w, m => w.length ≤ m
  | .add e f, m => e.orderLE m ∧ f.orderLE m
  | .sum f, m => ∀ i, (f i).orderLE m

def JetExpression.derivative (i : Fin n) : JetExpression n → JetExpression n
  | .zero => .zero
  | .term a w => .add (.term a (i :: w))
      (.term (∂_{EuclideanSpace.single i (1 : ℝ)} a) w)
  | .add e f => .add (e.derivative i) (f.derivative i)
  | .sum f => .sum (fun j => (f j).derivative i)

theorem JetExpression.orderLE_mono (e : JetExpression n) {m l : ℕ}
    (h : e.orderLE m) (hml : m ≤ l) : e.orderLE l := by
  induction e with
  | zero => trivial
  | term a w => exact h.trans hml
  | add e f ihe ihf => exact ⟨ihe h.1, ihf h.2⟩
  | sum f ih => exact fun i => ih i (h i)

theorem JetExpression.orderLE_derivative (e : JetExpression n) {m : ℕ}
    (h : e.orderLE m) (i : Fin n) : (e.derivative i).orderLE (m + 1) := by
  induction e with
  | zero => trivial
  | term a w =>
    exact ⟨by simpa only [JetExpression.orderLE, List.length_cons] using
        Nat.add_le_add_right h 1,
      h.trans (Nat.le_succ m)⟩
  | add e f ihe ihf => exact ⟨ihe h.1, ihf h.2⟩
  | sum f ih => exact fun j => ih j (h j)

theorem JetExpression.eval_congr (e : JetExpression n) {m : ℕ}
    (h : e.orderLE m) (q q' : List (Fin n) → ScalarL2 n)
    (hqq : ∀ w, w.length ≤ m → q w = q' w) : e.eval q = e.eval q' := by
  induction e with
  | zero => rfl
  | term a w => exact congrArg (schwartzMultiplier a) (hqq w h)
  | add e f ihe ihf => exact congrArg₂ (· + ·) (ihe h.1) (ihf h.2)
  | sum f ih => exact Finset.sum_congr rfl (fun i _ => ih i (h i))

theorem JetExpression.eval_hasWeakDerivative (e : JetExpression n) {m : ℕ}
    (h : e.orderLE m) (q : List (Fin n) → ScalarL2 n) (i : Fin n)
    (hq : ∀ w, w.length ≤ m →
      HasWeakSchwartzDerivative (q w) (q (i :: w)) (EuclideanSpace.single i (1 : ℝ))) :
    HasWeakSchwartzDerivative (e.eval q) ((e.derivative i).eval q)
      (EuclideanSpace.single i (1 : ℝ)) := by
  induction e with
  | zero => exact HasWeakSchwartzDerivative.zero _
  | term a w => exact HasWeakSchwartzDerivative.mul _ _ _ (hq w h) a
  | add e f ihe ihf => exact (ihe h.1).add (ihf h.2)
  | sum f ih => exact HasWeakSchwartzDerivative.sum _ _ _ (fun j => ih j (h j))

def commutatorExpression (A : Fin n → Fin n → 𝓢(E, ℝ)) :
    List (Fin n) → JetExpression n
  | [] => .zero
  | k :: w => .add ((commutatorExpression A w).derivative k)
      (.sum (fun i => .sum (fun j => .add
        (.term (∂_{EuclideanSpace.single j (1 : ℝ)}
          (∂_{EuclideanSpace.single k (1 : ℝ)} (A i j))) (i :: w))
        (.term (∂_{EuclideanSpace.single k (1 : ℝ)} (A i j)) (j :: i :: w)))))

theorem commutatorExpression_order (A : Fin n → Fin n → 𝓢(E, ℝ))
    (w : List (Fin n)) : (commutatorExpression A w).orderLE (w.length + 1) := by
  induction w with
  | nil => trivial
  | cons k w ih =>
    refine ⟨?_, fun i j => ⟨?_, ?_⟩⟩
    · simpa only [List.length_cons] using
        JetExpression.orderLE_derivative (commutatorExpression A w) ih k
    · simp only [JetExpression.orderLE, List.length_cons]; omega
    · exact le_rfl

def commutedSource (A : Fin n → Fin n → 𝓢(E, ℝ))
    (g q : List (Fin n) → ScalarL2 n) (w : List (Fin n)) : ScalarL2 n :=
  g w + (commutatorExpression A w).eval q

def DivergenceEquation (A : Fin n → Fin n → 𝓢(E, ℝ))
    (D : Fin n → ScalarL2 n) (G : ScalarL2 n) (U : Set E) : Prop :=
  ∀ φ : 𝓢(E, ℝ), HasCompactSupport φ → tsupport φ ⊆ U →
    (∑ i, ∑ j, inner ℝ (schwartzMultiplier (A i j) (D i))
      ((∂_{EuclideanSpace.single j (1 : ℝ)} φ).toLp 2 volume)) =
        inner ℝ G (φ.toLp 2 volume)

theorem commuted_divergence_equation (A : Fin n → Fin n → 𝓢(E, ℝ))
    (g q : List (Fin n) → ScalarL2 n) {m : ℕ}
    (hq : IsWeakSchwartzJet q (m + 2)) (hg : IsWeakSchwartzJet g (m + 1))
    (w : List (Fin n)) (hw : w.length ≤ m) (k : Fin n) {U : Set E}
    (heq : DivergenceEquation A (fun i => q (i :: w)) (commutedSource A g q w) U) :
    DivergenceEquation A (fun i => q (i :: k :: w))
      (commutedSource A g q (k :: w)) U := by
  have hW (i j : Fin n) : HasWeakSchwartzDerivative (q (i :: w))
      (q (j :: i :: w)) (EuclideanSpace.single j (1 : ℝ)) :=
    hq (i :: w) (by simp only [List.length_cons]; omega) j
  have hswap (i : Fin n) : q (k :: i :: w) = q (i :: k :: w) :=
    weakSecond_symmetric (q w) (fun a => q (a :: w)) (fun a b => q (b :: a :: w))
      (fun a => hq w (by omega) a) hW i k
  have hsource : HasWeakSchwartzDerivative (commutedSource A g q w)
      (g (k :: w) + ((commutatorExpression A w).derivative k).eval q)
        (EuclideanSpace.single k (1 : ℝ)) :=
    (hg w (by omega) k).add ((commutatorExpression A w).eval_hasWeakDerivative
      (commutatorExpression_order A w) q k (fun v hv => hq v (by omega) k))
  intro φ hφ hφU
  have h := differentiated_divergence_equation A (fun i => q (i :: w))
    (fun i j => q (j :: i :: w)) (commutedSource A g q w)
    (g (k :: w) + ((commutatorExpression A w).derivative k).eval q) k
    hW hsource heq φ hφ hφU
  simpa only [hswap, differentiatedSource, commutedSource, commutatorExpression,
    JetExpression.eval, add_assoc] using h

theorem exists_finite_weakJet_of_divergence
    (u : ScalarL2 n) (D : Fin n → ScalarL2 n)
    (hD : ∀ i, HasWeakSchwartzDerivative u (D i) (EuclideanSpace.single i (1 : ℝ)))
    {K : Set E} (hK : IsCompact K) (huK : ∀ᵐ x ∂volume, x ∉ K → u x = 0)
    (A : Fin n → Fin n → 𝓢(E, ℝ)) {r ell B : ℝ}
    (hr : 0 < r) (hEll : 0 < ell) (hB : 0 ≤ B)
    (hell : ∀ x ∈ cthickening (3 * r) K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (hAB : ∀ i j x, ‖fderiv ℝ (A i j) x‖ ≤ B)
    (g : List (Fin n) → ScalarL2 n)
    (heq : DivergenceEquation A D (g []) (cthickening (3 * r) K)) (s : ℕ) :
    IsWeakSchwartzJet g s → ∃ q : List (Fin n) → ScalarL2 n,
      q [] = u ∧ (∀ i, q [i] = D i) ∧ IsWeakSchwartzJet q (s + 2) ∧
        ∀ w, w.length ≤ s → DivergenceEquation A (fun i => q (i :: w))
          (commutedSource A g q w) (cthickening (3 * r) K) := by
  classical
  induction s with
  | zero =>
    intro _
    obtain ⟨W, hW⟩ := exists_secondDerivatives_of_weak_first u D hD hK huK A
      hr hEll hB hell hAB (g []) heq
    let q : List (Fin n) → ScalarL2 n
      | [] => u
      | [i] => D i
      | i :: j :: _ => W j i
    refine ⟨q, rfl, fun _ => rfl, ?_, ?_⟩
    · intro w hw i
      cases w with
      | nil => exact hD i
      | cons j w =>
        have hwzero : w = [] := List.eq_nil_of_length_eq_zero
          (by simp only [List.length_cons] at hw; omega)
        subst w
        exact (hW j i).2
    · intro w hw
      have hwzero : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst w
      simpa only [commutedSource, commutatorExpression, JetExpression.eval, add_zero, q]
        using heq
  | succ s ih =>
    intro hg
    obtain ⟨q, hq0, hq1, hq, hqe⟩ := ih (fun w hw i => hg w (by omega) i)
    have hqK : ∀ᵐ x ∂volume, x ∉ K → q [] x = 0 := by
      simpa only [hq0] using huK
    have hqe' (w : List (Fin n)) (hw : w.length ≤ s + 1) :
        DivergenceEquation A (fun i => q (i :: w)) (commutedSource A g q w)
          (cthickening (3 * r) K) := by
      cases w with
      | nil => exact hqe [] (by simp)
      | cons k w =>
        have hws : w.length ≤ s := by simp only [List.length_cons] at hw; omega
        exact commuted_divergence_equation A g q hq hg w hws k (hqe w hws)
    have hqint : ∀ w : List (Fin n), w.length < s + 2 → ∀ i (φ : 𝓢(E, ℝ)),
        inner ℝ (q (i :: w)) (φ.toLp 2 volume) =
          -(∫ x, q w x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) := by
      intro w hw i φ
      simpa only [inner_schwartz, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hq w hw i φ
    obtain ⟨S, hSsupport, hSjet⟩ := exists_schwartz_approximation_of_finite_weak_jets
      q (s + 2) hK hqK hqint hr
    have hthick : cthickening (r + r) (cthickening r K) ⊆ cthickening (3 * r) K := by
      simpa only [show r + r + r = 3 * r by ring] using
        cthickening_cthickening_subset (add_nonneg hr.le hr.le) hr.le K
    have hnext (w : {w : List (Fin n) // w.length = s + 1}) :
        ∃ V : Fin n → Fin n → ScalarL2 n, ∀ i j,
          HasWeakSchwartzDerivative (q (i :: w.val)) (V i j)
            (EuclideanSpace.single j (1 : ℝ)) := by
      obtain ⟨K', hK', hqK'⟩ := hq.exists_ae_compact_support hK hqK w.val
        (by rw [w.property]; omega)
      have hfirst (i : Fin n) : Tendsto (fun a =>
          (∂_{EuclideanSpace.single i (1 : ℝ)} (orderedSchwartzDerivative w.val (S a))).toLp
            2 volume) atTop (𝓝 (q (i :: w.val))) := by
        simpa only [orderedSchwartzDerivative] using
          hSjet (i :: w.val) (by simp only [List.length_cons, w.property]; omega)
      obtain ⟨V, hV⟩ := exists_secondDerivatives_of_approximation
        (fun a => orderedSchwartzDerivative w.val (S a)) (q w.val)
        (fun i => q (i :: w.val)) (hSjet w.val (by rw [w.property]; omega)) hfirst A
        (fun a => (hSsupport a).1.of_isClosed_subset (isClosed_tsupport _)
          (tsupport_orderedSchwartzDerivative_subset w.val (S a)))
        (fun a => (tsupport_orderedSchwartzDerivative_subset w.val (S a)).trans
          (hSsupport a).2)
        hr hEll hB (fun x hx => hell x (hthick hx)) hAB (commutedSource A g q w.val)
        (fun i => (hq w.val (by rw [w.property]; omega) i).integrable_of_ae_compact_support
          hK' hqK')
        (fun φ hφ hφK => hqe' w.val (by rw [w.property]) φ hφ (hφK.trans hthick))
      exact ⟨V, fun i j => (hV i j).2⟩
    choose V hV using hnext
    let q' : List (Fin n) → ScalarL2 n
      | j :: i :: w => if hw : w.length = s + 1 then V ⟨w, hw⟩ i j else q (j :: i :: w)
      | w => q w
    have hkeep (w : List (Fin n)) (hw : w.length ≤ s + 2) : q' w = q w := by
      cases w with
      | nil => rfl
      | cons i w =>
        cases w with
        | nil => rfl
        | cons j w =>
          have hne : w.length ≠ s + 1 := by simp only [List.length_cons] at hw; omega
          simp only [q', dif_neg hne]
    have hq' : IsWeakSchwartzJet q' (s + 1 + 2) := by
      intro w hw i
      rw [hkeep w (by omega)]
      by_cases hlow : w.length < s + 2
      · rw [hkeep (i :: w) (by simp only [List.length_cons]; omega)]
        exact hq w hlow i
      · cases w with
        | nil => simp only [List.length_nil] at hlow; omega
        | cons j w =>
          have htop : w.length = s + 1 := by
            simp only [List.length_cons] at hw hlow
            omega
          change HasWeakSchwartzDerivative (q (j :: w))
            (if h : w.length = s + 1 then V ⟨w, h⟩ j i else q (i :: j :: w))
              (EuclideanSpace.single i (1 : ℝ))
          rw [dif_pos htop]
          exact hV ⟨w, htop⟩ j i
    refine ⟨q', (hkeep [] (by simp)).trans hq0,
      fun i => (hkeep [i] (by simp)).trans (hq1 i), hq', ?_⟩
    intro w hw
    have hfirst : (fun i => q' (i :: w)) = fun i => q (i :: w) := by
      funext i
      exact hkeep (i :: w) (by simp only [List.length_cons]; omega)
    have hsource : commutedSource A g q' w = commutedSource A g q w := by
      unfold commutedSource
      congr 1
      exact (commutatorExpression A w).eval_congr (commutatorExpression_order A w) q' q
        (fun v hv => hkeep v (by omega))
    rw [hfirst, hsource]
    exact hqe' w hw

theorem IsWeakSchwartzJet.mono {q : List (Fin n) → ScalarL2 n} {s t : ℕ}
    (hq : IsWeakSchwartzJet q t) (hst : s ≤ t) : IsWeakSchwartzJet q s :=
  fun w hw i => hq w (hw.trans_le hst) i

theorem IsWeakSchwartzJet.sub {q r : List (Fin n) → ScalarL2 n} {s : ℕ}
    (hq : IsWeakSchwartzJet q s) (hr : IsWeakSchwartzJet r s) :
    IsWeakSchwartzJet (fun w => q w - r w) s := by
  intro w hw i φ
  simp only [inner_sub_left, hq w hw i φ, hr w hw i φ]
  ring

theorem HasWeakSchwartzDerivative.finset_sum {ι : Type*} (s : Finset ι)
    (u d : ι → ScalarL2 n) (v : E)
    (h : ∀ i ∈ s, HasWeakSchwartzDerivative (u i) (d i) v) :
    HasWeakSchwartzDerivative (∑ i ∈ s, u i) (∑ i ∈ s, d i) v := by
  intro φ
  simp only [sum_inner]
  calc
    _ = ∑ i ∈ s, -inner ℝ (u i) ((∂_{v} φ).toLp 2 volume) :=
      Finset.sum_congr rfl (fun i hi => h i hi φ)
    _ = _ := by rw [Finset.sum_neg_distrib]

def JetExpression.iteratedDerivative (e : JetExpression n) : List (Fin n) → JetExpression n
  | [] => e
  | i :: w => (e.iteratedDerivative w).derivative i

theorem JetExpression.iteratedDerivative_order (e : JetExpression n) {p : ℕ}
    (he : e.orderLE p) (w : List (Fin n)) :
    (e.iteratedDerivative w).orderLE (p + w.length) := by
  induction w with
  | nil => simpa only [JetExpression.iteratedDerivative, List.length_nil, Nat.add_zero] using he
  | cons i w ih =>
    simpa only [JetExpression.iteratedDerivative, List.length_cons, Nat.add_assoc] using
      (e.iteratedDerivative w).orderLE_derivative ih i

theorem JetExpression.isWeakJet_eval_iteratedDerivative (e : JetExpression n) {p s : ℕ}
    (he : e.orderLE p) (q : List (Fin n) → ScalarL2 n)
    (hq : IsWeakSchwartzJet q (s + p)) :
    IsWeakSchwartzJet (fun w => (e.iteratedDerivative w).eval q) s := by
  intro w hw i
  exact (e.iteratedDerivative w).eval_hasWeakDerivative (e.iteratedDerivative_order he w) q i
    (fun v hv => hq v (by omega) i)

def finiteSourceJet {ι : Type*} [Fintype ι]
    (B : List (Fin n) → ScalarL2 n) (Q : ι → List (Fin n) → ScalarL2 n)
    (e : ι → JetExpression n) (w : List (Fin n)) : ScalarL2 n :=
  B w + ∑ c, ((e c).iteratedDerivative w).eval (Q c)

theorem finiteSourceJet_nil {ι : Type*} [Fintype ι]
    (B : List (Fin n) → ScalarL2 n) (Q : ι → List (Fin n) → ScalarL2 n)
    (e : ι → JetExpression n) :
    finiteSourceJet B Q e [] = B [] + ∑ c, (e c).eval (Q c) := rfl

theorem isWeakSchwartzJet_finiteSourceJet {ι : Type*} [Fintype ι]
    (B : List (Fin n) → ScalarL2 n) (Q : ι → List (Fin n) → ScalarL2 n)
    (e : ι → JetExpression n) {s : ℕ}
    (hB : IsWeakSchwartzJet B s) (hQ : ∀ c, IsWeakSchwartzJet (Q c) (s + 1))
    (he : ∀ c, (e c).orderLE 1) : IsWeakSchwartzJet (finiteSourceJet B Q e) s := by
  intro w hw i
  exact (hB w hw i).add (HasWeakSchwartzDerivative.finset_sum Finset.univ
    (fun c => ((e c).iteratedDerivative w).eval (Q c))
    (fun c => ((e c).iteratedDerivative (i :: w)).eval (Q c))
    (EuclideanSpace.single i (1 : ℝ))
    (fun c _ => (e c).isWeakJet_eval_iteratedDerivative (he c) (Q c) (hQ c) w hw i))

theorem IsWeakSchwartzJet.eq_of_nil_eq
    {q q' : List (Fin n) → ScalarL2 n} {s : ℕ}
    (hq : IsWeakSchwartzJet q s) (hq' : IsWeakSchwartzJet q' s)
    (hzero : q [] = q' []) (w : List (Fin n)) (hw : w.length ≤ s) : q w = q' w := by
  revert hw
  induction w with
  | nil => intro _; exact hzero
  | cons i w ih =>
    intro hw
    have hws : w.length < s := by simp only [List.length_cons] at hw; omega
    have htail : q w = q' w := ih hws.le
    have hd := hq w hws i
    rw [htail] at hd
    exact hd.unique (hq' w hws i)

def JetExpression.firstOrderTerm (a : 𝓢(E, ℝ)) (i : Option (Fin n)) : JetExpression n :=
  .term a (match i with | none => [] | some j => [j])

theorem JetExpression.firstOrderTerm_order (a : 𝓢(E, ℝ)) (i : Option (Fin n)) :
    (JetExpression.firstOrderTerm a i).orderLE 1 := by
  cases i <;> simp [JetExpression.firstOrderTerm, JetExpression.orderLE]

theorem finiteSourceJet_nil_eq_firstOrder {ι : Type*} [Fintype ι]
    (B : List (Fin n) → ScalarL2 n) (Q : ι → List (Fin n) → ScalarL2 n)
    (a : ι → 𝓢(E, ℝ)) (o : ι → Option (Fin n))
    (V : ι → ScalarL2 n) (D : ι → Fin n → ScalarL2 n)
    (hzero : ∀ c, Q c [] = V c) (hfirst : ∀ c i, Q c [i] = D c i) :
    finiteSourceJet B Q (fun c => JetExpression.firstOrderTerm (a c) (o c)) [] =
      B [] + ∑ c, schwartzMultiplier (a c)
        (match o c with | none => V c | some i => D c i) := by
  rw [finiteSourceJet_nil]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  cases h : o c with
  | none => simp only [JetExpression.firstOrderTerm, h, JetExpression.eval, hzero]
  | some i => simp only [JetExpression.firstOrderTerm, h, JetExpression.eval, hfirst]

theorem exists_extended_weakJet_of_finiteSource {ι : Type*} [Fintype ι]
    (q : List (Fin n) → ScalarL2 n) (s : ℕ) (hq : IsWeakSchwartzJet q (s + 1))
    (B : List (Fin n) → ScalarL2 n) (Q : ι → List (Fin n) → ScalarL2 n)
    (e : ι → JetExpression n)
    (hB : IsWeakSchwartzJet B s) (hQ : ∀ c, IsWeakSchwartzJet (Q c) (s + 1))
    (he : ∀ c, (e c).orderLE 1)
    {K : Set E} (hK : IsCompact K) (hqK : ∀ᵐ x ∂volume, x ∉ K → q [] x = 0)
    (A : Fin n → Fin n → 𝓢(E, ℝ)) {r ell C : ℝ}
    (hr : 0 < r) (hEll : 0 < ell) (hC : 0 ≤ C)
    (hell : ∀ x ∈ cthickening (3 * r) K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (hAC : ∀ i j x, ‖fderiv ℝ (A i j) x‖ ≤ C)
    (heq : DivergenceEquation A (fun i => q [i]) (B [] + ∑ c, (e c).eval (Q c))
      (cthickening (3 * r) K)) :
    ∃ q' : List (Fin n) → ScalarL2 n,
      (∀ w, w.length ≤ s + 1 → q' w = q w) ∧ IsWeakSchwartzJet q' (s + 2) ∧
        ∀ w, w.length ≤ s → DivergenceEquation A (fun i => q' (i :: w))
          (commutedSource A (finiteSourceJet B Q e) q' w) (cthickening (3 * r) K) := by
  have hD (i : Fin n) : HasWeakSchwartzDerivative (q []) (q [i])
      (EuclideanSpace.single i (1 : ℝ)) := hq [] (by simp) i
  have hsource : IsWeakSchwartzJet (finiteSourceJet B Q e) s :=
    isWeakSchwartzJet_finiteSourceJet B Q e hB hQ he
  have hbase : DivergenceEquation A (fun i => q [i]) (finiteSourceJet B Q e [])
      (cthickening (3 * r) K) := by
    simpa only [finiteSourceJet_nil] using heq
  obtain ⟨q', hzero, _, hq', hcommuted⟩ := exists_finite_weakJet_of_divergence
    (q []) (fun i => q [i]) hD hK hqK A hr hEll hC hell hAC
    (finiteSourceJet B Q e) hbase s hsource
  exact ⟨q', fun w hw =>
    (hq'.mono (by omega : s + 1 ≤ s + 2)).eq_of_nil_eq hq hzero w hw,
    hq', hcommuted⟩

end PoincareConjecture.DeTurckHigherDomainNative

end
