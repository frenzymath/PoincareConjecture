
import PoincareConjecture.Proofs.M05.Analysis.ODE.Linear
import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Analysis.Calculus.Deriv.Basic











set_option autoImplicit false

open Set
open scoped NNReal

noncomputable section

namespace PoincareConjecture.RicciFlow.Frame

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [FiniteDimensional ℝ V]


structure EvolvingMetricData (J : Set ℝ) where
  metric : ℝ → V →L[ℝ] V →L[ℝ] ℝ
  ricci : ℝ → V →L[ℝ] V →L[ℝ] ℝ
  metric_deriv : ∀ t, HasDerivAt metric (-2 • ricci t) t
  ricci_symm : ∀ t v w, ricci t v w = ricci t w v

private noncomputable def finBasisOperatorEquiv :
    (Fin (Module.finrank ℝ V) → V) ≃L[ℝ] (V →L[ℝ] V) :=
  (((Module.finBasis ℝ V).constr ℝ).trans
    (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V) (F' := V))).toContinuousLinearEquiv

private theorem finBasisOperatorEquiv_apply_basis
    (f : Fin (Module.finrank ℝ V) → V) (i : Fin (Module.finrank ℝ V)) :
    finBasisOperatorEquiv f ((Module.finBasis ℝ V) i) = f i := by
  simp [finBasisOperatorEquiv]


noncomputable def transportCurveOn
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b)) {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) (t : ℝ) : V →L[ℝ] V :=
  finBasisOperatorEquiv (fun i =>
    Poincare.ODE.Linear.solOf hab hcont hK ((Module.finBasis ℝ V) i) t)

@[simp] theorem transportCurveOn_apply_of_mem
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b)) {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) {t : ℝ} (ht : t ∈ Icc a b) (v : V) :
    transportCurveOn (V := V) A hab hcont hK t v =
      Poincare.ODE.Linear.solOf hab hcont hK v t := by
  have hmaps : transportCurveOn (V := V) A hab hcont hK t =
      finBasisOperatorEquiv (fun i =>
        Poincare.ODE.Linear.solOf hab hcont hK ((Module.finBasis ℝ V) i) t) := by
    apply ContinuousLinearMap.coe_injective
    apply (Module.finBasis ℝ V).ext
    intro i
    simp [transportCurveOn, finBasisOperatorEquiv_apply_basis]
  let S : V →ₗ[ℝ] V :=
    { toFun := fun x => Poincare.ODE.Linear.solOf hab hcont hK x t
      map_add' := fun x y => Poincare.ODE.Linear.solOf_add hab hcont hK x y ht
      map_smul' := fun c x => Poincare.ODE.Linear.solOf_smul hab hcont hK c x ht }
  have hS : finBasisOperatorEquiv (fun i =>
      Poincare.ODE.Linear.solOf hab hcont hK ((Module.finBasis ℝ V) i) t) =
      S.toContinuousLinearMap := by
    apply ContinuousLinearMap.coe_injective
    apply (Module.finBasis ℝ V).ext
    intro i
    simp [S, finBasisOperatorEquiv_apply_basis]
  rw [hmaps, hS]
  rfl


theorem transportCurveOn_hasDerivWithinAt
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b)) {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (transportCurveOn (V := V) A hab hcont hK)
      ((A t).comp (transportCurveOn (V := V) A hab hcont hK t)) (Icc a b) t := by
  have hcoord : HasDerivWithinAt
      (fun s : ℝ => fun i : Fin (Module.finrank ℝ V) =>
        Poincare.ODE.Linear.solOf hab hcont hK ((Module.finBasis ℝ V) i) s)
      (fun i : Fin (Module.finrank ℝ V) =>
        A t (Poincare.ODE.Linear.solOf hab hcont hK ((Module.finBasis ℝ V) i) t))
      (Icc a b) t := by
    rw [hasDerivWithinAt_pi]
    intro i
    exact Poincare.ODE.Linear.solOf_isSolOn hab hcont hK _ t ht
  have hraw :=
    (finBasisOperatorEquiv (V := V)).hasFDerivAt.comp_hasDerivWithinAt t hcoord
  convert hraw using 1 <;> try rfl
  apply ContinuousLinearMap.coe_injective
  apply (Module.finBasis ℝ V).ext
  intro i
  simp [transportCurveOn, finBasisOperatorEquiv_apply_basis]

theorem transportCurveOn_continuousOn
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b)) {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) :
    ContinuousOn (transportCurveOn (V := V) A hab hcont hK) (Icc a b) :=
  fun t ht => (transportCurveOn_hasDerivWithinAt A hab hcont hK ht).continuousWithinAt

@[simp] theorem transportCurveOn_left
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b)) {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) :
    transportCurveOn A hab hcont hK a = ContinuousLinearMap.id ℝ V := by
  ext v
  rw [transportCurveOn_apply_of_mem A hab hcont hK ⟨le_rfl, hab⟩]
  exact Poincare.ODE.Linear.solOf_left hab hcont hK v


theorem transportCurveOn_eqOn
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b)) {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    {Ψ : ℝ → V →L[ℝ] V} (hΨa : Ψ a = ContinuousLinearMap.id ℝ V)
    (hΨ : ∀ t ∈ Icc a b,
      HasDerivWithinAt Ψ ((A t).comp (Ψ t)) (Icc a b) t) :
    EqOn (transportCurveOn A hab hcont hK) Ψ (Icc a b) := by
  intro t ht
  ext v
  rw [transportCurveOn_apply_of_mem A hab hcont hK ht]
  apply Poincare.ODE.Linear.IsSolOn.eqOn_of_left hK
    (Poincare.ODE.Linear.solOf_isSolOn hab hcont hK v) (W := fun s => Ψ s v) _ _ ht
  · intro s hs
    simpa using (hΨ s hs).clm_apply (hasDerivWithinAt_const s (Icc a b) v)
  · simp [Poincare.ODE.Linear.solOf_left, hΨa]


theorem transportCurveOn_eqOn_of_le
    (A : ℝ → V →L[ℝ] V) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hcont : ContinuousOn A (Icc a c)) {K L : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (hL : ∀ t ∈ Icc a c, ‖A t‖₊ ≤ L) :
    EqOn (transportCurveOn A hab (hcont.mono (Icc_subset_Icc le_rfl hbc)) hK)
      (transportCurveOn A (hab.trans hbc) hcont hL) (Icc a b) := by
  apply transportCurveOn_eqOn A hab _ hK (transportCurveOn_left A _ _ _)
  intro t ht
  exact (transportCurveOn_hasDerivWithinAt A (hab.trans hbc) hcont hL
    ⟨ht.1, ht.2.trans hbc⟩).mono (Icc_subset_Icc le_rfl hbc)


theorem transportCurveOn_bijective
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b)) {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) {t : ℝ} (ht : t ∈ Icc a b) :
    Function.Bijective (transportCurveOn A hab hcont hK t) := by
  suffices hi : Function.Injective (transportCurveOn A hab hcont hK t) from
    ⟨hi, (LinearMap.injective_iff_surjective
      (f := (transportCurveOn A hab hcont hK t).toLinearMap)).mp hi⟩
  intro v w hvw
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hsol (v : V) : Poincare.ODE.Linear.IsSolOn A a t
      (Poincare.ODE.Linear.solOf hab hcont hK v) :=
    fun s hs => (Poincare.ODE.Linear.solOf_isSolOn hab hcont hK v s (hsub hs)).mono hsub
  have heq := Poincare.ODE.Linear.IsSolOn.eqOn_of_right
    (fun s hs => hK s (hsub hs)) (hsol v) (hsol w)
    (by simpa only [transportCurveOn_apply_of_mem A hab hcont hK ht] using hvw)
    (show a ∈ Icc a t from ⟨le_rfl, ht.1⟩)
  simpa only [Poincare.ODE.Linear.solOf_left] using heq

set_option maxHeartbeats 800000 in
private theorem pairing_deriv_zero {J : Set ℝ} (G : EvolvingMetricData (V := V) J)
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b)) {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (hleft : ∀ t ∈ Icc a b, ∀ v w, G.metric t (A t v) w = G.ricci t v w)
    (hright : ∀ t ∈ Icc a b, ∀ v w, G.metric t v (A t w) = G.ricci t v w)
    (v w : V) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt
      (fun s => G.metric s
        (transportCurveOn (V := V) A hab hcont hK s v)
        (transportCurveOn (V := V) A hab hcont hK s w)) 0 (Icc a b) t := by
  let U := fun s => transportCurveOn (V := V) A hab hcont hK s v
  let W := fun s => transportCurveOn (V := V) A hab hcont hK s w
  have hmetric : HasDerivWithinAt G.metric (-2 • G.ricci t) (Icc a b) t :=
    @HasDerivAt.hasDerivWithinAt ℝ _ (V →L[ℝ] V →L[ℝ] ℝ) _ _
      G.metric (-2 • G.ricci t) t (Icc a b) (G.metric_deriv t)
  have hU₀ := transportCurveOn_hasDerivWithinAt A hab hcont hK ht
  have hW₀ := transportCurveOn_hasDerivWithinAt A hab hcont hK ht
  have hU : HasDerivWithinAt U (A t (U t)) (Icc a b) t := by
    have hh := hU₀.clm_apply
      (hasDerivWithinAt_const (x := t) (s := Icc a b) (c := v))
    simpa [U] using hh
  have hW : HasDerivWithinAt W (A t (W t)) (Icc a b) t := by
    have hh := hW₀.clm_apply
      (hasDerivWithinAt_const (x := t) (s := Icc a b) (c := w))
    simpa [W] using hh
  have h₁ : HasDerivWithinAt
      (fun s => G.metric s (U s))
      ((-2 • G.ricci t) (U t) + G.metric t (A t (U t)))
      (Icc a b) t :=
    @HasDerivWithinAt.clm_apply ℝ _ V _ _ t (Icc a b) (V →L[ℝ] ℝ) _ _
      G.metric (-2 • G.ricci t) U (A t (U t)) hmetric hU
  have h₂ : HasDerivWithinAt
      (fun s => G.metric s (U s) (W s))
      (((-2 • G.ricci t) (U t) + G.metric t (A t (U t))) (W t) +
        G.metric t (U t) (A t (W t)))
      (Icc a b) t :=
    @HasDerivWithinAt.clm_apply ℝ _ V _ _ t (Icc a b) ℝ _ _
      (fun s => G.metric s (U s))
      ((-2 • G.ricci t) (U t) + G.metric t (A t (U t))) W
      (A t (W t)) h₁ hW
  apply h₂.congr_deriv
  simp only [U, W, smul_apply, add_apply]
  rw [hleft t ht, hright t ht]
  ring


theorem transport_pairing_eq_left {J : Set ℝ} (G : EvolvingMetricData (V := V) J)
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn A (Icc a b)) {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (hleft : ∀ t ∈ Icc a b, ∀ v w, G.metric t (A t v) w = G.ricci t v w)
    (hright : ∀ t ∈ Icc a b, ∀ v w, G.metric t v (A t w) = G.ricci t v w)
    (v w : V) {t : ℝ} (ht : t ∈ Icc a b) :
    G.metric t (transportCurveOn (V := V) A hab.le hcont hK t v)
      (transportCurveOn (V := V) A hab.le hcont hK t w) = G.metric a v w := by
  let f : ℝ → ℝ := fun s => G.metric s
    (transportCurveOn (V := V) A hab.le hcont hK s v)
    (transportCurveOn (V := V) A hab.le hcont hK s w)
  have hdiff : DifferentiableOn ℝ f (Icc a b) := by
    intro s hs
    exact (pairing_deriv_zero G A hab.le hcont hK hleft hright v w hs).differentiableWithinAt
  have hderiv : ∀ s ∈ Ico a b, derivWithin f (Icc a b) s = 0 := by
    intro s hs
    exact (pairing_deriv_zero G A hab.le hcont hK hleft hright v w
      ⟨hs.1, hs.2.le⟩).derivWithin ((uniqueDiffOn_Icc hab) s ⟨hs.1, hs.2.le⟩)
  have hc := constant_of_derivWithin_zero hdiff hderiv t ht
  have hva : transportCurveOn (V := V) A hab.le hcont hK a v = v := by
    rw [transportCurveOn_apply_of_mem A hab.le hcont hK ⟨le_rfl, hab.le⟩]
    exact Poincare.ODE.Linear.solOf_left hab.le hcont hK v
  have hwa : transportCurveOn (V := V) A hab.le hcont hK a w = w := by
    rw [transportCurveOn_apply_of_mem A hab.le hcont hK ⟨le_rfl, hab.le⟩]
    exact Poincare.ODE.Linear.solOf_left hab.le hcont hK w
  simpa [f, hva, hwa] using hc


theorem transport_isometry_on {J : Set ℝ} (G : EvolvingMetricData (V := V) J)
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn A (Icc a b)) {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (hleft : ∀ t ∈ Icc a b, ∀ v w, G.metric t (A t v) w = G.ricci t v w)
    (hright : ∀ t ∈ Icc a b, ∀ v w, G.metric t v (A t w) = G.ricci t v w)
    (t : Icc a b) (v w : V) :
    G.metric t (transportCurveOn (V := V) A hab.le hcont hK t v)
      (transportCurveOn (V := V) A hab.le hcont hK t w) = G.metric a v w :=
  transport_pairing_eq_left G A hab hcont hK hleft hright v w t.2


theorem transport_injective_of_nondegenerate {J : Set ℝ}
    (G : EvolvingMetricData (V := V) J) (A : ℝ → V →L[ℝ] V)
    {a b : ℝ} (hab : a < b) (hcont : ContinuousOn A (Icc a b)) {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (hleft : ∀ t ∈ Icc a b, ∀ v w, G.metric t (A t v) w = G.ricci t v w)
    (hright : ∀ t ∈ Icc a b, ∀ v w, G.metric t v (A t w) = G.ricci t v w)
    (hnd : ∀ v, G.metric a v v = 0 → v = 0) (t : Icc a b) :
    Function.Injective (transportCurveOn (V := V) A hab.le hcont hK t) := by
  intro v w hvw
  have hz := transport_isometry_on G A hab hcont hK hleft hright t (v - w) (v - w)
  have hzero : transportCurveOn (V := V) A hab.le hcont hK t (v - w) = 0 := by
    calc
      transportCurveOn (V := V) A hab.le hcont hK t (v - w) =
          transportCurveOn (V := V) A hab.le hcont hK t v -
            transportCurveOn (V := V) A hab.le hcont hK t w := by rw [map_sub]
      _ = 0 := sub_eq_zero.mpr hvw
  have hz' := hz
  rw [hzero] at hz'
  exact sub_eq_zero.mp (hnd (v - w) (by simpa using hz'.symm))

end PoincareConjecture.RicciFlow.Frame

end
