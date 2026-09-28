import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.Local
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Pullback.Chart












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

noncomputable section

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Frame

open PoincareConjecture.ReducedLengthMinimum.Variational
open PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

def fieldChartCoordinates (x : M) (γ : ℝ → M)
    (P : ∀ s, TangentSpace (𝓡 n) (γ s)) (s : ℝ) : E :=
  (trivializationAt E (TangentSpace (𝓡 n)) x).continuousLinearMapAt ℝ (γ s) (P s)

theorem fieldChartCoordinates_smooth (x : M) (γ : ℝ → M)
    (P : ∀ s, TangentSpace (𝓡 n) (γ s)) (U : Set ℝ)
    (hP : ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' E (γ s) (P s)) U)
    (hchart : ∀ s ∈ U, γ s ∈ (chartAt E x).source) :
    ContDiffOn ℝ ∞ (fieldChartCoordinates x γ P) U := by
  let e := trivializationAt E (TangentSpace (𝓡 n)) x
  have hpair := e.contMDiffOn.comp hP (fun s hs ↦ e.mem_source.mpr (hchart s hs))
  have hcoord : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞
      (fun s ↦ (e (Bundle.TotalSpace.mk' E (γ s) (P s))).2) U :=
    fun s hs ↦ (hpair s hs).snd
  apply hcoord.contDiffOn.congr
  intro s hs
  exact Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
    (R := ℝ) e (hchart s hs) (P s)

theorem chartFrame_fieldChartCoordinates (x : M) (γ : ℝ → M)
    (P : ∀ s, TangentSpace (𝓡 n) (γ s)) {s : ℝ}
    (hchart : γ s ∈ (chartAt E x).source) :
    chartFrame x (fieldChartCoordinates x γ P s) (γ s) = P s :=
  (trivializationAt E (TangentSpace (𝓡 n)) x).symmL_continuousLinearMapAt hchart (P s)

def LocalAdaptedEquation {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (P : ∀ s, TangentSpace (𝓡 n) (γ s)) (s : ℝ) : Prop :=
  ∀ x : M, γ s ∈ (chartAt E x).source →
    HasDerivAt (fieldChartCoordinates x γ P)
      (chartTransportOperator (chartActionMetric F T x)
        (s, extChartAt (𝓡 n) x (γ s)) (deriv ((extChartAt (𝓡 n) x) ∘ γ) s)
          (fieldChartCoordinates x γ P s)) s

structure IsAdaptedFieldOn {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (P : ∀ s, TangentSpace (𝓡 n) (γ s)) (U : Set ℝ) : Prop where
  smooth : ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) ∞
    (fun s ↦ Bundle.TotalSpace.mk' E (γ s) (P s)) U
  equation : ∀ s ∈ U, LocalAdaptedEquation F T γ P s

set_option maxHeartbeats 800000 in
theorem localAdaptedEquation_of_pullback {J C U : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (γ : ℝ → M)
    (P : ∀ s, TangentSpace (𝓡 n) (γ s))
    (H : ParametricAlongCurveExtensionOn C γ P) (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ U)
    (hP : ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' E (γ s) (P s)) U)
    {s : ℝ} (hs : s ∈ C) (hsU : s ∈ U) (hC : UniqueDiffWithinAt ℝ C s)
    (htime : s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (heq : ∀ Z : TangentSpace (𝓡 n) (γ s),
      (F.metric (T - s ^ 2)).inner (γ s)
          (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ P C H s) Z =
        -(2 * s) * (F.connection (T - s ^ 2)).ricci (γ s) (P s) Z) :
    LocalAdaptedEquation F T γ P s := by
  intro x hx
  let V := U ∩ γ ⁻¹' (chartAt E x).source
  have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU (chartAt E x).open_source
  have hsV : s ∈ V := ⟨hsU, hx⟩
  let v := fieldChartCoordinates x γ P
  have hv : ContDiffOn ℝ ∞ v V :=
    fieldChartCoordinates_smooth x γ P V (hP.mono inter_subset_left) (fun _ ht ↦ ht.2)
  have hrep (r : ℝ) (hr : r ∈ V) : chartFrame x (v r) (γ r) = P r :=
    chartFrame_fieldChartCoordinates x γ P hr.2
  have hγs := ((hγ s hsU).contMDiffAt (hU.mem_nhds hsU)).mdifferentiableAt (by simp)
  have hpull := pullbackCovariantDerivative_chart_formula_local F (fun r ↦ T - r ^ 2)
    hV x γ v hv (fun _ hr ↦ hr.2.2) P (fun r hr ↦ hrep r hr.2) H hs hsV hC hγs
  let B := chartTransportOperator (chartActionMetric F T x)
    (s, extChartAt (𝓡 n) x (γ s)) (deriv ((extChartAt (𝓡 n) x) ∘ γ) s) (v s)
  have href (Z : TangentSpace (𝓡 n) (γ s)) :=
    chartTransportOperator_adapted_pairing_squareDomain F T s x (γ s) hx htime
      (deriv ((extChartAt (𝓡 n) x) ∘ γ) s) (v s) Z
  have hz (Z : TangentSpace (𝓡 n) (γ s)) :
      (F.metric (T - s ^ 2)).inner (γ s) (chartFrame x (deriv v s - B) (γ s)) Z = 0 := by
    have h₁ := heq Z
    rw [hpull] at h₁
    have h₂ := href Z
    rw [hrep s hsV] at h₂
    change (F.metric (T - s ^ 2)).inner (γ s)
      (chartFrame x B (γ s) + _) Z = _ at h₂
    simp only [map_add, add_apply] at h₁ h₂
    change (F.metric (T - s ^ 2)).inner (γ s)
      ((trivializationAt E (TangentSpace (𝓡 n)) x).symmL ℝ (γ s) (deriv v s - B)) Z = 0
    simp only [map_sub, sub_apply]
    change (F.metric (T - s ^ 2)).inner (γ s) (chartFrame x (deriv v s) (γ s)) Z -
      (F.metric (T - s ^ 2)).inner (γ s) (chartFrame x B (γ s)) Z = 0
    linarith only [h₁, h₂]
  have hzero : chartFrame x (deriv v s - B) (γ s) = 0 := by
    by_contra hne
    exact (ne_of_gt ((F.metric (T - s ^ 2)).pos (γ s) _ hne))
      (hz (chartFrame x (deriv v s - B) (γ s)))
  have hd : deriv v s = B := by
    let e := trivializationAt E (TangentSpace (𝓡 n)) x
    have h := congrArg (e.continuousLinearMapAt ℝ (γ s)) hzero
    change e.continuousLinearMapAt ℝ (γ s) (e.symmL ℝ (γ s) (deriv v s - B)) = _ at h
    rw [e.continuousLinearMapAt_symmL hx, map_zero] at h
    exact sub_eq_zero.mp h
  exact ((hv s hsV).contDiffAt (hV.mem_nhds hsV)).differentiableAt (by simp)
    |>.hasDerivAt.congr_deriv hd

theorem pullback_adapted_of_localAdaptedEquation {J C U : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (γ : ℝ → M)
    (P : ∀ s, TangentSpace (𝓡 n) (γ s))
    (H : ParametricAlongCurveExtensionOn C γ P) (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ U)
    (hP : ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' E (γ s) (P s)) U)
    {s : ℝ} (hs : s ∈ C) (hsU : s ∈ U) (hC : UniqueDiffWithinAt ℝ C s)
    (htime : s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (heq : LocalAdaptedEquation F T γ P s) (Z : TangentSpace (𝓡 n) (γ s)) :
    (F.metric (T - s ^ 2)).inner (γ s)
        (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ P C H s) Z =
      -(2 * s) * (F.connection (T - s ^ 2)).ricci (γ s) (P s) Z := by
  let x := γ s
  let V := U ∩ γ ⁻¹' (chartAt E x).source
  have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU (chartAt E x).open_source
  have hsV : s ∈ V := ⟨hsU, mem_chart_source E x⟩
  let v := fieldChartCoordinates x γ P
  have hv : ContDiffOn ℝ ∞ v V :=
    fieldChartCoordinates_smooth x γ P V (hP.mono inter_subset_left) (fun _ ht ↦ ht.2)
  have hrep (r : ℝ) (hr : r ∈ V) : chartFrame x (v r) (γ r) = P r :=
    chartFrame_fieldChartCoordinates x γ P hr.2
  have hγs := ((hγ s hsU).contMDiffAt (hU.mem_nhds hsU)).mdifferentiableAt (by simp)
  rw [pullbackCovariantDerivative_chart_formula_local F (fun r ↦ T - r ^ 2)
    hV x γ v hv (fun _ hr ↦ hr.2.2) P (fun r hr ↦ hrep r hr.2) H hs hsV hC hγs,
    (heq x hsV.2).deriv]
  have h := chartTransportOperator_adapted_pairing_squareDomain F T s x (γ s)
    hsV.2 htime (deriv ((extChartAt (𝓡 n) x) ∘ γ) s) (v s) Z
  rwa [hrep s hsV] at h

theorem LocalAdaptedEquation.congr {J : Set ℝ} {F : RicciFlow n M J} {T s : ℝ}
    {γ : ℝ → M} {P Q : ∀ t, TangentSpace (𝓡 n) (γ t)}
    (h : LocalAdaptedEquation F T γ P s) (heq : ∀ᶠ t in 𝓝 s, P t = Q t) :
    LocalAdaptedEquation F T γ Q s := by
  intro x hx
  have hv : fieldChartCoordinates x γ P =ᶠ[𝓝 s] fieldChartCoordinates x γ Q := by
    filter_upwards [heq] with t ht
    simp only [fieldChartCoordinates, ht]
  have hd := (h x hx).congr_of_eventuallyEq hv.symm
  simpa only [hv.eq_of_nhds] using hd

theorem IsAdaptedFieldOn.mono {J : Set ℝ} {F : RicciFlow n M J} {T : ℝ}
    {γ : ℝ → M} {P : ∀ t, TangentSpace (𝓡 n) (γ t)} {U V : Set ℝ}
    (h : IsAdaptedFieldOn F T γ P U) (hVU : V ⊆ U) :
    IsAdaptedFieldOn F T γ P V :=
  ⟨h.smooth.mono hVU, fun s hs ↦ h.equation s (hVU hs)⟩

theorem IsAdaptedFieldOn.congr {J : Set ℝ} {F : RicciFlow n M J} {T : ℝ}
    {γ : ℝ → M} {P Q : ∀ t, TangentSpace (𝓡 n) (γ t)} {U : Set ℝ}
    (h : IsAdaptedFieldOn F T γ P U) (hU : IsOpen U)
    (heq : ∀ t ∈ U, P t = Q t) : IsAdaptedFieldOn F T γ Q U := by
  refine ⟨h.smooth.congr (fun t ht ↦ ?_), ?_⟩
  · rw [heq t ht]
  · intro s hs
    apply (h.equation s hs).congr
    filter_upwards [hU.mem_nhds hs] with t ht using heq t ht

theorem IsAdaptedFieldOn.of_locally {J : Set ℝ} {F : RicciFlow n M J} {T : ℝ}
    {γ : ℝ → M} {P : ∀ t, TangentSpace (𝓡 n) (γ t)} {U : Set ℝ}
    (h : ∀ s ∈ U, ∃ (Q : ∀ t, TangentSpace (𝓡 n) (γ t)) (V : Set ℝ),
      IsOpen V ∧ s ∈ V ∧ IsAdaptedFieldOn F T γ Q V ∧
        ∀ᶠ t in 𝓝 s, P t = Q t) : IsAdaptedFieldOn F T γ P U := by
  have hp (s : ℝ) (hs : s ∈ U) :
      ContMDiffAt 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) ∞
          (fun t ↦ Bundle.TotalSpace.mk' E (γ t) (P t)) s ∧
        LocalAdaptedEquation F T γ P s := by
    obtain ⟨Q, V, hV, hsV, hQ, heq⟩ := h s hs
    have he : (fun t ↦ Bundle.TotalSpace.mk' E (γ t) (P t)) =ᶠ[𝓝 s]
        (fun t ↦ Bundle.TotalSpace.mk' E (γ t) (Q t)) := by
      filter_upwards [heq] with t ht
      rw [ht]
    exact ⟨((hQ.smooth s hsV).contMDiffAt (hV.mem_nhds hsV)).congr_of_eventuallyEq he,
      (hQ.equation s hsV).congr (heq.mono (fun _ ht ↦ ht.symm))⟩
  exact ⟨fun s hs ↦ (hp s hs).1.contMDiffWithinAt, fun s hs ↦ (hp s hs).2⟩

end PoincareConjecture.ReducedLengthMinimum.Variation.Frame
