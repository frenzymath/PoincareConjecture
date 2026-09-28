import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.Field
import PoincareConjecture.Proofs.Horizon.Analysis.ODE.Uniqueness.Open

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

noncomputable section

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Frame

open PoincareConjecture.ReducedLengthMinimum.Variational
open PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

private theorem linearODE_eventuallyEq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ → E →L[ℝ] E) (f g : ℝ → E) (s : ℝ)
    (hA : ContDiffAt ℝ 1 A s)
    (hf : ∀ᶠ t in 𝓝 s, HasDerivAt f (A t (f t)) t)
    (hg : ∀ᶠ t in 𝓝 s, HasDerivAt g (A t (g t)) t)
    (heq : f s = g s) : f =ᶠ[𝓝 s] g := by
  let V : ℝ × E → ℝ × E := fun z ↦ (1, A z.1 z.2)
  have hV : ContDiffAt ℝ 1 V (s, f s) :=
    contDiffAt_const.prodMk ((hA.comp _ contDiffAt_fst).clm_apply contDiffAt_snd)
  have hf' : ∀ᶠ t in 𝓝 s,
      HasDerivAt (fun r ↦ (r, f r)) (V (t, f t)) t :=
    hf.mono (fun t ht ↦ (hasDerivAt_id t).prodMk ht)
  have hg' : ∀ᶠ t in 𝓝 s,
      HasDerivAt (fun r ↦ (r, g r)) (V (t, g t)) t :=
    hg.mono (fun t ht ↦ (hasDerivAt_id t).prodMk ht)
  have h := Poincare.ODE.eq_nhds_of_hasDerivAt hV hf' hg'
    (congrArg (fun v ↦ (s, v)) heq)
  exact h.mono (fun _ ht ↦ congrArg Prod.snd ht)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem adaptedField_eventuallyEq {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (P Q : ∀ t, TangentSpace (𝓡 n) (γ t))
    (U : Set ℝ) (hU : IsOpen U)
    (htime : ∀ s ∈ U, s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ U)
    (hP : IsAdaptedFieldOn F T γ P U) (hQ : IsAdaptedFieldOn F T γ Q U)
    (s₀ : ℝ) (hs₀ : s₀ ∈ U) (heq : P s₀ = Q s₀) :
    ∀ᶠ t in 𝓝 s₀, P t = Q t := by
  let x := γ s₀
  let D := U ∩ γ ⁻¹' (chartAt E x).source
  have hD : IsOpen D := hγ.continuousOn.isOpen_inter_preimage hU (chartAt E x).open_source
  have hsD : s₀ ∈ D := ⟨hs₀, mem_chart_source E x⟩
  let y : ℝ → E := fun t ↦ extChartAt (𝓡 n) x (γ t)
  have hy : ContDiffOn ℝ ∞ y D := by
    apply ContMDiffOn.contDiffOn
    exact (contMDiffOn_extChartAt (I := 𝓡 n) (x := x)).comp
      (hγ.mono inter_subset_left) (fun s hs ↦ by
        simpa only [extChartAt_source, mem_preimage] using hs.2)
  have hdy : ContDiffOn ℝ ∞ (deriv y) D := hy.deriv_of_isOpen hD (by simp)
  let A : ℝ → E →L[ℝ] E := fun t ↦
    chartTransportOperator (chartActionMetric F T x) (t, y t) (deriv y t)
  have hA : ContDiffOn ℝ ∞ A D :=
    (chartTransportOperator_contDiffOn (chartActionMetric F T x) (chartActionDomain F T x)
      (chartActionDomain_open F T x) (chartActionMetric_contDiffOn F T x)
      (fun z hz ↦ chartActionMetric_pos F T x hz)).comp
      (f := fun t : ℝ ↦ ((t, y t), deriv y t))
      ((contDiffOn_id.prodMk hy).prodMk hdy) (fun t ht ↦
        ⟨⟨htime t ht.1, (extChartAt (𝓡 n) x).map_source (by
          simpa only [extChartAt_source, mem_preimage] using ht.2)⟩, mem_univ _⟩)
  have hv : ∀ᶠ t in 𝓝 s₀, HasDerivAt (fieldChartCoordinates x γ P)
      (A t (fieldChartCoordinates x γ P t)) t := by
    filter_upwards [hD.mem_nhds hsD] with t ht
    exact hP.equation t ht.1 x ht.2
  have hw : ∀ᶠ t in 𝓝 s₀, HasDerivAt (fieldChartCoordinates x γ Q)
      (A t (fieldChartCoordinates x γ Q t)) t := by
    filter_upwards [hD.mem_nhds hsD] with t ht
    exact hQ.equation t ht.1 x ht.2
  have h₀ : fieldChartCoordinates x γ P s₀ = fieldChartCoordinates x γ Q s₀ := by
    simp only [fieldChartCoordinates, heq]
  have hsame := linearODE_eventuallyEq A (fieldChartCoordinates x γ P)
    (fieldChartCoordinates x γ Q) s₀
    (((hA s₀ hsD).contDiffAt (hD.mem_nhds hsD)).of_le (by simp)) hv hw h₀
  filter_upwards [hD.mem_nhds hsD, hsame] with t ht htw
  rw [← chartFrame_fieldChartCoordinates x γ P ht.2, htw,
    chartFrame_fieldChartCoordinates x γ Q ht.2]

theorem adaptedField_eqOn {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (P Q : ∀ t, TangentSpace (𝓡 n) (γ t))
    (U : Set ℝ) (hU : IsOpen U) (hconn : IsPreconnected U)
    (htime : ∀ s ∈ U, s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ U)
    (hP : IsAdaptedFieldOn F T γ P U) (hQ : IsAdaptedFieldOn F T γ Q U)
    (s₀ : ℝ) (hs₀ : s₀ ∈ U) (heq : P s₀ = Q s₀) : ∀ t ∈ U, P t = Q t := by
  let G : Set ℝ := {s | ∀ᶠ t in 𝓝 s, P t = Q t}
  have hopen : IsOpen G := isOpen_setOfPred_eventually_nhds
  have hlocal (t : ℝ) (ht : t ∈ U) (he : P t = Q t) : t ∈ G :=
    adaptedField_eventuallyEq F T γ P Q U hU htime hγ hP hQ t ht he
  have hclosed : closure G ∩ U ⊆ G := by
    intro t ht
    let x := γ t
    let V := U ∩ γ ⁻¹' (chartAt E x).source
    have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU (chartAt E x).open_source
    have htV : t ∈ V := ⟨ht.2, mem_chart_source E x⟩
    have hPc := fieldChartCoordinates_smooth x γ P V (hP.smooth.mono inter_subset_left)
      (fun _ hr ↦ hr.2)
    have hQc := fieldChartCoordinates_smooth x γ Q V (hQ.smooth.mono inter_subset_left)
      (fun _ hr ↦ hr.2)
    have hfreq : ∃ᶠ r in 𝓝 t, fieldChartCoordinates x γ P r =
        fieldChartCoordinates x γ Q r :=
      (mem_closure_iff_frequently.mp ht.1).mono (fun r hr ↦ by
        simp only [fieldChartCoordinates, hr.self_of_nhds])
    have hc := tendsto_nhds_unique_of_frequently_eq
      ((hPc t htV).contDiffAt (hV.mem_nhds htV)).continuousAt
      ((hQc t htV).contDiffAt (hV.mem_nhds htV)).continuousAt hfreq
    apply hlocal t ht.2
    rw [← chartFrame_fieldChartCoordinates x γ P htV.2, hc,
      chartFrame_fieldChartCoordinates x γ Q htV.2]
  have hall := hconn.subset_of_closure_inter_subset hopen ⟨s₀, hs₀, hlocal s₀ hs₀ heq⟩ hclosed
  exact fun t ht ↦ (hall ht).self_of_nhds

end PoincareConjecture.ReducedLengthMinimum.Variation.Frame
