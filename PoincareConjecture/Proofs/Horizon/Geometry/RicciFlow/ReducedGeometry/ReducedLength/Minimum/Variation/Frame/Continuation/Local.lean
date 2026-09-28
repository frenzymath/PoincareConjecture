import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.Field







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

theorem exists_adapted_field_in_chart {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) (γ : ℝ → M) {a b s₀ : ℝ} (hs₀ : s₀ ∈ Ioo a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ (Ioo a b))
    (hchart : ∀ s ∈ Ioo a b, γ s ∈ (chartAt E x).source)
    (htime : ∀ s ∈ Ioo a b, s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (v₀ : TangentSpace (𝓡 n) (γ s₀)) :
    ∃ P : ∀ s, TangentSpace (𝓡 n) (γ s),
      P s₀ = v₀ ∧ IsAdaptedFieldOn F T γ P (Ioo a b) := by
  let y : ℝ → E := fun s ↦ extChartAt (𝓡 n) x (γ s)
  have hy : ContDiffOn ℝ ∞ y (Ioo a b) := by
    apply ContMDiffOn.contDiffOn
    exact (contMDiffOn_extChartAt (I := 𝓡 n) (x := x)).comp hγ (fun s hs ↦ by
      simpa only [extChartAt_source, mem_preimage] using hchart s hs)
  have hgraph (s : ℝ) (hs : s ∈ Ioo a b) : (s, y s) ∈ chartActionDomain F T x :=
    ⟨htime s hs, (extChartAt (𝓡 n) x).map_source (by
      simpa only [extChartAt_source] using hchart s hs)⟩
  let e := trivializationAt E (TangentSpace (𝓡 n)) x
  let w₀ := e.continuousLinearMapAt ℝ (γ s₀) v₀
  obtain ⟨v, hv, hv₀, hd, _⟩ := exists_smooth_coordinate_transport
    (chartActionMetric F T x) (chartActionDomain F T x)
    (chartActionDomain_open F T x) (chartActionMetric_contDiffOn F T x)
    (fun z hz ↦ chartActionMetric_pos F T x hz)
    (fun z hz ↦ chartActionMetric_symm F T x hz) y hs₀ hy hgraph (fun _ : Unit ↦ w₀)
  let P : ∀ s, TangentSpace (𝓡 n) (γ s) := fun s ↦ chartFrame x (v () s) (γ s)
  have hP := chartFrame_curve_contMDiffOn x γ (v ()) (Ioo a b) hγ (hv ()) hchart
  let H : ParametricAlongCurveExtensionOn (Ioo a b) γ P :=
    chartSectionExtension isOpen_Ioo Subset.rfl x γ (v ()) (hv ())
      (fun s hs ↦ hchart s hs) P (fun _ _ ↦ rfl)
  refine ⟨P, ?_, hP, ?_⟩
  · change chartFrame x (v () s₀) (γ s₀) = v₀
    rw [hv₀ ()]
    exact e.symmL_continuousLinearMapAt (hchart s₀ hs₀) v₀
  · intro s hs
    have hγs := ((hγ s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)).mdifferentiableAt (by simp)
    apply localAdaptedEquation_of_pullback F T γ P H isOpen_Ioo hγ hP
      hs hs (isOpen_Ioo.uniqueDiffOn s hs) (htime s hs)
    intro Z
    rw [pullbackCovariantDerivative_chart_formula F (fun r ↦ T - r ^ 2)
      isOpen_Ioo Subset.rfl x γ (v ()) (hv ()) (fun s hs ↦ hchart s hs) P
      (fun _ _ ↦ rfl) H hs (isOpen_Ioo.uniqueDiffOn s hs) hγs, (hd () s hs).deriv]
    exact chartTransportOperator_adapted_pairing_squareDomain F T s x (γ s)
      (hchart s hs) (htime s hs) (deriv y s) (v () s) Z

theorem exists_uniform_local_isAdaptedFieldOn {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
    (htime : ∀ s ∈ U, s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ U) (s₀ : ℝ) (hs₀ : s₀ ∈ U) :
    ∃ (W : Set ℝ) (d : ℝ), IsOpen W ∧ s₀ ∈ W ∧ W ⊆ U ∧ 0 < d ∧
      ∀ t₀ ∈ W, ∀ v₀ : TangentSpace (𝓡 n) (γ t₀),
        ∃ P : ∀ s, TangentSpace (𝓡 n) (γ s),
          Ioo (t₀ - d) (t₀ + d) ⊆ U ∧ P t₀ = v₀ ∧
            IsAdaptedFieldOn F T γ P (Ioo (t₀ - d) (t₀ + d)) := by
  let x := γ s₀
  let D := U ∩ γ ⁻¹' (chartAt E x).source
  have hD : IsOpen D := hγ.continuousOn.isOpen_inter_preimage hU (chartAt E x).open_source
  have hsD : s₀ ∈ D := ⟨hs₀, mem_chart_source E x⟩
  obtain ⟨l, r, hlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hD.mem_nhds hsD)
  let d := min (s₀ - l) (r - s₀) / 4
  have hd : 0 < d := div_pos (lt_min (sub_pos.mpr hlr.1) (sub_pos.mpr hlr.2)) (by norm_num)
  have hleft : 4 * d ≤ s₀ - l := by
    dsimp only [d]
    linarith only [min_le_left (s₀ - l) (r - s₀)]
  have hright : 4 * d ≤ r - s₀ := by
    dsimp only [d]
    linarith only [min_le_right (s₀ - l) (r - s₀)]
  let W := Ioo (s₀ - d) (s₀ + d)
  have hWD : W ⊆ D := by
    intro t ht
    apply hsub
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨W, d, isOpen_Ioo, ⟨by linarith, by linarith⟩,
    hWD.trans inter_subset_left, hd, ?_⟩
  intro t₀ ht₀ v₀
  have hID : Ioo (t₀ - d) (t₀ + d) ⊆ D := by
    intro t ht
    apply hsub
    constructor <;> linarith [ht₀.1, ht₀.2, ht.1, ht.2]
  have hIU : Ioo (t₀ - d) (t₀ + d) ⊆ U := hID.trans inter_subset_left
  obtain ⟨P, hP₀, hP⟩ := exists_adapted_field_in_chart F T x γ
    (show t₀ ∈ Ioo (t₀ - d) (t₀ + d) from ⟨by linarith, by linarith⟩)
    (hγ.mono hIU) (fun _ ht ↦ (hID ht).2) (fun _ ht ↦ htime _ (hIU ht)) v₀
  exact ⟨P, hIU, hP₀, hP⟩

end PoincareConjecture.ReducedLengthMinimum.Variation.Frame
