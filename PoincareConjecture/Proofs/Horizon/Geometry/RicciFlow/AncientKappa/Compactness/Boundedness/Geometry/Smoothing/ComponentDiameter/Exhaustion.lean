import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.Smoothing.ComponentDiameter.Components
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.Smoothing.RegularBand








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

open Poincare.Riemannian.Soul
open Poincare.Geometry.Riemannian.ScalarOperators.Gradient.Flow

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [NoncompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

omit [NoncompactSpace M] in


theorem exists_uniform_exhaustion_level_component_diameter_with_error
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (p : M) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    letI := g.toMetricSpace
    let f := busemannExhaustion p
    let U := {x | a / 2 < f x ∧ f x < b + 1 / 2}
    ∃ d : ℝ, 0 < d ∧ ∀ u : M → ℝ,
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u →
      (∀ x ∈ U, mfderiv (𝓡 3) 𝓘(ℝ, ℝ) u x ≠ 0) →
      (∀ x ∈ horoballIntersection p (b + 1), 0 < f x →
        |u x - f x| ≤ min (a/8) (1/8)) →
      ∀ c ∈ Icc a b, ∀ x ∈ {x | x ∈ U ∧ u x = c},
        ∃ y ∈ connectedComponentIn {x | x ∈ U ∧ u x = c} x,
        ∃ z ∈ connectedComponentIn {x | x ∈ U ∧ u x = c} x,
          d ≤ dist y z := by
  let := g.toMetricSpace
  let f := busemannExhaustion p
  let U := {x | a / 2 < f x ∧ f x < b + 1 / 2}
  let C := horoballIntersection p (b + 1)
  let K := C ∩ f ⁻¹' Icc (3*a/4) (b+1/4)
  have hf : Continuous f := (lipschitz_busemannExhaustion p).continuous
  have hU : IsOpen U := (isOpen_lt continuous_const hf).inter (isOpen_lt hf continuous_const)
  have hdist (x y : M) : dist x y = (g.edist x y).toReal := rfl
  have hC : IsCompact C :=
    g.isCompact_horoballIntersection_of_nonnegativeSectional D hc hsec hdist p (by linarith)
  have hK : IsCompact K := hC.inter_right (isClosed_Icc.preimage hf)
  have hKU : K ⊆ U := by
    intro x hx
    exact ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
  have hUC : U ⊆ C := by
    intro x hx
    apply (busemannExhaustion_le_iff (by linarith : 0 ≤ b + 1)).mp
    linarith [hx.2]
  obtain ⟨d, hd, hbound⟩ :=
    AncientCompactness.exists_uniform_regular_level_component_diameter D hK hU hKU
  let ε₀ := min (a/8) (1/8)
  have hεa : ε₀ ≤ a/8 := min_le_left _ _
  have hεone : ε₀ ≤ 1/8 := min_le_right _ _
  refine ⟨d, hd, ?_⟩
  intro u hu hreg herror c hc
  have hSK : {x | x ∈ U ∧ u x = c} ⊆ K := by
    intro x hx
    have hxC := hUC hx.1
    have he := abs_le.mp (herror x hxC (by linarith [hx.1.1]))
    rw [hx.2] at he
    exact ⟨hxC, by linarith [hc.1, he.2], by linarith [hc.2, he.1]⟩
  have hS : IsCompact {x | x ∈ U ∧ u x = c} := by
    have heq : {x | x ∈ U ∧ u x = c} = K ∩ u ⁻¹' {c} := by
      ext x
      exact ⟨fun hx => ⟨hSK hx, hx.2⟩, fun hx => ⟨hKU hx.1, hx.2⟩⟩
    rw [heq]
    exact hK.inter_right (isClosed_singleton.preimage hu.continuous)
  exact hbound u hu hreg c hS hSK

omit [NoncompactSpace M] in


theorem exists_uniform_exhaustion_level_component_diameter
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (p : M) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    letI := g.toMetricSpace
    let f := busemannExhaustion p
    let U := {x | a / 2 < f x ∧ f x < b + 1 / 2}
    ∃ d ε₀ : ℝ, 0 < d ∧ 0 < ε₀ ∧ ∀ u : M → ℝ,
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u →
      (∀ x ∈ U, mfderiv (𝓡 3) 𝓘(ℝ, ℝ) u x ≠ 0) →
      (∀ x ∈ horoballIntersection p (b + 1), 0 < f x → |u x - f x| ≤ ε₀) →
      ∀ c ∈ Icc a b, ∀ x ∈ {x | x ∈ U ∧ u x = c},
        ∃ y ∈ connectedComponentIn {x | x ∈ U ∧ u x = c} x,
        ∃ z ∈ connectedComponentIn {x | x ∈ U ∧ u x = c} x,
          d ≤ dist y z := by
  let := g.toMetricSpace
  obtain ⟨d, hd, hbound⟩ :=
    g.exists_uniform_exhaustion_level_component_diameter_with_error D hc hsec p ha hab
  exact ⟨d, min (a/8) (1/8), hd, lt_min (by positivity) (by norm_num), hbound⟩

omit [NoncompactSpace M] in


theorem exists_uniform_exhaustion_low_level_component_diameter
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    let f := busemannExhaustion p
    ∃ d : ℝ, 0 < d ∧ ∀ b : ℝ, 1 ≤ b → ∀ u : M → ℝ,
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u →
      (∀ x ∈ {x | 1/2 < f x ∧ f x < b+1/2},
        mfderiv (𝓡 3) 𝓘(ℝ, ℝ) u x ≠ 0) →
      (∀ x ∈ horoballIntersection p (b+1), 0 < f x → |u x-f x| ≤ 1/8) →
      ∀ x ∈ {x | (1/2 < f x ∧ f x < b+1/2) ∧ u x = 1},
        ∃ y ∈ connectedComponentIn {x | (1/2 < f x ∧ f x < b+1/2) ∧ u x = 1} x,
        ∃ z ∈ connectedComponentIn {x | (1/2 < f x ∧ f x < b+1/2) ∧ u x = 1} x,
          d ≤ dist y z := by
  let := g.toMetricSpace
  let f := busemannExhaustion p
  let O := {x | (1:ℝ)/2 < f x ∧ f x < 1+1/2}
  obtain ⟨d, hd, hbound⟩ :=
    g.exists_uniform_exhaustion_level_component_diameter_with_error D hc hsec p
      (a := 1) (b := 1) zero_lt_one le_rfl
  refine ⟨d, hd, ?_⟩
  intro b hb u hu hreg herror
  have hregO (x : M) (hx : x ∈ O) : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) u x ≠ 0 :=
    hreg x ⟨hx.1, by linarith [hx.2]⟩
  have herrorO (x : M) (hx : x ∈ horoballIntersection p (1+1)) (hpos : 0 < f x) :
      |u x-f x| ≤ min (1/8) (1/8) := by
    rw [min_self]
    apply herror x ?_ hpos
    apply (busemannExhaustion_le_iff (by linarith : 0 ≤ b+1)).mp
    have hxle : f x ≤ 1+1 :=
      (busemannExhaustion_le_iff (by norm_num : 0 ≤ (1:ℝ)+1)).mpr hx
    linarith
  have hsets : {x | (1/2 < f x ∧ f x < b+1/2) ∧ u x = 1} =
      {x | x ∈ O ∧ u x = 1} := by
    ext x
    constructor
    · intro hx
      have hxC : x ∈ horoballIntersection p (b+1) := by
        apply (busemannExhaustion_le_iff (by linarith : 0 ≤ b+1)).mp
        linarith [hx.1.2]
      have hh := abs_le.mp (herror x hxC (by linarith [hx.1.1]))
      rw [hx.2] at hh
      exact ⟨⟨hx.1.1, by linarith [hh.1]⟩, hx.2⟩
    · intro hx
      exact ⟨⟨hx.1.1, by linarith [hx.1.2]⟩, hx.2⟩
  rw [hsets]
  exact hbound u hu hregO herrorO 1 ⟨le_rfl, le_rfl⟩




theorem exists_smooth_exhaustion_approx_with_regular_component_diameters
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (p : M) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    letI := g.toMetricSpace
    let f := busemannExhaustion p
    let U := {x | a / 2 < f x ∧ f x < b + 1 / 2}
    ∃ l d : ℝ, 0 < l ∧ 0 < d ∧ IsOpen U ∧
      ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ u : M → ℝ,
        ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u ∧ u p ≤ ε ∧
        (∀ x ∈ horoballIntersection p (b + 1), u x ≤ f x + ε) ∧
        (∀ x ∈ horoballIntersection p (b + 1), 0 < f x → |u x - f x| ≤ ε) ∧
        (∀ x ∈ horoballIntersection p (b + 1),
          g.tangentNorm x (D.gradient u x) ≤ 1 + η) ∧
        (∀ x ∈ horoballIntersection p (b + 1), ∀ v : TangentSpace (𝓡 3) x,
          -η * g.inner x v v ≤ D.hessian u x v v) ∧
        (∀ x ∈ U, l ≤ g.tangentNorm x (D.gradient u x)) ∧
        IsCompact {x | x ∈ U ∧ u x ∈ Icc a b} ∧
        ∀ c ∈ Icc a b, ∀ x ∈ {x | x ∈ U ∧ u x = c},
          ∃ y ∈ connectedComponentIn {x | x ∈ U ∧ u x = c} x,
          ∃ z ∈ connectedComponentIn {x | x ∈ U ∧ u x = c} x,
            d ≤ dist y z := by
  let := g.toMetricSpace
  let f := busemannExhaustion p
  let U := {x | a / 2 < f x ∧ f x < b + 1 / 2}
  obtain ⟨d, ε₀, hd, hε₀, hdiam⟩ :=
    g.exists_uniform_exhaustion_level_component_diameter D hc hsec p ha hab
  obtain ⟨l, hl, hU, hsmooth⟩ :=
    g.exists_smooth_exhaustion_approx_with_regular_band_controls D hc hsec p ha hab
  refine ⟨l, d, hl, hd, hU, ?_⟩
  intro ε η hε hη
  obtain ⟨u, hu, hup, hupper, herror, hgradupper, hhess, hgrad, hband⟩ :=
    hsmooth (min ε ε₀) η (lt_min hε hε₀) hη
  have hreg (x : M) (hx : x ∈ U) : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) u x ≠ 0 := by
    intro hz
    have hg := (gradient_eq_zero_iff_mfderiv_eq_zero_manifold D u x).mpr hz
    have hh := hgrad x hx
    simp only [hg, tangentNorm, map_zero, Real.sqrt_zero] at hh
    exact (not_le_of_gt hl) hh
  refine ⟨u, hu, hup.trans (min_le_left _ _), ?_, ?_, hgradupper, hhess, hgrad, hband, ?_⟩
  · intro x hx
    exact (hupper x hx).trans (add_le_add_right (min_le_left _ _) _)
  · intro x hx hpos
    exact (herror x hx hpos).trans (min_le_left _ _)
  · exact hdiam u hu hreg (fun x hx hpos => (herror x hx hpos).trans (min_le_right _ _))

end PoincareConjecture.RiemannianMetric
