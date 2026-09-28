import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerBubbleLimitHarmonic



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60


theorem suAnnularReflection_involutive : Function.Involutive suAnnularReflection := by
  intro p
  apply Subtype.ext
  exact (ℝ ∙ m60SpherePole.val)ᗮ.reflection_reflection p.val


theorem suSphereParameter_zero : m60SphereParameter 0 = -m60SpherePole := by
  let : Fact (Module.finrank ℝ LoopAmbient = 2 + 1) := ⟨by simp [LoopAmbient]⟩
  apply Subtype.ext
  simp [m60SphereParameter, m60SphereChart, stereographic'_symm_apply]


theorem suAnnularReflection_pole : suAnnularReflection m60SpherePole = -m60SpherePole := by
  apply Subtype.ext
  exact Submodule.reflection_orthogonalComplement_singleton_eq_neg _

private theorem parameter_ne_pole (z : LoopPlane) : m60SphereParameter z ≠ m60SpherePole := by
  have h : m60SphereParameter z ∈ m60SphereChart.source :=
    m60SphereChart.map_target (by simp [m60SphereChart])
  simpa only [m60SphereChart, stereographic'_source, mem_compl_iff, mem_singleton_iff] using h


def suSphereFromPlane {M : Type u} (f : LoopPlane → M) (p : M) : UnitTwoSphere → M :=
  fun x => if x = m60SpherePole then p else f (m60SphereChart x)


theorem suSphereFromPlane_parameter {M : Type u} (f : LoopPlane → M) (p : M) :
    suSphereFromPlane f p ∘ m60SphereParameter = f := by
  funext z
  simp only [Function.comp_apply, suSphereFromPlane, if_neg (parameter_ne_pole z)]
  exact congrArg f (m60SphereChart.right_inv (by simp [m60SphereChart]))



theorem suSphereFromPlane_inverted {M : Type u} (f : LoopPlane → M) (p : M) :
    suSphereFromPlane f p ∘ (suAnnularReflection ∘ m60SphereParameter) =
      Function.update (f ∘ suBubbleInversion) 0 p := by
  funext z
  by_cases hz : z = 0
  · subst z
    have hzero : suAnnularReflection (m60SphereParameter 0) = m60SpherePole := by
      rw [suSphereParameter_zero, ← suAnnularReflection_pole]
      exact suAnnularReflection_involutive _
    simp [Function.comp_apply, hzero, suSphereFromPlane]
  · have hreflection : suAnnularReflection (m60SphereParameter z) =
        m60SphereParameter (suBubbleInversion z) := by
      have hi : suBubbleInversion z = (4 / ‖z‖ ^ 2) • z := by
        norm_num [suBubbleInversion, EuclideanGeometry.inversion, div_pow]
      rw [hi]
      exact suAnnularReflection_parameter hz
    rw [Function.comp_apply, Function.comp_apply, hreflection,
      Function.update_of_ne hz]
    exact congrFun (suSphereFromPlane_parameter f p) (suBubbleInversion z)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in



theorem suSphereFromPlane_smooth (f : LoopPlane → M) (p : M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hzero : ContMDiffAt (𝓡 2) (𝓡 n) ∞
      (Function.update (f ∘ suBubbleInversion) 0 p) 0) :
    ContMDiff (𝓡 2) (𝓡 n) ∞ (suSphereFromPlane f p) := by
  have hchart {x : UnitTwoSphere} (hx : x ∈ m60SphereChart.source) :
      ContMDiffAt (𝓡 2) (𝓡 2) ∞ m60SphereChart x := by
    have hh : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m60SphereChart m60SphereChart.source := by
      rw [m60SphereChart_eq_chartAt]
      exact contMDiffOn_chart
    exact hh.contMDiffAt (m60SphereChart.open_source.mem_nhds hx)
  intro x
  by_cases hx : x = m60SpherePole
  · subst x
    let Q := m60SphereChart ∘ suAnnularReflection
    have hQ0 : Q m60SpherePole = 0 := by
      change m60SphereChart (suAnnularReflection m60SpherePole) = 0
      rw [suAnnularReflection_pole, ← suSphereParameter_zero]
      exact m60SphereChart.right_inv (by simp [m60SphereChart])
    have hsource : suAnnularReflection m60SpherePole ∈ m60SphereChart.source := by
      rw [suAnnularReflection_pole, ← suSphereParameter_zero]
      exact m60SphereChart.symm.map_source (by simp [m60SphereChart])
    have hQ : ContMDiffAt (𝓡 2) (𝓡 2) ∞ Q m60SpherePole :=
      (hchart hsource).comp _ (suAnnularReflection_smooth _)
    have hzQ : ContMDiffAt (𝓡 2) (𝓡 n) ∞
        (Function.update (f ∘ suBubbleInversion) 0 p) (Q m60SpherePole) := by
      rwa [hQ0]
    have h := hzQ.comp m60SpherePole hQ
    apply h.congr_of_eventuallyEq
    filter_upwards [suAnnularReflection_smooth.continuous.continuousAt
      (m60SphereChart.open_source.mem_nhds hsource)] with x hxs
    change suSphereFromPlane f p x = Function.update (f ∘ suBubbleInversion) 0 p (Q x)
    rw [← congrFun (suSphereFromPlane_inverted f p) (Q x)]
    change suSphereFromPlane f p x =
      suSphereFromPlane f p (suAnnularReflection (m60SphereParameter (Q x)))
    have hi : m60SphereParameter (Q x) = suAnnularReflection x :=
      m60SphereChart.left_inv hxs
    rw [hi, suAnnularReflection_involutive]
  · have hxs : x ∈ m60SphereChart.source := by simpa [m60SphereChart] using hx
    apply ((hf _).comp x (hchart hxs)).congr_of_eventuallyEq
    filter_upwards [m60SphereChart.open_source.mem_nhds hxs] with y hy
    have hyp : y ≠ m60SpherePole := by simpa [m60SphereChart] using hy
    simp only [suSphereFromPlane, if_neg hyp, Function.comp_apply]


theorem suSphereFromPlane_energy (g : RiemannianMetric n M) (f : LoopPlane → M) (p : M) :
    m60SphereEnergy g (suSphereFromPlane f p) = ∫ z, m60EnergyDensity g f z := by
  simp only [m60SphereEnergy, m60SphereEnergyDensity, suSphereFromPlane_parameter]



theorem suSphereFromPlane_harmonic (g : RiemannianMetric n M) (f : LoopPlane → M) (p : M)
    (hh : SUPlaneHarmonic g f) : M60SphereChartHarmonic g (suSphereFromPlane f p) := by
  intro q z hz
  have hv := congrFun (suSphereFromPlane_parameter f p) z
  change suSphereFromPlane f p (m60SphereParameter z) = f z at hv
  rw [hv] at hz
  have h := hh q z hz
  simpa only [suSphereFromPlane_parameter, Fin.sum_univ_two] using h

end PoincareConjecture.M60
