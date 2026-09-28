import PoincareConjecture.Definitions.M64Annulus
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.AreaMeasurability
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.ProjectionPointwise








set_option autoImplicit false

open MeasureTheory Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture




theorem m64AnnulusDomain_ae_eq_boxInterior :
    m64AnnulusDomain =ᵐ[volume]
      (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹' (Set.pi Set.univ
        (fun i : Fin 2 => Set.Ioo ((0 : Fin 2 → ℝ) i)
          (![curvePeriod, 1] i))) := by
  let e : LoopPlane → (Fin 2 → ℝ) := @WithLp.ofLp 2 (Fin 2 → ℝ)
  let lo : Fin 2 → ℝ := 0
  let hi : Fin 2 → ℝ := ![curvePeriod, 1]
  have hbox : (Set.pi Set.univ (fun i : Fin 2 => Set.Ioo (lo i) (hi i))) =ᵐ[
      (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ))]
      Set.pi Set.univ (fun i : Fin 2 => Set.Icc (lo i) (hi i)) :=
    by
      simpa only [pi_univ_Icc] using
        (Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin 2 => (volume : Measure ℝ))
          (f := lo) (g := hi))
  have hpre : e ⁻¹' (Set.pi Set.univ (fun i : Fin 2 => Set.Ioo (lo i) (hi i))) =ᵐ[volume]
      e ⁻¹' (Set.pi Set.univ (fun i : Fin 2 => Set.Icc (lo i) (hi i))) :=
    (PiLp.volume_preserving_ofLp (ι := Fin 2)).quasiMeasurePreserving.preimage_ae_eq hbox
  have hdom : m64AnnulusDomain =
      e ⁻¹' (Set.pi Set.univ (fun i : Fin 2 => Set.Icc (lo i) (hi i))) := by
    ext p
    simp only [m64AnnulusDomain, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, Set.mem_Icc]
    dsimp [e]
    simp only [true_implies]
    change (0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ p 1 ∧ p 1 ≤ 1) ↔
      (∀ i : Fin 2, lo i ≤ p i ∧ p i ≤ hi i)
    constructor
    · intro hp i
      fin_cases i
      · exact ⟨hp.1, hp.2.1⟩
      · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · intro hp
      have h0 := hp 0
      have h1 := hp 1
      simpa [lo, hi] using ⟨h0.1, h0.2, h1.1, h1.2⟩
  rw [hdom]
  simpa only [e, lo, hi] using hpre.symm




theorem m64ProjectedDensity_integrable
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}
    {circumference : ℝ} (P : M62.CircleProductData F circumference)
    (t : ℝ) (c0 c1 : ℝ → P.charts.Point)
    (A : M64Annulus (P.flow.metric t) c0 c1) :
    IntegrableOn
      (m60AreaDensity (F.metric t) (fun z => (A.map z).1))
      m64AnnulusDomain volume := by
  let e : LoopPlane → (Fin 2 → ℝ) := @WithLp.ofLp 2 (Fin 2 → ℝ)
  let lo : Fin 2 → ℝ := 0
  let hi : Fin 2 → ℝ := ![curvePeriod, 1]
  let S : Set LoopPlane := e ⁻¹' (Set.pi Set.univ
    (fun i : Fin 2 => Set.Ioo (lo i) (hi i)))
  have hS : IsOpen S := by
    apply (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)).preimage
    exact PiLp.continuous_ofLp 2 _
  have hSdom : S ⊆ m64AnnulusDomain := by
    intro p hp
    simp only [S, e, Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Ioo] at hp
    change 0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ p 1 ∧ p 1 ≤ 1
    have h0 := hp 0 trivial
    have h1 := hp 1 trivial
    simpa [lo, hi] using ⟨h0.1.le, h0.2.le, h1.1.le, h1.2.le⟩
  have hcont : ContinuousOn (fun z => (A.map z).1) S :=
    continuous_fst.continuousOn.comp (A.continuous_on_domain.mono hSdom)
      (fun _ _ => mem_univ _)
  have hmeas := m60AreaDensity_aestronglyMeasurableOn (F.metric t) hS hcont
  have hfullS : IntegrableOn (m60AreaDensity (P.flow.metric t) A.map) S volume :=
    A.area_integrable.mono_set hSdom
  have hpoint : ∀ᵐ z ∂volume.restrict S,
      m60AreaDensity (F.metric t) (fun w => (A.map w).1) z ≤
        m60AreaDensity (P.flow.metric t) A.map z := by
    filter_upwards [ae_restrict_mem hS.measurableSet,
      ae_restrict_of_ae A.ae_manifold_differentiable] with z hzdom hz
    exact m64CircleProduct_projected_density_le P t A.map z (hz (hSdom hzdom))
  have hintS : IntegrableOn
      (m60AreaDensity (F.metric t) (fun z => (A.map z).1)) S volume :=
    hfullS.mono' hmeas (by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (m60AreaDensity_nonneg (F.metric t)
          (fun z => (A.map z).1) _)] using hpoint)
  have hae : m64AnnulusDomain =ᵐ[volume] S := by
    simpa only [S, e, lo, hi] using m64AnnulusDomain_ae_eq_boxInterior
  exact (integrableOn_congr_set_ae hae).mpr hintS

end PoincareConjecture
