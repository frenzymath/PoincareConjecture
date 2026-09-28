import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.SobolevLocalization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.DivergenceEquation







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet.Boundary

open Poincare.Analysis.Sobolev.Weak

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

local notation "E" => EuclideanSpace ℝ (Fin n)

omit [NeZero n] in
private theorem memLp_coeff_mul {K O : Set E} (hK : IsCompact K)
    (hO : MeasurableSet O) (hOK : O ⊆ K) {a v : E → ℝ}
    (ha : ContinuousOn a K) (hv : MemLp v 2 (volume.restrict O)) :
    MemLp (fun x => a x * v x) 2 (volume.restrict O) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ha
  apply hv.of_le_mul (((ha.mono hOK).aestronglyMeasurable hO).mul hv.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem hO] with x hx
  change ‖a x * v x‖ ≤ C * ‖v x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x (hOK hx)) (norm_nonneg _)

omit [NeZero n] in
private theorem weakPartial_eq_coordinateDerivative
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K O : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (hOK : O ⊆ K) (hO : IsOpen O) (u : H1Zero D Ω)
    {F p : E → ℝ} (i : Fin n) (hF : EqOn F (fun z => toL2 D Ω u (e z)) O)
    (hp : MemLp p 2 (volume.restrict O)) (hw : HasWeakPartialDeriv i p F O) :
    p =ᵐ[volume.restrict O]
      localCoordinateDerivative e he hei hK hKs hOK (EuclideanSpace.single i 1) u := by
  have hraw : HasWeakPartialDeriv i p (fun z => toL2 D Ω u (e z)) O := by
    intro φ hφ hc hs
    calc
      _ = ∫ z in O, F z * fderiv ℝ φ z (EuclideanSpace.single i 1) := by
        apply setIntegral_congr_fun hO.measurableSet
        intro z hz
        dsimp only
        rw [hF hz]
      _ = _ := hw φ hφ hc hs
  exact hraw.ae_eq hO (fun φ hφ hc hs =>
    localCoordinateDerivative_weak e he hei hK hKs hOK hO u i hφ hc hs)
    (hp.locallyIntegrable (by norm_num))
    ((Lp.memLp _).locallyIntegrable (by norm_num))



theorem weakEigen_localized_divergence
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ e.target)
    (hflat : ∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0)
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVs : closure V ⊆ e.source) (hone : ∀ z ∈ V, χ (e z) = 1)
    (u : H1Zero D Ω) (lambda : ℝ)
    (heigen : ∀ v : H1Zero D Ω,
      ⟪u, v⟫_ℝ = (1 + lambda) * ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ) :
    let F := chartPullback e (fun y => χ y * toL2 D Ω u y)
    let H := {z : E | 0 < z 0}
    MemW01p 2 F H ∧
    ∃ p : Fin n → E → ℝ,
      (∀ i, MemLp (p i) 2 (volume.restrict H)) ∧
      (∀ i, HasWeakPartialDeriv i (p i) F H) ∧
      (∀ i, MemLp (fun z => ∑ j, divergenceCoefficients g e z i j * p j z)
        2 (volume.restrict (V ∩ H))) ∧
      MemLp (fun z => (lambda * g.pullbackVolumeDensity e z) * F z)
        2 (volume.restrict (V ∩ H)) ∧
      (∀ φ : E → ℝ,
        ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V ∩ H →
        (∫ z in V ∩ H, ∑ i, ∑ j, divergenceCoefficients g e z i j * p j z *
          fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        ∫ z in V ∩ H, (lambda * g.pullbackVolumeDensity e z) * F z * φ z) := by
  classical
  dsimp only
  let F := chartPullback e (fun y => χ y * toL2 D Ω u y)
  let H : Set E := {z | 0 < z 0}
  have hH : IsOpen H := isOpen_lt continuous_const (by fun_prop)
  have hO : IsOpen (V ∩ H) := hV.inter hH
  have hOK : V ∩ H ⊆ closure V := inter_subset_left.trans subset_closure
  have hmeasure := Measure.restrict_mono (μ := volume)
    (show V ∩ H ⊆ H from inter_subset_right) le_rfl
  have hF : MemW01p 2 F H := memW01p_chartPullback_toL2 e he hei χ hχ hc hs hflat u
  choose p hp hw using hF.1.2
  have hpeq (i : Fin n) : p i =ᵐ[volume.restrict (V ∩ H)]
      localCoordinateDerivative e he hei hVc hVs hOK (EuclideanSpace.single i 1) u := by
    apply weakPartial_eq_coordinateDerivative e he hei hVc hVs hOK hO u i (F := F)
    · intro z hz
      simp only [F, chartPullback_apply e _ (hVs (hOK hz)), hone z hz.1, one_mul]
    · exact (hp i).mono_measure hmeasure
    · exact (hw i).restrict hO inter_subset_right
  have hFraw {z : E} (hz : z ∈ V ∩ H) : F z = toL2 D Ω u (e z) := by
    simp only [F, chartPullback_apply e _ (hVs (hOK hz)), hone z hz.1, one_mul]
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) (closure V) := by
    intro z hz
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds (hVs hz)))
      (hD.mfderiv_injective (hVs hz))).1.continuousAt.continuousWithinAt
  refine ⟨hF, p, hp, hw, ?_, ?_, ?_⟩
  · intro i
    apply memLp_finsetSum
    intro j _
    exact memLp_coeff_mul hVc hO.measurableSet hOK
      ((contDiffOn_divergenceCoefficients e he hei i j).continuousOn.mono hVs)
      ((hp j).mono_measure hmeasure)
  · exact memLp_coeff_mul hVc hO.measurableSet hOK (continuousOn_const.mul hρ)
      (hF.1.1.mono_measure hmeasure)
  · intro φ hφ hφc hφs
    have hΩ : e '' (V ∩ H) ⊆ Ω := by
      rintro y ⟨z, hz, rfl⟩
      exact (hflat z (hVs (hOK hz))).mpr hz.2
    have heq := weakEigen_divergence_local e he hei hVc hVs hOK hΩ u lambda heigen
      hφ hφc hφs
    calc
      _ = ∫ z in V ∩ H, ∑ i, ∑ j, divergenceCoefficients g e z i j *
          localCoordinateDerivative e he hei hVc hVs hOK (EuclideanSpace.single j 1) u z *
            fderiv ℝ φ z (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr hpeq] with z hz
        simp only [hz]
      _ = _ := heq
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
        change (lambda * g.pullbackVolumeDensity e z) * toL2 D Ω u (e z) * φ z =
          (lambda * g.pullbackVolumeDensity e z) * F z * φ z
        rw [hFraw hz]

end PoincareConjecture.LeviCivitaData.Dirichlet.Boundary
