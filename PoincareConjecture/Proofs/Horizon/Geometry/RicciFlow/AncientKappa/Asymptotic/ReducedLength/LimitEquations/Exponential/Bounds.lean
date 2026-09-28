import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.WeakEquations.Lipschitz

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.LeviCivitaData

open Dirichlet Poincare.Analysis.Sobolev.Weak

private theorem memLp_top_of_continuousOn_closure
    {n : ℕ} {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContinuousOn f (closure O)) : MemLp f ∞ (volume.restrict O) := by
  obtain ⟨C, hC⟩ := hOc.exists_bound_of_continuousOn hf
  apply memLp_top_of_bound ((hf.mono subset_closure).aestronglyMeasurable hO.measurableSet) C
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  exact hC x (subset_closure hx)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem reducedPotential_flux_source_memLp
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOs : closure O ⊆ e.source)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hu : LipschitzOnWith L u (closure O)) (τ : ℝ) :
    (∀ i : Fin n, MemLp (fun x => -(∑ j, divergenceCoefficients g e x i j *
      fderiv ℝ u x (EuclideanSpace.single j 1))) 2 (volume.restrict O)) ∧
    MemLp (fun x => (fderiv ℝ u x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x)) -
      D.scalarCurvature (e x) - (u x - (n : ℝ)) / τ) *
        g.pullbackVolumeDensity e x / 2) 2 (volume.restrict O) := by
  let : IsFiniteMeasure (volume.restrict O) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt hOc.measure_lt_top⟩
  have hd (i : Fin n) : MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single i 1))
      ∞ (volume.restrict O) :=
    memLp_top_fderiv_apply_of_lipschitzOn hO (hu.mono subset_closure) _
  have ha (i j : Fin n) : MemLp (fun x => divergenceCoefficients g e x i j)
      ∞ (volume.restrict O) :=
    memLp_top_of_continuousOn_closure hO hOc
      ((contDiffOn_divergenceCoefficients e he hei i j).continuousOn.mono hOs)
  constructor
  · intro i
    exact (memLp_finsetSum Finset.univ (fun j _ =>
      (hd j).mul' (r := ∞) (ha i j))).neg.mono_exponent le_top
  · have henergy : MemLp (fun x => g.pullbackVolumeDensity e x *
        fderiv ℝ u x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x)))
        ∞ (volume.restrict O) := by
      have hs := memLp_finsetSum Finset.univ (fun i _ =>
        memLp_finsetSum Finset.univ (fun j _ =>
          ((ha i j).mul' (r := ∞) (hd j)).mul' (r := ∞) (hd i)))
      convert hs using 1
      funext x
      simpa only [mul_comm, mul_left_comm, mul_assoc] using
        (sum_divergenceCoefficients_eq_inverse_pairing (g := g) e x
          (fderiv ℝ u x) (fderiv ℝ u x)).symm
    have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
      ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
    have hρ : ContinuousOn (g.pullbackVolumeDensity e) (closure O) := by
      intro x hx
      exact (g.contDiffAt_pullbackVolumeDensity
        (he.contMDiffAt (e.open_source.mem_nhds (hOs hx)))
        (hD.mfderiv_injective (hOs hx))).1.continuousAt.continuousWithinAt
    have hR := D.continuous_scalarCurvature.comp_continuousOn (e.continuousOn.mono hOs)
    have hother : MemLp (fun x => (D.scalarCurvature (e x) +
        (u x - (n : ℝ)) / τ) * g.pullbackVolumeDensity e x) ∞ (volume.restrict O) :=
      memLp_top_of_continuousOn_closure hO hOc
        ((hR.add ((hu.continuousOn.sub continuousOn_const).div_const τ)).mul hρ)
    have h := ((henergy.sub hother).mul_const (2⁻¹ : ℝ)).mono_exponent
      (show (2 : ℝ≥0∞) ≤ (⊤ : ℝ≥0∞) from le_top)
    convert h using 1
    funext x
    dsimp only [Pi.sub_apply]
    ring

end PoincareConjecture.LeviCivitaData
