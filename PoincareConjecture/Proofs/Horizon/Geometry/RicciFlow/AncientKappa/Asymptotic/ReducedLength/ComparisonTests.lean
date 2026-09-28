import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.WeakCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.Coefficients
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.ComparisonTest

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u
namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

open LeviCivitaData.Dirichlet Poincare.Analysis.Sobolev.Weak

private theorem memLp_top_of_continuousOn_compactClosure
    {n : ℕ} {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContinuousOn f (closure O)) : MemLp f ∞ (volume.restrict O) := by
  obtain ⟨C, hC⟩ := hOc.exists_bound_of_continuousOn hf
  apply memLp_top_of_bound ((hf.mono subset_closure).aestronglyMeasurable hO.measurableSet) C
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  exact hC x (subset_closure hx)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M}

theorem reducedLength_coordinate_flux_memLp
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOs : closure O ⊆ e.source) (i : Fin n) :
    let g := K.flow.metric (0 - τ)
    let l := fun x ↦ reducedLength K.flow 0 p (e x) τ
    MemLp (fun x ↦ -g.pullbackVolumeDensity e x *
      WithLp.ofLp ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) i)
        2 (volume.restrict O) := by
  let g := K.flow.metric (0 - τ)
  let l := fun x ↦ reducedLength K.flow 0 p (e x) τ
  let : IsFiniteMeasure (volume.restrict O) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt hOc.measure_lt_top⟩
  obtain ⟨C, hC⟩ := P.reducedLength_lipschitzOn_compact_coordinates p hτ e he hOc hOs
  have hd (j : Fin n) : MemLp (fun x ↦ fderiv ℝ l x (EuclideanSpace.single j 1))
      2 (volume.restrict O) :=
    (memLp_top_fderiv_apply_of_lipschitzOn hO (hC.mono subset_closure) _).mono_exponent le_top
  have ha (j : Fin n) : MemLp (fun x ↦ divergenceCoefficients g e x i j)
      ∞ (volume.restrict O) :=
    memLp_top_of_continuousOn_compactClosure hO hOc
      ((contDiffOn_divergenceCoefficients e he hei i j).continuousOn.mono hOs)
  have hsum : MemLp (fun x ↦ ∑ j, divergenceCoefficients g e x i j *
      fderiv ℝ l x (EuclideanSpace.single j 1)) 2 (volume.restrict O) :=
    memLp_finsetSum _ (fun j _ ↦ (hd j).mul' (ha j))
  have hflux (x) : -g.pullbackVolumeDensity e x *
      WithLp.ofLp ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) i =
      -(∑ j, divergenceCoefficients g e x i j * fderiv ℝ l x (EuclideanSpace.single j 1)) := by
    have h := sum_divergenceCoefficients_eq_inverse_pairing (g := g) e x
      (fderiv ℝ l x) (EuclideanSpace.proj i)
    have h' : (∑ j, divergenceCoefficients g e x i j * fderiv ℝ l x (EuclideanSpace.single j 1)) =
        g.pullbackVolumeDensity e x *
          WithLp.ofLp ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) i := by
      simpa [PiLp.proj_apply, PiLp.single_apply, Finset.sum_mul] using h
    rw [h', neg_mul]
  exact hsum.neg.ae_eq (Eventually.of_forall fun x ↦ (hflux x).symm)

theorem reducedLength_coordinate_source_memLp
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOs : closure O ⊆ e.source) :
    MemLp (fun x ↦ ((reducedLength K.flow 0 p (e x) τ + (n : ℝ) / 2) / τ) *
      (K.flow.metric (0 - τ)).pullbackVolumeDensity e x) 2 (volume.restrict O) := by
  let g := K.flow.metric (0 - τ)
  let : IsFiniteMeasure (volume.restrict O) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt hOc.measure_lt_top⟩
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) (closure O) := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds (hOs hx)))
      (hD.mfderiv_injective (hOs hx))).1.continuousAt.continuousWithinAt
  have hl := (P.continuous_reducedLength p τ hτ).comp_continuousOn (e.continuousOn.mono hOs)
  exact (memLp_top_of_continuousOn_compactClosure hO hOc
    (((hl.add continuousOn_const).div_const τ).mul hρ)).mono_exponent le_top

theorem reducedLength_weak_coordinate_comparison_test
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOs : closure O ⊆ e.source)
    {v φ : EuclideanSpace ℝ (Fin n) → ℝ} {B ε : ℝ≥0}
    (hv : LipschitzOnWith B v O)
    (herr : ∀ x ∈ O, |reducedLength K.flow 0 p (e x) τ - v x| ≤ ε)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) :
    let g := K.flow.metric (0 - τ)
    let l := fun x ↦ reducedLength K.flow 0 p (e x) τ
    (∫ x in O, ∑ i : Fin n,
      (-g.pullbackVolumeDensity e x *
        WithLp.ofLp ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) i) *
      (φ x * (fderiv ℝ v x (EuclideanSpace.single i 1) -
        fderiv ℝ l x (EuclideanSpace.single i 1)) +
        (v x - l x + ε) * fderiv ℝ φ x (EuclideanSpace.single i 1))) ≤
      ∫ x in O, (((l x + (n : ℝ) / 2) / τ) * g.pullbackVolumeDensity e x) *
        (φ x * (v x - l x + ε)) := by
  obtain ⟨C, hC⟩ := P.reducedLength_lipschitzOn_compact_coordinates p hτ e he hOc hOs
  apply Poincare.Analysis.Elliptic.weakInequality_comparison_test hO
    (fun i ↦ P.reducedLength_coordinate_flux_memLp p hτ e he hei hO hOc hOs i)
    (P.reducedLength_coordinate_source_memLp p hτ e he hei hO hOc hOs) ?_
    (hC.mono subset_closure) hv herr hφ hφc hφO hφ0 hφ1
  intro ψ hψ hψc hψO hψ0
  exact P.reducedLength_weak_coordinate_divergence_le p hτ e he hei hO hOc hOs
    hψ hψc hψO hψ0

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
