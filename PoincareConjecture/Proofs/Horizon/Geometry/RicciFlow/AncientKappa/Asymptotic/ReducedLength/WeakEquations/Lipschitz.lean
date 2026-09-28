import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.WeakEquations.CoordinateGradient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.ComparisonTests

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

universe u
namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

open LeviCivitaData.Dirichlet Poincare.Analysis.Sobolev.Weak

private theorem memLp_top_on_compactClosure
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

theorem reducedLength_nonlinear_coordinate_source_memLp
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOs : closure O ⊆ e.source) :
    let g := K.flow.metric (0 - τ)
    let l := fun x => reducedLength K.flow 0 p (e x) τ
    MemLp (fun x => (fderiv ℝ l x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) -
      (K.flow.connection (0 - τ)).scalarCurvature (e x) - (l x - (n : ℝ)) / τ) *
        g.pullbackVolumeDensity e x / 2) 2 (volume.restrict O) := by
  let g := K.flow.metric (0 - τ)
  let l := fun x => reducedLength K.flow 0 p (e x) τ
  let : IsFiniteMeasure (volume.restrict O) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt hOc.measure_lt_top⟩
  obtain ⟨C, hC⟩ := P.reducedLength_lipschitzOn_compact_coordinates p hτ e he hOc hOs
  have hd (i : Fin n) : MemLp (fun x => fderiv ℝ l x (EuclideanSpace.single i 1))
      ∞ (volume.restrict O) :=
    memLp_top_fderiv_apply_of_lipschitzOn hO (hC.mono subset_closure) _
  have ha (i j : Fin n) : MemLp (fun x => divergenceCoefficients g e x i j)
      ∞ (volume.restrict O) :=
    memLp_top_on_compactClosure hO hOc
      ((contDiffOn_divergenceCoefficients e he hei i j).continuousOn.mono hOs)
  have henergy : MemLp (fun x => g.pullbackVolumeDensity e x *
      fderiv ℝ l x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)))
      ∞ (volume.restrict O) := by
    have hs := memLp_finsetSum Finset.univ (fun i _ =>
      memLp_finsetSum Finset.univ (fun j _ =>
        ((ha i j).mul' (r := ∞) (hd j)).mul' (r := ∞) (hd i)))
    convert hs using 1
    funext x
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      (sum_divergenceCoefficients_eq_inverse_pairing (g := g) e x
        (fderiv ℝ l x) (fderiv ℝ l x)).symm
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) (closure O) := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds (hOs hx)))
      (hD.mfderiv_injective (hOs hx))).1.continuousAt.continuousWithinAt
  have hl := (P.continuous_reducedLength p τ hτ).comp_continuousOn (e.continuousOn.mono hOs)
  have hR := (K.flow.connection (0 - τ)).continuous_scalarCurvature.comp_continuousOn
    (e.continuousOn.mono hOs)
  have hother : MemLp (fun x => ((K.flow.connection (0 - τ)).scalarCurvature (e x) +
      (l x - (n : ℝ)) / τ) * g.pullbackVolumeDensity e x) ∞ (volume.restrict O) :=
    memLp_top_on_compactClosure hO hOc
      ((hR.add ((hl.sub continuousOn_const).div_const τ)).mul hρ)
  have h := ((henergy.sub hother).mul_const (2⁻¹ : ℝ)).mono_exponent
    (show (2 : ℝ≥0∞) ≤ (⊤ : ℝ≥0∞) from le_top)
  convert h using 1
  funext x
  dsimp only [Pi.sub_apply]
  ring

theorem reducedLength_second_weak_coordinate_lipschitz_test
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOs : closure O ⊆ e.source)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ≥0}
    (hv : LipschitzWith C v) (hv0 : ∀ x, 0 ≤ v x)
    (hvc : HasCompactSupport v) (hvO : tsupport v ⊆ O) :
    let g := K.flow.metric (0 - τ)
    let l := fun x => reducedLength K.flow 0 p (e x) τ
    (∫ x in O, ∑ i : Fin n, (-g.pullbackVolumeDensity e x *
      WithLp.ofLp ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) i) *
      fderiv ℝ v x (EuclideanSpace.single i 1)) ≤
    ∫ x in O, ((fderiv ℝ l x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) -
      (K.flow.connection (0 - τ)).scalarCurvature (e x) - (l x - (n : ℝ)) / τ) *
        g.pullbackVolumeDensity e x / 2) * v x := by
  let g := K.flow.metric (0 - τ)
  let l := fun x => reducedLength K.flow 0 p (e x) τ
  let F := fun (i : Fin n) x => -g.pullbackVolumeDensity e x *
    WithLp.ofLp ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) i
  let f := fun x => (fderiv ℝ l x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) -
    (K.flow.connection (0 - τ)).scalarCurvature (e x) - (l x - (n : ℝ)) / τ) *
      g.pullbackVolumeDensity e x / 2
  have hF (i : Fin n) : MemLp (F i) 2 (volume.restrict O) :=
    P.reducedLength_coordinate_flux_memLp p hτ e he hei hO hOc hOs i
  have hf : MemLp f 2 (volume.restrict O) :=
    P.reducedLength_nonlinear_coordinate_source_memLp p hτ e he hei hO hOc hOs
  apply Poincare.Analysis.Elliptic.weakInequality_of_nonneg_compact_lipschitz
    hO hF hf ?_ hv hv0 hvc hvO
  intro φ hφ hφc hφO hφ0
  have hφ2 : MemLp φ 2 (volume.restrict O) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict O
  have hpartial (i : Fin n) : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))
      2 (volume.restrict O) := by
    have hcont : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hs : HasCompactSupport (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
      hφc.fderiv_apply ℝ _
    exact (hcont.memLp_of_hasCompactSupport hs).restrict O
  have hleft : IntegrableOn (fun x => ∑ i, F i x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) O :=
    integrable_finsetSum _ (fun i _ => (hF i).integrable_mul (hpartial i))
  have hright : IntegrableOn (fun x => f x * φ x) O := hf.integrable_mul hφ2
  have hp (x) : (∑ i, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      -g.pullbackVolumeDensity e x *
        fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) := by
    have h := congrArg (fderiv ℝ φ x)
      ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr
        ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)))
    simp only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply] at h
    rw [← h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [F]
    ring
  obtain ⟨_, hw⟩ := P.reducedLength_second_weak_coordinate_gradient_inequality
    p hτ e he hei hO (subset_closure.trans hOs) hφ hφc hφO hφ0
  have heq : (fun x => (φ x *
      (-fderiv ℝ l x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) +
        (K.flow.connection (0 - τ)).scalarCurvature (e x) + (l x - (n : ℝ)) / τ) -
      2 * fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x))) *
      g.pullbackVolumeDensity e x) =
      fun x => 2 * ((∑ i, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) -
        f x * φ x) := by
    funext x
    rw [hp]
    dsimp only [f]
    ring
  change (∫ x in O, _) ≤ 0 at hw
  rw [heq, integral_const_mul, integral_sub hleft hright] at hw
  linarith

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
