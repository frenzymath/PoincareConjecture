import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.WeakEquations.Lipschitz
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.ExponentialTest








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

universe u
namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

open LeviCivitaData.Dirichlet Poincare.Analysis.Sobolev.Weak

private theorem covector_coordinates
    {n : ℕ} (D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    (∑ i, v i * D (EuclideanSpace.single i 1)) = D v := by
  have h := congrArg D ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply] using h

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M}

theorem reducedLength_exponential_weak_coordinate_inequality
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOs : closure O ⊆ e.source)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) :
    let g := K.flow.metric (0 - τ)
    let l := fun x => reducedLength K.flow 0 p (e x) τ
    let B := fun x => g.pullbackVolumeDensity e x * Real.exp (-l x) *
      (φ x * (fderiv ℝ l x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) +
        (K.flow.connection (0 - τ)).scalarCurvature (e x) + (l x - (n : ℝ)) / τ) / 2 -
        fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)))
    IntegrableOn B O ∧ (∫ x in O, B x) ≤ 0 := by
  let g := K.flow.metric (0 - τ)
  let l := fun x => reducedLength K.flow 0 p (e x) τ
  let v := fun x => φ x * Real.exp (-l x)
  let F := fun (i : Fin n) x => -g.pullbackVolumeDensity e x *
    WithLp.ofLp ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) i
  let f := fun x => (fderiv ℝ l x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) -
    (K.flow.connection (0 - τ)).scalarCurvature (e x) - (l x - (n : ℝ)) / τ) *
      g.pullbackVolumeDensity e x / 2
  let : IsFiniteMeasure (volume.restrict O) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt hOc.measure_lt_top⟩
  obtain ⟨A, hA⟩ := P.reducedLength_lipschitzOn_compact_coordinates p hτ e he hOc hOs
  obtain ⟨C, hC⟩ := Poincare.Analysis.Elliptic.compact_lipschitz_exp_test hOc hA hφ hφc hφO
  have hv0 (x) : 0 ≤ v x := mul_nonneg (hφ0 x) (Real.exp_pos _).le
  have hvc : HasCompactSupport v := hφc.mul_right
  have hvO : tsupport v ⊆ O := tsupport_mul_subset_left.trans hφO
  have hw := P.reducedLength_second_weak_coordinate_lipschitz_test
    p hτ e he hei hO hOc hOs hC hv0 hvc hvO
  have hF (i : Fin n) : MemLp (F i) 2 (volume.restrict O) :=
    P.reducedLength_coordinate_flux_memLp p hτ e he hei hO hOc hOs i
  have hf : MemLp f 2 (volume.restrict O) :=
    P.reducedLength_nonlinear_coordinate_source_memLp p hτ e he hei hO hOc hOs
  have hv : MemLp v 2 (volume.restrict O) :=
    (hC.continuous.memLp_of_hasCompactSupport hvc).restrict O
  have hpartial (i : Fin n) : MemLp (fun x => fderiv ℝ v x (EuclideanSpace.single i 1))
      2 (volume.restrict O) :=
    (memLp_top_fderiv_apply_of_lipschitzOn hO hC.lipschitzOnWith _).mono_exponent le_top
  have hleft : IntegrableOn (fun x => ∑ i, F i x *
      fderiv ℝ v x (EuclideanSpace.single i 1)) O :=
    integrable_finsetSum Finset.univ (fun i _ => (hF i).integrable_mul (hpartial i))
  have hright : IntegrableOn (fun x => f x * v x) O := hf.integrable_mul hv
  have hi := hleft.sub hright
  have heq : (fun x => (∑ i, F i x * fderiv ℝ v x (EuclideanSpace.single i 1)) -
      f x * v x) =ᵐ[volume.restrict O]
      (fun x => g.pullbackVolumeDensity e x * Real.exp (-l x) *
        (φ x * (fderiv ℝ l x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) +
          (K.flow.connection (0 - τ)).scalarCurvature (e x) + (l x - (n : ℝ)) / τ) / 2 -
          fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)))) := by
    filter_upwards [ae_restrict_mem hO.measurableSet,
      ae_restrict_of_ae ((hA.mono subset_closure).ae_differentiableWithinAt_of_mem
        (μ := volume))] with x hx hdx
    have dl : DifferentiableAt ℝ l x := (hdx hx).differentiableAt (hO.mem_nhds hx)
    have dv : fderiv ℝ v x = Real.exp (-l x) • fderiv ℝ φ x -
        (φ x * Real.exp (-l x)) • fderiv ℝ l x := by
      change fderiv ℝ (φ * fun y => Real.exp ((-l) y)) x = _
      rw [((hφ.differentiable (by simp) x).hasFDerivAt.mul
        dl.hasFDerivAt.neg.exp).fderiv]
      ext w
      simp only [Pi.neg_apply, add_apply, smul_apply, neg_apply, smul_eq_mul, sub_apply]
      ring
    have hs : (∑ i, F i x * fderiv ℝ v x (EuclideanSpace.single i 1)) =
        -g.pullbackVolumeDensity e x *
          fderiv ℝ v x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) := by
      dsimp only [F]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, covector_coordinates]
    rw [hs, dv]
    dsimp only [f, v]
    simp only [sub_apply, smul_apply, smul_eq_mul]
    ring
  refine ⟨hi.congr heq, ?_⟩
  dsimp only [g, l] at heq
  change (∫ x in O, _) ≤ 0
  rw [← integral_congr_ae heq, integral_sub hleft hright]
  exact sub_nonpos.mpr hw

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
