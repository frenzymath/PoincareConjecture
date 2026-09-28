import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.WeakCoordinates







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u
namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem LeviCivitaData.gradient_norm_sq_eq_inverse_pairing
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {f : M → ℝ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source)
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (e x)) :
    (g.tangentNorm (e x) (D.gradient f (e x))) ^ 2 =
      fderiv ℝ (f ∘ e) x ((g.pullbackCoefficients e x).inverse (fderiv ℝ (f ∘ e) x)) := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  obtain ⟨w, hw⟩ := hD.mfderiv_surjective hx (D.gradient f (e x))
  have hchain (v : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (f ∘ e) x v =
        mvfderiv (𝓡 n) f (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) := by
    have hh := congrArg (fun A => A v) (mvfderiv_comp x hf (hD.mdifferentiableAt hx))
    simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
      ContinuousLinearMap.comp_apply] at hh
    convert! hh using 1
  have hF : g.pullbackCoefficients e x w = fderiv ℝ (f ∘ e) x := by
    ext v
    change g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x w)
      (mfderiv (𝓡 n) (𝓡 n) e x v) = _
    rw [hw, D.inner_gradient, hchain]
  have hinv : (g.pullbackCoefficients e x).inverse (fderiv ℝ (f ∘ e) x) = w :=
    (g.isInvertible_pullbackCoefficients (hD.mfderiv_injective hx)).inverse_apply_eq.mpr hF.symm
  rw [hinv, hchain, hw, ← D.inner_gradient]
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact (real_inner_self_eq_norm_sq (D.gradient f (e x))).symm

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]



theorem AncientAsymptoticSolitonPredecessors.reducedLengthGradientNormSq_coordinates_ae
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target) :
    let g := K.flow.metric (0 - τ)
    let l := fun x => reducedLength K.flow 0 p (e x) τ
    ∀ᵐ x ∂volume, x ∈ e.source →
      reducedLengthGradientNormSq K.flow 0
        (fun z => reducedLength K.flow 0 p z.1 z.2) τ (e x) =
      fderiv ℝ l x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) := by
  obtain ⟨V⟩ := P.reduced_volume (τ + 1) (by linarith)
  obtain ⟨D⟩ := V.measure_regularity p
  filter_upwards [AncientAsymptoticSolitonPredecessors.ae_regular_in_coordinates
    D hτ (by linarith) e he hei] with x hx hxs
  obtain ⟨r⟩ := D.regular_points (e x, τ) (hx hxs)
  rw [reducedLengthGradientNormSq_eq_gradient_norm_sq]
  exact (K.flow.connection (0 - τ)).gradient_norm_sq_eq_inverse_pairing e he hei hxs
    ((AncientAsymptoticSolitonPredecessors.regular_reducedLength_spatial_smooth r).mdifferentiableAt
      (by simp))

end PoincareConjecture
