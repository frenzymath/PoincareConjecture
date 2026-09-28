import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.Scaling

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u
namespace PoincareConjecture.AncientRescaling

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {s : ℝ} (R : AncientRescaling K s)

def reducedLengthCoordinateFlux (p : M) (τ : ℝ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  -(R.flow.metric (-τ)).pullbackVolumeDensity e x *
    WithLp.ofLp (((R.flow.metric (-τ)).pullbackCoefficients e x).inverse
      (fderiv ℝ (fun y => reducedLength K.flow 0 p (e y) (s * τ)) x)) i

def reducedLengthCoordinateSource (p : M) (τ : ℝ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ((reducedLength K.flow 0 p (e x) (s * τ) + (n : ℝ) / 2) / τ) *
    (R.flow.metric (-τ)).pullbackVolumeDensity e x

theorem reducedLengthCoordinateFlux_scale (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) (i : Fin n) :
    R.reducedLengthCoordinateFlux p τ e i x =
      (Real.sqrt ((1 / s) ^ n) * s) *
        (-(K.flow.metric (0 - s * τ)).pullbackVolumeDensity e x *
          WithLp.ofLp (((K.flow.metric (0 - s * τ)).pullbackCoefficients e x).inverse
            (fderiv ℝ (fun y => reducedLength K.flow 0 p (e y) (s * τ)) x)) i) := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  unfold reducedLengthCoordinateFlux
  rw [R.pullbackVolumeDensity_scale hτ, R.inverse_pullbackCoefficients_scale hτ
    (hD.mfderiv_injective hx)]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem reducedLengthCoordinateSource_scale (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (x : EuclideanSpace ℝ (Fin n)) :
    R.reducedLengthCoordinateSource p τ e x =
      (Real.sqrt ((1 / s) ^ n) * s) *
        (((reducedLength K.flow 0 p (e x) (s * τ) + (n : ℝ) / 2) / (s * τ)) *
          (K.flow.metric (0 - s * τ)).pullbackVolumeDensity e x) := by
  unfold reducedLengthCoordinateSource
  rw [R.pullbackVolumeDensity_scale hτ]
  field_simp [R.tau_pos.ne', hτ.ne']

theorem reducedLengthCoordinateFlux_memLp
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOs : closure O ⊆ e.source) (i : Fin n) :
    MemLp (R.reducedLengthCoordinateFlux p τ e i) 2 (volume.restrict O) := by
  have h := (P.reducedLength_coordinate_flux_memLp p (mul_pos R.tau_pos hτ)
    e he hei hO hOc hOs i).const_mul (Real.sqrt ((1 / s) ^ n) * s)
  apply h.ae_eq
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  exact (R.reducedLengthCoordinateFlux_scale p hτ e he hei (hOs (subset_closure hx)) i).symm

theorem reducedLengthCoordinateSource_memLp
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOs : closure O ⊆ e.source) :
    MemLp (R.reducedLengthCoordinateSource p τ e) 2 (volume.restrict O) := by
  have h := (P.reducedLength_coordinate_source_memLp p (mul_pos R.tau_pos hτ)
    e he hei hO hOc hOs).const_mul (Real.sqrt ((1 / s) ^ n) * s)
  exact h.ae_eq (Eventually.of_forall fun x => (R.reducedLengthCoordinateSource_scale p hτ e x).symm)

theorem reducedLength_weak_coordinate_divergence_le
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOs : closure O ⊆ e.source)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) :
    (∫ x in O, ∑ i, R.reducedLengthCoordinateFlux p τ e i x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) ≤
      ∫ x in O, R.reducedLengthCoordinateSource p τ e x * φ x := by
  have h := P.reducedLength_weak_coordinate_divergence_le p (mul_pos R.tau_pos hτ)
    e he hei hO hOc hOs hφ hφc hφO hφ0
  have hm := mul_le_mul_of_nonneg_left h
    (mul_nonneg (Real.sqrt_nonneg ((1 / s) ^ n)) R.tau_pos.le)
  rw [← integral_const_mul, ← integral_const_mul] at hm
  convert! hm using 1
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [R.reducedLengthCoordinateFlux_scale p hτ e he hei (hOs (subset_closure hx)) i]
    ring
  · apply integral_congr_ae
    filter_upwards with x
    rw [R.reducedLengthCoordinateSource_scale p hτ]
    ring

end PoincareConjecture.AncientRescaling
