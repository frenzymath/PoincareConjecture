import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.WeakLaplacian

/-!
# The Hamilton--Jacobi identity for actual reduced length

The two regular-point differential formulas eliminate the reduced Harnack
integral. The slice-null exceptional set then gives the identity for the
actual reduced length almost everywhere and relates the two frozen weak
integrands. Reference: Morgan--Tian, Theorem 6.50, p. 131, and Corollary 6.51,
p. 132 (Clay edition).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.AncientAsymptoticSolitonPredecessors

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M}

/-- The actual reduced length satisfies Hamilton--Jacobi at every regular point. -/
theorem regular_reducedLength_hamiltonJacobi (P : AncientAsymptoticSolitonPredecessors K)
    {R τ : ℝ} {p q : M} (r : ReducedLengthRegularPoint K.flow 0 R p q τ) :
    2 * deriv (fun s => reducedLength K.flow 0 p q s) τ +
      reducedLengthGradientNormSq K.flow 0 (fun z => reducedLength K.flow 0 p z.1 z.2) τ q -
      (K.flow.connection (0 - τ)).scalarCurvature q + reducedLength K.flow 0 p q τ / τ = 0 := by
  obtain ⟨Q⟩ := P.reduced_length R (r.tau_pos.trans r.tau_lt)
  have ht := (Q.regular_point_formulas p q τ r).1
  have hg := (Q.regular_point_formulas p q τ r).2.1
  have htime : (fun s => reducedLength K.flow 0 p q s) =ᶠ[𝓝 τ]
      (fun s => r.representative (q, s)) := by
    have hnb := (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (r.neighborhood_open.mem_nhds r.center_mem)
    filter_upwards [hnb] with s hs
    exact (r.representative_eq (q, s) hs).symm
  have hgrad : reducedLengthGradientNormSq K.flow 0
      (fun z => reducedLength K.flow 0 p z.1 z.2) τ q =
      reducedLengthGradientNormSq K.flow 0 r.representative τ q := by
    unfold reducedLengthGradientNormSq
    simp only [mvfderiv, (regular_reducedLength_spatial_eventuallyEq r).mfderiv_eq]
    rfl
  rw [r.representative_eq (q, τ) r.center_mem] at ht hg
  rw [htime.deriv_eq, hgrad, ht, hg]
  ring

/-- Every positive-time slice satisfies the Hamilton--Jacobi identity almost
everywhere with respect to its actual Riemannian volume. -/
theorem ae_reducedLength_hamiltonJacobi (P : AncientAsymptoticSolitonPredecessors K)
    (p : M) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᵐ q ∂calibratedMetricVolume (K.flow.metric (0 - τ)),
      2 * deriv (fun s => reducedLength K.flow 0 p q s) τ +
        reducedLengthGradientNormSq K.flow 0 (fun z => reducedLength K.flow 0 p z.1 z.2) τ q -
        (K.flow.connection (0 - τ)).scalarCurvature q + reducedLength K.flow 0 p q τ / τ = 0 := by
  obtain ⟨V⟩ := P.reduced_volume (τ + 1) (by linarith)
  obtain ⟨D⟩ := V.measure_regularity p
  have hreg : ∀ᵐ q ∂calibratedMetricVolume (K.flow.metric (0 - τ)),
      (q, τ) ∈ D.regularDomain := ae_iff.mpr (D.slice_complement_null τ hτ (by linarith))
  filter_upwards [hreg] with q hq
  obtain ⟨r⟩ := D.regular_points (q, τ) hq
  exact P.regular_reducedLength_hamiltonJacobi r

/-- The two supplied weak integrands are opposite multiples almost everywhere. -/
theorem ae_reducedLength_weak_integrands_relation
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (φ : M → ℝ) :
    ∀ᵐ q ∂calibratedMetricVolume (K.flow.metric (0 - τ)),
      2 * reducedLengthFirstWeakIntegrand K.flow 0 p τ φ q +
        reducedLengthSecondWeakIntegrand K.flow 0 p τ φ q = 0 := by
  filter_upwards [P.ae_reducedLength_hamiltonJacobi p hτ] with q hq
  dsimp only [reducedLengthFirstWeakIntegrand, reducedLengthSecondWeakIntegrand]
  have h := congrArg (fun x => φ q * x) hq
  field_simp at h ⊢
  nlinarith

end PoincareMT.AncientAsymptoticSolitonPredecessors
