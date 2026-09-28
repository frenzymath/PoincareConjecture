import PoincareConjecture.Proofs.M09.SpatialContact
import PoincareConjecture.Proofs.M09.NormalizedActionDerivative
import PoincareConjecture.Proofs.M09.ParametricCurveDerivative
import PoincareConjecture.Proofs.M09.MinimizingInitialVectors








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_first_derivatives_of_lower_contact
    {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hL : LGeodesicTheory F T τmax) {p : M}
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax) (B : M × ℝ → ℝ)
    (hB : ContMDiffAt ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞ B (A.gamma Z b, b))
    (hvalue : B (A.gamma Z b, b) = A.action Z b / (2 * Real.sqrt b))
    (hlower : ∀ᶠ w in 𝓝 (A.gamma Z b, b), B w ≤ reducedLength F T p w.1 w.2) :
    (∀ v : TangentSpace (𝓡 n) (A.gamma Z b),
      mvfderiv (𝓡 n) (fun q ↦ B (q, b)) (A.gamma Z b) v =
        (F.metric (T - b)).inner (A.gamma Z b) (curveVelocity (A.gamma Z) b) v) ∧
    reducedLengthGradientNormSq F T B b (A.gamma Z b) =
      (F.metric (T - b)).inner (A.gamma Z b)
        (curveVelocity (A.gamma Z) b) (curveVelocity (A.gamma Z) b) ∧
    deriv (fun t ↦ B (A.gamma Z b, t)) b =
      ((F.connection (T - b)).scalarCurvature (A.gamma Z b) -
        (F.metric (T - b)).inner (A.gamma Z b)
          (curveVelocity (A.gamma Z) b) (curveVelocity (A.gamma Z) b)) / 2 -
        B (A.gamma Z b, b) / (2 * b) := by
  have hspace := lExponentialFamily_spatial_differential_of_lower_contact hM04 hτmax
    hwindow hL A Z b hb hmax (fun q ↦ B (q, b))
    (hB.comp (A.gamma Z b) (contMDiffAt_id.prodMk contMDiffAt_const)) hvalue
    ((continuous_id.prodMk continuous_const).continuousAt.tendsto.eventually hlower)
  refine ⟨hspace, reducedLengthGradientNormSq_eq_of_differential F T b B _ _ hspace, ?_⟩
  have hswap := (hB.comp (b, A.gamma Z b)
    (contMDiffAt_snd.prodMk contMDiffAt_fst)).mdifferentiableAt (by simp)
  have hcurve := (lExponentialFamily_gammaSlice_contMDiffAt A Z b hb hmax).mdifferentiableAt (by simp)
  have hchain := hasDerivAt_parametric_curve (fun z : ℝ × M ↦ B (z.2, z.1))
    (A.gamma Z) b hswap hcurve
  have hactual := lExponentialFamily_normalizedAction_hasDerivAt hM04 hwindow A Z b hb hmax
  have hnear : ∀ᶠ t in 𝓝 b,
      B (A.gamma Z t, t) ≤ reducedLength F T p (A.gamma Z t) t :=
    (hcurve.continuousAt.prodMk continuousAt_id).tendsto.eventually hlower
  have hmin : IsLocalMin
      (fun t ↦ A.action Z t / (2 * Real.sqrt t) - B (A.gamma Z t, t)) b := by
    filter_upwards [isOpen_Ioo.mem_nhds (show b ∈ Set.Ioo 0 τmax from ⟨hb, hmax⟩), hnear]
      with t ht hl
    rw [← hvalue, sub_self]
    exact sub_nonneg.mpr (hl.trans
      (lExponentialFamily_reducedLength_le_action hL A Z t ht.1 ht.2))
  have hstat := hmin.hasDerivAt_eq_zero (hactual.sub hchain)
  dsimp only at hstat
  rw [hspace, ← hvalue] at hstat
  linarith

end PoincareConjecture.Proofs.M09
