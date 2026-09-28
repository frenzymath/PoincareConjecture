import PoincareConjecture.Proofs.M09.PullbackFirstDerivatives
import PoincareConjecture.Proofs.M09.RegularRepresentative

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]

theorem lExponentialFamily_regular_branch_first_derivatives {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hL : LGeodesicTheory F T τmax) {p : M} (A : LExponentialFamily F T τmax p)
    (G : OpenPartialHomeomorph (TangentSpace (𝓡 n) p × ℝ) (M × ℝ))
    (hsource : G.source = A.regularDomain)
    (hforward : ∀ z, G z = (A.gamma z.1 z.2, z.2))
    (htarget : G.target ⊆ Set.univ ×ˢ Set.Ioo 0 τmax)
    (hinv : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
      ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ)))
        ((𝓘(ℝ, TangentSpace (𝓡 n) p)).prod (𝓘(ℝ, ℝ))) ∞ G.symm G.target)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hz : (Z, b) ∈ G.source) :
    let B : M × ℝ → ℝ := fun w ↦ A.action (G.symm w).1 w.2 / (2 * Real.sqrt w.2)
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
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let B : M × ℝ → ℝ := fun w ↦ A.action (G.symm w).1 w.2 / (2 * Real.sqrt w.2)
  have hreg : (Z, b) ∈ A.regularDomain := by simpa only [hsource] using hz
  obtain ⟨hb, hmax, _, _⟩ := hreg.1
  have hcenter : (A.gamma Z b, b) ∈ G.target := by
    rw [← hforward (Z, b)]
    exact G.map_source hz
  have hB : ContMDiffAt ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞ B (A.gamma Z b, b) :=
    (lExponentialFamily_regular_representative_smooth hM04 hτmax hwindow A G htarget hinv).contMDiffAt
      (G.open_target.mem_nhds hcenter)
  have hpull : (fun z : TangentSpace (𝓡 n) p × ℝ ↦ B (A.gamma z.1 z.2, z.2)) =ᶠ[𝓝 (Z, b)]
      (fun z ↦ A.action z.1 z.2 / (2 * Real.sqrt z.2)) := by
    filter_upwards [G.open_source.mem_nhds hz] with z hzs
    change A.action (G.symm (A.gamma z.1 z.2, z.2)).1 z.2 / (2 * Real.sqrt z.2) = _
    rw [← hforward z, G.left_inv hzs]
  exact lExponentialFamily_first_derivatives_of_pullback hM04 hτmax hwindow hL A Z b hb hmax
    B hB hpull hreg.2.2

end PoincareConjecture.Proofs.M09
