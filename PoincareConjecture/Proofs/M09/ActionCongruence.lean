import PoincareConjecture.Proofs.M09.SquareActionIntegral

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem backwardLLength_congr_Ioo {J : Set ℝ} (F : RicciFlow n M J)
    (T a b : ℝ) (hab : a ≤ b) (γ δ : ℝ → M)
    (heq : Set.EqOn γ δ (Set.Ioo a b)) :
    backwardLLength F T a b γ = backwardLLength F T a b δ := by
  unfold backwardLLength
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro t ht
  have hlocal : γ =ᶠ[nhds t] δ := Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) heq
  have hderiv := hlocal.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n)
  have hv : (curveVelocity (n := n) γ t : EuclideanSpace ℝ (Fin n)) =
      curveVelocity (n := n) δ t :=
    congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) ↦ L 1) hderiv
  have hphase : (⟨γ t, curveVelocity (n := n) γ t⟩ : TangentBundle (𝓡 n) M) =
      ⟨δ t, curveVelocity (n := n) δ t⟩ :=
    Bundle.TotalSpace.ext (heq ht) (heq_of_eq hv)
  have hvalue := congrArg (fun q : TangentBundle (𝓡 n) M ↦
    Real.sqrt t * ((F.connection (T - t)).scalarCurvature q.1 +
      (F.metric (T - t)).inner q.1 q.2 q.2)) hphase
  exact hvalue

end PoincareConjecture.Proofs.M09
