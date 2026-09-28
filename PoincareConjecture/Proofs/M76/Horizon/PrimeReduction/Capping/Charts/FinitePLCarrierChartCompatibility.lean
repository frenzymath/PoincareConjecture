import PoincareConjecture.Proofs.M76.Mathlib.FinitePLNeighborhoodExtension
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLAtlasNeighborhood










set_option autoImplicit false

open Set Metric Geometry

namespace OpenPartialHomeomorph

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]



theorem mem_piecewiseAffineGroupoid_transition_of_finitePL_representatives
    {T : Set E} (Q Q' : OpenPartialHomeomorph T V)
    {A : Set E} {C : Set V} {f : E → V} {g : V → E}
    (hf : FinitePiecewiseAffineOn f A) (hg : FinitePiecewiseAffineOn g C)
    (hQs : ∀ x ∈ Q'.source, (x : E) ∈ A)
    (hQt : Q.target ⊆ interior C)
    (hQf : ∀ x ∈ Q'.source, Q' x = f x)
    (hQg : ∀ y ∈ Q.target, (Q.symm y : E) = g y) :
    Q.symm.trans Q' ∈ piecewiseAffineGroupoid V := by
  obtain ⟨f', U, _, hAU, hf', hff⟩ := hf.exists_locallyPiecewiseAffine_extension
  have hg' : LocallyPiecewiseAffineOn g Q.target :=
    hg.locallyPiecewiseAffineOn_of_subset_interior Q.open_target hQt
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  have hcomp : LocallyPiecewiseAffineOn (f' ∘ g) (Q.symm.trans Q').source := by
    apply (hf'.comp hg').mono (Q.symm.trans Q').open_source
    intro y hy
    refine ⟨hy.1, ?_⟩
    change g y ∈ U
    rw [← hQg y hy.1]
    exact hAU (hQs _ hy.2)
  apply hcomp.congr
  intro y hy
  have hy' : Q.symm y ∈ Q'.source := hy.2
  change f' (g y) = Q' (Q.symm y)
  rw [← hQg y hy.1]
  exact (hff (hQs (Q.symm y) hy')).trans (hQf (Q.symm y) hy').symm



theorem mem_piecewiseAffineGroupoid_transition_of_closed_ball_charts
    {T : Set E} (Q Q' : OpenPartialHomeomorph T V)
    {A B : Set E} {f : E → V} {g : V → E}
    (hQs : Q'.source = (Subtype.val : T → E) ⁻¹' (A \ B))
    (hQt : Q.target = interior (closedBall (0 : V) 1))
    (hf : FinitePiecewiseAffineOn f A)
    (hg : FinitePiecewiseAffineOn g (closedBall (0 : V) 1))
    (hQf : ∀ x : T, Q' x = f x)
    (hQg : ∀ y ∈ closedBall (0 : V) 1, (Q.symm y : E) = g y) :
    Q.symm.trans Q' ∈ piecewiseAffineGroupoid V := by
  apply Q.mem_piecewiseAffineGroupoid_transition_of_finitePL_representatives
    Q' hf hg
  · intro x hx
    rw [hQs] at hx
    exact hx.1
  · exact hQt ▸ subset_rfl
  · exact fun x _ => hQf x
  · exact fun y hy => hQg y (interior_subset (hQt ▸ hy))

end OpenPartialHomeomorph
