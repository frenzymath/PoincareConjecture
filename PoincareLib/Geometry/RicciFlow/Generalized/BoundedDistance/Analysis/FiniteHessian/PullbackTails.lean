import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.FiniteHessian.Pullback

/-!
# Uniform finite pullback-error tails

A single family containing every tolerance level fixes the pullback
constant before the desired tolerance. Uniform ambient jet convergence
therefore gives uniform pullback jet convergence on the same source tails.
Source: Morgan--Tian Proposition 9.79, pp. 232-234, and Proposition 10.7,
p. 253; M28 derivations 103 and 105.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareMT.Proofs.M28.FiniteHessian

variable {ι E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Uniformly small ambient jets on source tails give uniformly small
pullback jets on source tails. Empty stage fibres are allowed. One common
estimate is applied before choosing the output tolerance; the coordinate
maps need not converge. Source: M28 derivation 105. -/
theorem exists_bilinear_pullback_error_tail (n : ℕ) (stage : ι → ℕ)
    {f : ι → E → F} {A : ι → F → F →L[ℝ] F →L[ℝ] G} {x : ι → E}
    (hf : HasUniformJetBoundsAt n (fun i => fderiv ℝ (f i)) x)
    (hcf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hcA : ∀ i, ContDiffAt ℝ ∞ (A i) (f i (x i)))
    (hA : ∀ delta : ℝ, 0 < delta → ∃ K : ℕ, ∀ i, K ≤ stage i →
      ∀ m ≤ n, ‖iteratedFDeriv ℝ m (A i) (f i (x i))‖ ≤ delta) :
    ∀ rho : ℝ, 0 < rho → ∃ K : ℕ, ∀ i, K ≤ stage i → ∀ m ≤ n,
      ‖iteratedFDeriv ℝ m (fun y => (A i (f i y)).bilinearComp
        (fderiv ℝ (f i) y) (fderiv ℝ (f i) y)) (x i)‖ ≤ rho := by
  classical
  have hpos (l : ℕ) : 0 < (1 / ((l : ℝ) + 1) : ℝ) := by positivity
  choose K hK using fun l : ℕ => hA (1 / ((l : ℝ) + 1)) (hpos l)
  let J := {p : ℕ × ι // K p.1 ≤ stage p.2}
  let error : J → ℝ := fun p => 1 / ((p.1.1 : ℝ) + 1)
  have hfj : HasUniformJetBoundsAt n
      (fun p : J => fderiv ℝ (f p.1.2)) (fun p => x p.1.2) := by
    intro m hm
    obtain ⟨C, hC⟩ := hf m hm
    exact ⟨C, fun p => hC p.1.2⟩
  obtain ⟨C, _, hC⟩ := exists_bilinear_pullback_error_bound n
    (f := fun p : J => f p.1.2) (A := fun p : J => A p.1.2)
    (x := fun p : J => x p.1.2) (error := error)
    (fun p => hpos p.1.1) hfj (fun p => hcf p.1.2) (fun p => hcA p.1.2)
    (fun m hm p => hK p.1.1 p.1.2 p.2 m hm)
  intro rho hrho
  obtain ⟨l, hl⟩ := exists_nat_gt (C / rho)
  have hsmall : C * (1 / ((l : ℝ) + 1)) ≤ rho := by
    rw [mul_one_div, div_le_iff₀ (by positivity : 0 < (l : ℝ) + 1)]
    have h := (div_lt_iff₀ hrho).mp hl
    nlinarith
  refine ⟨K l, fun i hi m hm => ?_⟩
  exact (hC m hm (⟨(l, i), hi⟩ : J)).trans hsmall

end PoincareMT.Proofs.M28.FiniteHessian
