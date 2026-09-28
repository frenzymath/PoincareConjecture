import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.NormalDerivative
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.DifferentiatedEquation








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace Poincare.Analysis.Sobolev.BoundaryNormal

open Weak Poincare.Analysis.Sobolev.Euclidean NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)



theorem memWkp_three_of_tangential_memWkp_two
    (B : SmoothEllipticBilinearForm d univ)
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    {u f : E → ℝ} (hu : MemWkp 2 2 u O) (hf : MemW1p 2 f O)
    (htan : ∀ k : Fin d, k ≠ 0 → MemWkp 2 2 (chosenWeakPartial' 2 k u O) O)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u O x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x) :
    MemWkp 3 2 u O := by
  let p (i : Fin d) := chosenWeakPartial' 2 i u O
  have hp (i : Fin d) : MemW1p 2 (p i) O := (hu.chosenWeakPartial_mem i).memW1p
  have hw (i : Fin d) : HasWeakPartialDeriv i (p i) u O :=
    chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i
  let q (i : Fin d) := chosenWeakPartial' 2 i (p 0) O
  have hq (i : Fin d) : MemLp (q i) 2 (volume.restrict O) :=
    chosenWeakPartial'_memLp_of_mem (hp 0) i
  have hwq (i : Fin d) : HasWeakPartialDeriv i (q i) (p 0) O :=
    chosenWeakPartial'_isWeakPartial_of_mem (hp 0) i
  obtain ⟨F, hF, hFeq⟩ := BoundaryTangential.exists_weak_divergence_chosenWeakPartial
    hO hOc B.a B.smooth_a hu hf heq 0
  have hqtan (k : Fin d) (hk : k ≠ 0) (i : Fin d) :
      ∃ r, MemLp r 2 (volume.restrict O) ∧ HasWeakPartialDeriv k r (q i) O := by
    let v := chosenWeakPartial' 2 0 (p k) O
    have hv : MemW1p 2 v O := ((htan k hk).chosenWeakPartial_mem 0).memW1p
    have hwv : HasWeakPartialDeriv k v (p 0) O :=
      BoundaryTangential.weakPartial_commute k 0 (hw k) (hw 0)
        (chosenWeakPartial'_isWeakPartial_of_mem (hp k) 0)
    refine ⟨chosenWeakPartial' 2 i v O, chosenWeakPartial'_memLp_of_mem hv i, ?_⟩
    exact BoundaryTangential.weakPartial_commute k i hwv (hwq i)
      (chosenWeakPartial'_isWeakPartial_of_mem hv i)
  have hp0 : MemWkp 2 2 (p 0) O :=
    memWkp_two_of_tangential_weakDerivatives B hO hOc (hp 0).1 hF hq hwq hqtan hFeq
  refine ⟨hu.memW1p, fun i => ?_⟩
  by_cases hi : i = 0
  · simpa only [hi] using hp0
  · exact htan i hi

end Poincare.Analysis.Sobolev.BoundaryNormal
