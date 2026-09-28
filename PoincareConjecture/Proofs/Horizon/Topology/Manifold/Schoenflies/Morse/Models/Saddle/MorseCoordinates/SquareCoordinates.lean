import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.QuadraticPatch.Coordinates
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.SquareCompletion

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle

private abbrev E2 := EuclideanSpace Real (Fin 2)

private def sphereRoot (q : E2) : Real := Real.sqrt (1-‖q‖^2)
private def negativeScale (q : E2) : Real := Real.sqrt (sphereRoot q / (1+sphereRoot q))
private def positiveScale (q : E2) : Real := Real.sqrt (1 / (1+sphereRoot q))

private theorem sphereRoot_pos {q : E2} (hq : q ∈ ball (0 : E2) 1) : 0 < sphereRoot q := by
  apply Real.sqrt_pos.mpr
  have hn := mem_ball_zero_iff.mp hq
  nlinarith [norm_nonneg q]

private theorem sphereRoot_smooth : ContDiffOn Real ∞ sphereRoot (ball (0 : E2) 1) :=
  (contDiff_const.sub (contDiff_id.norm_sq Real)).contDiffOn.sqrt (fun _ hq =>
    ne_of_gt (Real.sqrt_pos.mp (sphereRoot_pos hq)))

private theorem negativeScale_smooth :
    ContDiffOn Real ∞ negativeScale (ball (0 : E2) 1) := by
  apply (sphereRoot_smooth.div (contDiffOn_const.add sphereRoot_smooth)
    (fun q hq => by have := sphereRoot_pos hq; positivity)).sqrt
  intro q hq
  exact ne_of_gt (div_pos (sphereRoot_pos hq) (by have := sphereRoot_pos hq; positivity))

private theorem positiveScale_smooth :
    ContDiffOn Real ∞ positiveScale (ball (0 : E2) 1) := by
  apply (contDiffOn_const.div (contDiffOn_const.add sphereRoot_smooth)
    (fun q hq => by have := sphereRoot_pos hq; positivity)).sqrt
  intro q hq
  exact ne_of_gt (div_pos zero_lt_one (by have := sphereRoot_pos hq; positivity))

def squareCoordinates (q : E2) : E2 :=
  WithLp.toLp 2 ![negativeScale q * q 0, positiveScale q * q 1]

theorem lowerGraph_eq_signed_squares {q : E2} (hq : q ∈ ball (0 : E2) 1) :
    lowerGraph q = -1 - (squareCoordinates q 0)^2 + (squareCoordinates q 1)^2 := by
  have ht := sphereRoot_pos hq
  have hd : 0 < 1+sphereRoot q := by positivity
  have ht2 : (sphereRoot q)^2 = 1-‖q‖^2 :=
    Real.sq_sqrt (le_of_lt (Real.sqrt_pos.mp ht))
  change -sphereRoot q - (q 0)^2 =
    -1 - (negativeScale q * q 0)^2 + (positiveScale q * q 1)^2
  rw [mul_pow, mul_pow, negativeScale, positiveScale,
    Real.sq_sqrt (div_pos ht hd).le, Real.sq_sqrt (div_pos zero_lt_one hd).le]
  field_simp
  nlinarith [norm_sq_two q]

theorem exists_squareCoordinates_inverse :
    ∃ e : OpenPartialHomeomorph E2 E2,
      0 ∈ e.source ∧ e 0 = 0 ∧
      MapsTo e e.source (ball (0 : E2) 1) ∧
      ContDiffOn Real ∞ e e.source ∧ ContDiffOn Real ∞ e.symm e.target ∧
      ∀ x ∈ e.source, lowerGraph (e x) = -1-(x 0)^2+(x 1)^2 := by
  let C : E2 ≃L[Real] Real × Real :=
    (EuclideanSpace.equiv (Fin 2) Real).trans
      (LinearEquiv.finTwoArrow Real Real).toContinuousLinearEquiv
  have hC (x : E2) : C x = (x 0, x 1) := rfl
  have hC0 (x : Real × Real) : C.symm x 0 = x.1 := rfl
  have hC1 (x : Real × Real) : C.symm x 1 = x.2 := rfl
  let U : Set (Real × Real) := C.symm ⁻¹' ball (0 : E2) 1
  have hU : IsOpen U := isOpen_ball.preimage C.symm.continuous
  have h0 : (0 : Real × Real) ∈ U := by simp [U]
  let u := negativeScale ∘ C.symm
  let w := positiveScale ∘ C.symm
  have hu : ContDiffOn Real ∞ u U :=
    negativeScale_smooth.comp C.symm.contDiff.contDiffOn (fun _ hx => hx)
  have hw : ContDiffOn Real ∞ w U :=
    positiveScale_smooth.comp C.symm.contDiff.contDiffOn (fun _ hx => hx)
  obtain ⟨Q, hQ0, hQzero, hQU, hQcoe, hQ, hQi⟩ :=
    Poincare.Analysis.Calculus.Morse.exists_rescalingShear_localInverse
      hU h0 hu (contDiffOn_const (c := (0 : Real))) hw
      (by simp [u, negativeScale, sphereRoot]) (by simp [w, positiveScale, sphereRoot])
  have h0t : (0 : Real × Real) ∈ Q.target := hQzero ▸ Q.map_source hQ0
  have hQi0 : Q.symm 0 = 0 := by
    calc
      Q.symm 0 = Q.symm (Q 0) := by rw [hQzero]
      _ = 0 := Q.left_inv hQ0
  let e := (C.toHomeomorph.toOpenPartialHomeomorph.trans Q.symm).trans
    C.symm.toHomeomorph.toOpenPartialHomeomorph
  have he (x : E2) : e x = C.symm (Q.symm (C x)) := rfl
  have hei (x : E2) : e.symm x = C.symm (Q (C x)) := rfl
  have hes : ∀ x ∈ e.source, C x ∈ Q.target := fun _ hx => hx.1.2
  have het : ∀ x ∈ e.target, C x ∈ Q.source := fun _ hx => hx.2.1
  refine ⟨e, ⟨⟨mem_univ _, by simpa using h0t⟩, mem_univ _⟩,
    by simp [he, hQi0], ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hQU (Q.map_target (hes x hx))
  · exact C.symm.contDiff.contDiffOn.comp
      (hQi.comp C.contDiff.contDiffOn (fun x hx => hes x hx)) (fun _ _ => mem_univ _)
  · exact C.symm.contDiff.contDiffOn.comp
      (hQ.comp C.contDiff.contDiffOn (fun x hx => het x hx)) (fun _ _ => mem_univ _)
  · intro x hx
    have hmem : e x ∈ ball (0 : E2) 1 := hQU (Q.map_target (hes x hx))
    have hcoords : squareCoordinates (e x) = x := by
      have h := Q.right_inv (hes x hx)
      rw [hQcoe] at h
      have hfirst := congrArg Prod.fst h
      have hsecond := congrArg Prod.snd h
      apply C.injective
      apply Prod.ext
      · simpa [hC, squareCoordinates, he, u, hC0,
          Poincare.Analysis.Calculus.Morse.rescalingShearMap] using hfirst
      · simpa [hC, squareCoordinates, he, w, hC1,
          Poincare.Analysis.Calculus.Morse.rescalingShearMap] using hsecond
    rw [lowerGraph_eq_signed_squares hmem, hcoords]

end Poincare.Manifold.Schoenflies.Saddle
