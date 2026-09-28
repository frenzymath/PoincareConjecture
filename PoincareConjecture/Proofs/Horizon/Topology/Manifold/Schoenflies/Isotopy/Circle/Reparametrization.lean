import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.Reparametrization.Increasing
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.RadialBody







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev coordinates := Complex.orthonormalBasisOneI.repr

open PoincareConjecture

private def circlePlaneReflection : E2 ≃ₗᵢ[Real] E2 :=
  coordinates.symm.trans (Complex.conjLIE.trans coordinates)

private theorem circlePlaneReflection_unitCircleExp (s : Real) :
    circlePlaneReflection (unitCircleExp s) = (unitCircleExp (-s) : E2) := by
  change coordinates (Complex.conjLIE
    (coordinates.symm (coordinates (Circle.exp ((2 * Real.pi) * s) : ℂ)))) =
    coordinates (Circle.exp ((2 * Real.pi) * (-s)) : ℂ)
  rw [coordinates.symm_apply_apply, mul_neg, Circle.exp_neg, Circle.coe_inv_eq_conj]
  rfl

private theorem exists_ambient_circle_reparametrization
    (q : Diffeomorph (𝓡 1) (𝓡 1) S1 S1 ∞) :
    ∃ G : E2 ≃ₘ[Real] E2, ∀ p : S1, G p = (q p : E2) := by
  obtain ⟨L, hL⟩ := exists_real_diffeomorph_lift_circle q
  have hsame (s t : Real) (h : unitCircleExp s = unitCircleExp t) :
      unitCircleExp (L s) = unitCircleExp (L t) := by rw [hL, hL, h]
  have hinj (s t : Real) (h : unitCircleExp (L s) = unitCircleExp (L t)) :
      unitCircleExp s = unitCircleExp t := by
    rw [hL, hL] at h
    exact q.injective h
  rcases L.continuous.strictMono_of_inj L.injective with hm | hm
  · have hperiod := add_one_of_strictMono_circle_lift L.continuous hm
      (fun t => hsame (t + 1) t (unitCircleExp_periodic t)) hinj
    obtain ⟨G, _, hG⟩ := exists_ambient_diffeomorph_of_increasing_circle_lift L hm hperiod
    refine ⟨G, fun p => ?_⟩
    obtain ⟨s, rfl⟩ := unitCircleExp_surjective p
    rw [hG, hL]
  · let N : Real ≃ₘ[Real] Real := {
      toEquiv := Equiv.neg Real
      contMDiff_toFun := contDiff_id.neg.contMDiff
      contMDiff_invFun := contDiff_id.neg.contMDiff }
    let L' := N.trans L
    have hL' (s : Real) : L' s = L (-s) := rfl
    have hm' : StrictMono L' := fun a b hab => hm (neg_lt_neg hab)
    have hperiod' : ∀ t, unitCircleExp (L' (t + 1)) = unitCircleExp (L' t) := by
      intro t
      change unitCircleExp (L (-(t + 1))) = unitCircleExp (L (-t))
      apply hsame
      exact unitCircleExp_eq_iff.mpr ⟨-1, by simp; ring⟩
    have hinj' (s t : Real) (h : unitCircleExp (L' s) = unitCircleExp (L' t)) :
        unitCircleExp s = unitCircleExp t := by
      obtain ⟨n, hn⟩ := unitCircleExp_eq_iff.mp (hinj (-s) (-t) h)
      exact unitCircleExp_eq_iff.mpr ⟨-n, by push_cast; linarith⟩
    have hperiod := add_one_of_strictMono_circle_lift L'.continuous hm' hperiod' hinj'
    obtain ⟨G, _, hG⟩ := exists_ambient_diffeomorph_of_increasing_circle_lift L' hm' hperiod
    refine ⟨circlePlaneReflection.toContinuousLinearEquiv.toDiffeomorph.trans G, fun p => ?_⟩
    obtain ⟨s, rfl⟩ := unitCircleExp_surjective p
    change G (circlePlaneReflection (unitCircleExp s)) = _
    rw [circlePlaneReflection_unitCircleExp, hG, hL', neg_neg, hL]



theorem exists_ambient_diffeomorph_of_circle_diffeomorph
    (q : Diffeomorph (𝓡 1) (𝓡 1)
      (sphere (0 : EuclideanSpace Real (Fin 2)) 1)
      (sphere (0 : EuclideanSpace Real (Fin 2)) 1) ∞) :
    ∃ G : Diffeomorph (𝓡 2) (𝓡 2)
        (EuclideanSpace Real (Fin 2)) (EuclideanSpace Real (Fin 2)) ∞,
      (∀ p : sphere (0 : EuclideanSpace Real (Fin 2)) 1, G p = (q p : E2)) ∧
      G '' closedBall (0 : E2) 1 = closedBall (0 : E2) 1 ∧
      G '' ball (0 : E2) 1 = ball (0 : E2) 1 := by
  obtain ⟨G, hG⟩ := exists_ambient_circle_reparametrization q
  have hsphere : G '' sphere (0 : E2) 1 = sphere (0 : E2) 1 := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      rw [hG ⟨x, hx⟩]
      exact (q ⟨x, hx⟩).property
    · intro y hy
      refine ⟨q.symm ⟨y, hy⟩, (q.symm ⟨y, hy⟩).property, ?_⟩
      simpa using hG (q.symm ⟨y, hy⟩)
  have hdim : 1 < Module.rank Real E2 := by
    rw [← Module.finrank_eq_rank]
    norm_num
  have hboundary : G.toHomeomorph '' sphere (0 : E2) 1 =
      (Homeomorph.refl E2) '' sphere (0 : E2) 1 := by simpa using hsphere
  refine ⟨G, hG, ?_, ?_⟩
  · simpa using G.toHomeomorph.image_closedBall_eq_of_image_sphere_eq
      (Homeomorph.refl E2) hdim hboundary
  · simpa using G.toHomeomorph.image_ball_eq_of_image_sphere_eq
      (Homeomorph.refl E2) hdim hboundary

end Poincare.Manifold.Schoenflies
