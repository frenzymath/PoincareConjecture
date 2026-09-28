import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Germ.SphereDifferential



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Reverse

private theorem bijective_convex_of_intertwining
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] (A A' L : E →L[Real] E)
    (hL : Function.Bijective L) (hcomm : L.comp A' = A.comp L) {t : Real}
    (hA' : Function.Bijective ((1 - t) • ContinuousLinearMap.id Real E + t • A')) :
    Function.Bijective ((1 - t) • ContinuousLinearMap.id Real E + t • A) := by
  let F := (1 - t) • ContinuousLinearMap.id Real E + t • A
  let G := (1 - t) • ContinuousLinearMap.id Real E + t • A'
  have hFG (u : E) : L (G u) = F (L u) := by
    change L ((1 - t) • u + t • A' u) = (1 - t) • L u + t • A (L u)
    rw [map_add, map_smul, map_smul]
    have hh := congrArg (fun M : E →L[Real] E => M u) hcomm
    change L (A' u) = A (L u) at hh
    rw [hh]
  have hinj : Function.Injective F := by
    intro x y hxy
    obtain ⟨u, rfl⟩ := hL.2 x
    obtain ⟨v, rfl⟩ := hL.2 y
    apply congrArg L
    apply hA'.1
    apply hL.1
    change L (G u) = L (G v)
    simpa only [hFG] using hxy
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

private abbrev E3 := EuclideanSpace Real (Fin 3)




theorem bijective_fderiv_homotopy_of_ambient_ball_boundary
    (B D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hball : D '' (B '' closedBall (0 : E3) 1) ⊆ B '' closedBall (0 : E3) 1)
    {U : Set E3} (hU : IsOpen U)
    (hfix : ∀ x ∈ U ∩ (B '' sphere (0 : E3) 1), D x = x)
    {x : E3} (hx : x ∈ U ∩ (B '' sphere (0 : E3) 1))
    {t : Real} (ht : t ∈ Icc 0 1) :
    Function.Bijective (fderiv Real (fun y => (1 - t) • y + t • D y) x) := by
  obtain ⟨p, hp, hpx⟩ := hx.2
  have hpU : B p ∈ U := hpx ▸ hx.1
  have hDp : D (B p) = B p := hfix (B p) ⟨hpU, ⟨p, hp, rfl⟩⟩
  let G := B.trans (D.trans B.symm)
  have hG (y : E3) : G y = B.symm (D (B y)) := rfl
  have hGp : G p = p := by rw [hG, hDp, B.symm_apply_apply]
  have hGball : MapsTo G (closedBall (0 : E3) 1) (closedBall (0 : E3) 1) := by
    intro y hy
    obtain ⟨z, hz, heq⟩ := hball ⟨B y, ⟨y, hy, rfl⟩, rfl⟩
    rw [hG, ← heq, B.symm_apply_apply]
    exact hz
  have hGfix : ∀ y ∈ B ⁻¹' U ∩ sphere (0 : E3) 1, G y = y := by
    intro y hy
    rw [hG, hfix (B y) ⟨hy.1, ⟨y, hy.2, rfl⟩⟩, B.symm_apply_apply]
  have hstandard := bijective_fderiv_homotopy_of_ball_preserving_sphere_patch
    G hGball (hU.preimage B.continuous) hGfix ht ⟨p, hp⟩ hpU
  have hBd : Differentiable Real B := B.contMDiff.contDiff.differentiable (by simp)
  have hDd : Differentiable Real D := D.contMDiff.contDiff.differentiable (by simp)
  have hGd : Differentiable Real G := G.contMDiff.contDiff.differentiable (by simp)
  have hcomm : (B : E3 -> E3) ∘ G = (D : E3 -> E3) ∘ B := by
    funext y
    exact B.apply_symm_apply (D (B y))
  have hleft := fderiv_comp p (hBd (G p)) (hGd p)
  have hright := fderiv_comp p (hDd (B p)) (hBd p)
  rw [hGp] at hleft
  have hlinear : (fderiv Real B p).comp (fderiv Real G p) =
      (fderiv Real D (B p)).comp (fderiv Real B p) := by
    rw [← hleft, hcomm, hright]
  have hBL : Function.Bijective (fderiv Real B p) := by
    have hh := (B.mfderivToContinuousLinearEquiv (by simp) p).bijective
    change Function.Bijective (mfderiv (𝓡 3) (𝓡 3) B p) at hh
    simpa only [mfderiv_eq_fderiv, TangentSpace] using hh
  have hdG := ((hasFDerivAt_id p).const_smul (1 - t)).add
    ((hGd p).hasFDerivAt.const_smul t)
  change Function.Bijective
    (fderiv Real ((1 - t) • (id : E3 -> E3) + t • (G : E3 -> E3)) p) at hstandard
  rw [hdG.fderiv] at hstandard
  have hdD := ((hasFDerivAt_id (B p)).const_smul (1 - t)).add
    ((hDd (B p)).hasFDerivAt.const_smul t)
  rw [← hpx]
  change Function.Bijective
    (fderiv Real ((1 - t) • (id : E3 -> E3) + t • (D : E3 -> E3)) (B p))
  rw [hdD.fderiv]
  exact bijective_convex_of_intertwining _ _ _ hBL hlinear hstandard

end Poincare.Manifold.Schoenflies.Reverse
