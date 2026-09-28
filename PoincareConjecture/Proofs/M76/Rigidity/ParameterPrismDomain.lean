import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteConvexDomain
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedAffineHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

noncomputable def originalParameterPrismCoordinates : E ≃ᴬ[ℝ] V3 :=
  (ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod]) :
    E ≃L[ℝ] V3).toContinuousAffineEquiv

theorem originalParameterPrism_ballPair :
    IsFinitePLBallPair E (D ×ˢ I)
      ((Q ×ˢ I) ∪ (D ×ˢ ({(-1 : ℝ), 1} : Set ℝ))) :=
  (isFinitePLBallPair_unit_cube (ι := Fin 2)).prod (isFinitePLBallPair_Icc (by norm_num))

theorem exists_finite_originalParameterPrism :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = D ×ˢ I := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKS, _⟩, _⟩, _⟩ :=
    originalParameterPrism_ballPair
  exact ⟨K, hK, hKS⟩

theorem originalParameterPrism_frontier :
    frontier (D ×ˢ I) = (Q ×ˢ I) ∪ (D ×ˢ ({(-1 : ℝ), 1} : Set ℝ)) := by
  rw [frontier_prod_eq, isClosed_closedBall.closure_eq, isClosed_Icc.closure_eq,
    frontier_closedBall _ one_ne_zero, frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1),
    union_comm]

theorem plDomain_originalParameterPrism :
    PLDomain (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph)
      (originalParameterPrismCoordinates '' (D ×ˢ I)) := by
  classical
  let c := originalParameterPrismCoordinates
  obtain ⟨K, hK, hKS⟩ := exists_finite_originalParameterPrism
  have hcK : K.AffineOnFaces c := K.affineOnFaces_affine c.toContinuousAffineMap
  let J := hcK.embeddedImage c.injective.injOn
  have hJ : J.faces.Finite := hcK.embeddedImage_finite _ hK
  have hJS : J.space = c '' (D ×ˢ I) := by rw [hcK.embeddedImage_space, hKS]
  have hcompact : IsCompact (c '' (D ×ˢ I)) :=
    ((isCompact_closedBall (0 : V2) 1).prod isCompact_Icc).image c.continuous
  have hcv : Convex ℝ (c '' (D ×ˢ I)) :=
    ((convex_closedBall (0 : V2) 1).prod (convex_Icc (-1 : ℝ) 1)).affine_image
      c.toAffineEquiv.toAffineMap
  have hzero : ((0 : V2), (0 : ℝ)) ∈ interior (D ×ˢ I) := by
    rw [interior_prod_eq, interior_closedBall _ one_ne_zero, interior_Icc]
    exact ⟨mem_ball_self zero_lt_one, by norm_num⟩
  have hne : (interior (c '' (D ×ˢ I))).Nonempty := by
    change (interior (c.toHomeomorph '' (D ×ˢ I))).Nonempty
    rw [← c.toHomeomorph.image_interior]
    exact ⟨c (0, 0), mem_image_of_mem c hzero⟩
  have hfront (t : ℝ) (ht : t = -1 ∨ t = 1) :
      c ((0 : V2), t) ∈ frontier (c '' (D ×ˢ I)) := by
    change c.toHomeomorph ((0 : V2), t) ∈ frontier (c.toHomeomorph '' (D ×ˢ I))
    rw [← c.toHomeomorph.image_frontier, originalParameterPrism_frontier]
    apply mem_image_of_mem
    exact Or.inr ⟨mem_closedBall_self zero_le_one, ht⟩
  apply J.plDomain_convex_of_frontier_points hJ hcompact hcv hne hJS
    (hfront (-1) (Or.inl rfl)) (hfront 1 (Or.inr rfl))
  intro heq
  have h := congrArg (fun x : E => x.2) (c.injective heq)
  norm_num at h

end PoincareConjecture.M76
