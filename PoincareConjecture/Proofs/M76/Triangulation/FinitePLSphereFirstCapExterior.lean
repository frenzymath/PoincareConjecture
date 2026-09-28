import PoincareConjecture.Proofs.M76.Triangulation.FinitePLSphereLocalFirstCap
import PoincareConjecture.Proofs.M76.Triangulation.ConvexFrontierConeExterior
import PoincareConjecture.Proofs.M76.Mathlib.PositiveHeightCutEnvelope
import PoincareConjecture.Proofs.M76.Mathlib.SmallConvexHalfspaceNeighborhood

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsFinitePL.exists_first_height_cap_ball_with_exterior_zero
    {s : Set E} {T : Set F} {e : s ≃ₜ frontier T} (he : e.IsFinitePL)
    (hT : IsCompact T) (hTcv : Convex ℝ T) (hTne : (interior T).Nonempty)
    (hdimF : Module.finrank ℝ F = 3) (hdimE : Module.finrank ℝ E = 3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C : Set E} (hC : IsCompact C) (hCcv : Convex ℝ C)
    (hKC : K.space = C) (hC0 : (0 : E) ∈ interior C)
    (h0s : (0 : E) ∈ s) (A : E →ₗ[ℝ] ℝ) (hA : A ≠ 0)
    (hmin : ∀ x ∈ s, 0 ≤ A x) (hzero : s ∩ {x | A x = 0} = {0})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ β ∈ Ioo (0 : ℝ) ε, ∃ d : Set E,
      IsFinitePLBallPair (ℝ × ℝ) d (s ∩ {x | A x = β}) ∧
      (∀ x ∈ d, A x = β) ∧ d ∩ s = s ∩ {x | A x = β} ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (convexJoin ℝ {0} d)
        (d ∪ (s ∩ {x | A x ≤ β})) ∧
      convexJoin ℝ {0} d ∩ s = s ∩ {x | A x ≤ β} ∧
      convexJoin ℝ {0} d ⊆ {x | A x ∈ Icc 0 β} ∧
      d ⊆ interior C ∧ convexJoin ℝ {0} d ⊆ interior C ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
        (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior (convexJoin ℝ {0} d) ×ˢ {1})
        ((d ∪ (s ∩ {x | A x ≤ β})) ×ˢ {(1 : ℝ)}) := by
  let c : E ≃L[ℝ] (Fin 3 → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [hdimE])
  obtain ⟨Q0, L, _, hQ0, hQ0cv, hQ00, hQ0C, hL, hQ0rep, _, _⟩ :=
    isOpen_interior.exists_small_convex_halfspace_frontier hC0 c
  obtain ⟨β, hβ, d, hd, hdplane, hdcontact, hball, hcontact, hheight, hdQ0, hconeQ0⟩ :=
    he.exists_local_first_height_cap_ball hT hTcv hTne hdimF hdimE h0s A.toAffineMap
      (map_zero A) hmin hzero isOpen_interior hQ0cv.interior hQ00 hε
  simp only [LinearMap.coe_toAffineMap] at hd hdplane hdcontact hball hcontact hheight
  obtain ⟨M, J, hM, hQrep, hQ, hQcv, hQzero, hJ, hJQ, htop, p, hpQ, hpA⟩ :=
    hQ0.exists_positive_height_cut_frontier hQ0cv L hL hQ0rep A hA hβ.1
  let Q := Q0 ∩ {x | A x ≤ β}
  have hdQ : d ⊆ frontier Q := by
    intro x hx
    exact htop ⟨interior_subset (hdQ0 hx), hdplane x hx⟩
  have hpout : p ∉ d := by
    intro hp
    rw [hdplane p hp] at hpA
    exact hβ.1.not_gt hpA
  have hQC : Q ⊆ interior C := inter_subset_left.trans hQ0C
  have hexterior := K.isFinitePLBallPair_convexFrontierCone_cylinderExterior
    J hK hJ hQ hC hQcv hCcv hQzero hQC hKC hJQ hdimE M hM hQrep hd hdQ
      ⟨p, hpQ, hpout⟩
  have hconeball := hd.convexJoin_zero_of_subset_frontier hQcv hQzero hdQ
  have hmodeldim : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = Module.finrank ℝ E := by
    simp [Module.finrank_prod, hdimE]
  have hboundary : d ∪ convexJoin ℝ {0} (s ∩ {x | A x = β}) =
      d ∪ (s ∩ {x | A x ≤ β}) :=
    (hconeball.frontier_eq_of_finrank_eq hmodeldim).symm.trans
      (hball.frontier_eq_of_finrank_eq hmodeldim)
  rw [hboundary] at hexterior
  exact ⟨β, hβ, d, hd, hdplane, hdcontact, hball, hcontact, hheight,
    hdQ0.trans (interior_subset.trans hQ0C),
    hconeQ0.trans (interior_subset.trans hQ0C), hexterior⟩

end Homeomorph
