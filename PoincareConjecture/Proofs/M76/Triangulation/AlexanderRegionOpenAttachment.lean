import PoincareConjecture.Proofs.M76.Triangulation.AlexanderRegionExteriorExcision
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalComplement











set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem alexander_attached_open_region_balls {b c d q U V D : Set E}
    (hdim : Module.finrank ℝ E = 3)
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q)
    (hc : IsFinitePLBallPair (ℝ × ℝ) c q)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hbd : b ∩ d = q) (hcd : c ∩ d = q)
    (hU : IsOpen U) (hV : IsOpen V)
    (hUD : closure U ⊆ interior D) (hVD : closure V ⊆ interior D)
    (hUf : frontier U = b ∪ d) (hVf : frontier V = c ∪ d)
    (hinter : closure U ∩ closure V = d)
    (hUB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure U) (b ∪ d))
    (hVB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure V) (c ∪ d))
    (hUE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ U ×ˢ {1}) ((b ∪ d) ×ˢ {1}))
    (hVE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ V ×ˢ {1}) ((c ∪ d) ×ˢ {1}))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hD : IsCompact D) (hcv : Convex ℝ D) (hne : (interior D).Nonempty)
    (hKD : K.space = D) :
    IsConnected (interior (closure U ∪ closure V)) ∧
      frontier (interior (closure U ∪ closure V)) = b ∪ c ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
        (closure (interior (closure U ∪ closure V))) (b ∪ c) ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
        (frontier (D ×ˢ Icc (-1 : ℝ) 1) \
          interior (closure U ∪ closure V) ×ˢ {1}) ((b ∪ c) ×ˢ {1}) := by
  have hmodel : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = Module.finrank ℝ E := by
    simp [Module.finrank_prod, hdim]
  have hR := hUB.union_of_ball_disk_attachment hVB hb hc hd hbd hcd hinter
  have hO := alexander_attached_spherical_exterior_ball hdim hb hc hd hbd hcd
    hU hV hUD hVD hUf hVf hinter hUB hVB hUE hVE K hK hD hcv hne hKD
  have hUreg : interior (closure U) = U := by
    rw [hUB.interior_eq_sdiff_of_finrank_eq hmodel, ← hUf,
      closure_sdiff_frontier, hU.interior_eq]
  rw [closure_cylinderExterior_sdiff_top_face hUreg hUD hVD] at hO
  exact ⟨hR.isConnected_interior_of_finrank_eq hmodel,
    hR.frontier_interior_of_finrank_eq hmodel,
    (hR.closure_interior_of_finrank_eq hmodel).symm ▸ hR, hO⟩

end Set
