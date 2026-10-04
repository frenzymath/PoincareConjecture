import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Regions.AlexanderRegionDeformedAssembly

/-!
# Actual paired region certificates for Alexander induction

The property retains one literal open bounded region and the
complete complementary closed side in a fixed outer cylinder.
The actual same-map cap reconstruction preserves this property.
See Alexander 1924, pp. 6--8 and M76 derivations 247 and 278c.
-/

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual open region of a surface has both finite PL
three-ball certificates inside one prescribed outer region.
The second ball is the literal closed complementary side
in that outer cylinder's frontier. See Alexander pp. 7--8
and M76 derivation 278c. -/
def HasAlexanderRegionBalls (S C : Set E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ IsConnected U ∧ frontier U = S ∧
    closure U ⊆ interior C ∧
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure U) S ∧
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ U ×ˢ {1}) (S ×ˢ {1})

variable [FiniteDimensional ℝ E]

/-- Two actual same-map capped region certificates give
the uncapped certificate in that same outer body. The
checked reconstruction derives all bounded-region incidence
internally. See Alexander pp. 7--8 and M76 derivation 278c. -/
theorem HasAlexanderRegionBalls.of_deformed_caps {b c d rim C : Set E}
    (hdim : Module.finrank ℝ E = 3)
    (hb : IsFinitePLBallPair (ℝ × ℝ) b rim)
    (hc : IsFinitePLBallPair (ℝ × ℝ) c rim)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d rim)
    (hbc : b ∩ c = rim) (hbd : b ∩ d = rim) (hcd : c ∩ d = rim)
    (A : E →ᵃ[ℝ] ℝ) (v : E) (hv : 0 < A.linear v) {a : ℝ}
    (hdplane : d ⊆ {x | A x = a})
    (H G : E ≃ₜ E)
    (hH : ∀ K : SimplicialComplex ℝ E, K.faces.Finite →
      FinitePiecewiseAffineOn (H : E → E) K.space)
    (hG : ∀ K : SimplicialComplex ℝ E, K.faces.Finite →
      FinitePiecewiseAffineOn (G : E → E) K.space)
    (hHC : H '' C = C) (hGC : G '' C = C)
    (hleft : HasAlexanderRegionBalls (H '' (b ∪ d)) C)
    (hright : HasAlexanderRegionBalls (G '' (c ∪ d)) C)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hKC : K.space = C) : HasAlexanderRegionBalls (b ∪ c) C := by
  obtain ⟨U, hU, _, hUf, hUC, hUB, hUE⟩ := hleft
  obtain ⟨V, hV, _, hVf, hVC, hVB, hVE⟩ := hright
  exact exists_alexander_region_balls_of_deformed_caps hdim hb hc hd hbc hbd hcd
    A v hv hdplane H G hH hG hHC hGC hU hV hUC hVC hUf hVf hUB hVB hUE hVE
    K hK hC hcv hne hKC

end Set
