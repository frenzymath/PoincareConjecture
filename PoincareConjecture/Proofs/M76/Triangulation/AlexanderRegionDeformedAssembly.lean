import PoincareConjecture.Proofs.M76.Triangulation.AlexanderRegionAssembly
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionPullback











set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem exists_alexander_region_balls_of_deformed_caps {b c d q U V D : Set E}
    (hdim : Module.finrank ℝ E = 3)
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q)
    (hc : IsFinitePLBallPair (ℝ × ℝ) c q)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hbc : b ∩ c = q) (hbd : b ∩ d = q) (hcd : c ∩ d = q)
    (A : E →ᵃ[ℝ] ℝ) (v : E) (hv : 0 < A.linear v) {a : ℝ}
    (hdplane : d ⊆ {x | A x = a})
    (H G : E ≃ₜ E)
    (hH : ∀ (L : SimplicialComplex ℝ E), L.faces.Finite →
      FinitePiecewiseAffineOn (H : E → E) L.space)
    (hG : ∀ (L : SimplicialComplex ℝ E), L.faces.Finite →
      FinitePiecewiseAffineOn (G : E → E) L.space)
    (hHD : H '' D = D) (hGD : G '' D = D)
    (hU : IsOpen U) (hV : IsOpen V)
    (hUD : closure U ⊆ interior D) (hVD : closure V ⊆ interior D)
    (hUf : frontier U = H '' (b ∪ d)) (hVf : frontier V = G '' (c ∪ d))
    (hUB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure U) (H '' (b ∪ d)))
    (hVB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure V) (G '' (c ∪ d)))
    (hUE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ U ×ˢ {1}) ((H '' (b ∪ d)) ×ˢ {1}))
    (hVE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ V ×ˢ {1}) ((G '' (c ∪ d)) ×ˢ {1}))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hD : IsCompact D) (hcv : Convex ℝ D) (hne : (interior D).Nonempty)
    (hKD : K.space = D) :
    ∃ W : Set E, IsOpen W ∧ IsConnected W ∧ frontier W = b ∪ c ∧
      closure W ⊆ interior D ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure W) (b ∪ c) ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
        (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ W ×ˢ {1}) ((b ∪ c) ×ˢ {1}) := by
  obtain ⟨hU', hUf', hUD', hUB', hUE'⟩ :=
    H.pullback_spherical_region_balls hH hHD hU hUD hUf hUB hUE
  obtain ⟨hV', hVf', hVD', hVB', hVE'⟩ :=
    G.pullback_spherical_region_balls hG hGD hV hVD hVf hVB hVE
  exact exists_alexander_uncapped_region_balls hdim hb hc hd hbc hbd hcd
    A v hv hdplane hU' hV' hUD' hVD' hUf' hVf' hUB' hVB' hUE' hVE'
    K hK hD hcv hne hKD

end Set
