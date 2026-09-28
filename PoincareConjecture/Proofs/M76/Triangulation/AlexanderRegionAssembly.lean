import PoincareConjecture.Proofs.M76.Triangulation.AlexanderRegionOpenAttachment
import PoincareConjecture.Proofs.M76.Triangulation.AlexanderRegionOpenExcision











set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem exists_alexander_uncapped_region_balls {b c d q U V D : Set E}
    (hdim : Module.finrank ℝ E = 3)
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q)
    (hc : IsFinitePLBallPair (ℝ × ℝ) c q)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hbc : b ∩ c = q) (hbd : b ∩ d = q) (hcd : c ∩ d = q)
    (A : E →ᵃ[ℝ] ℝ) (v : E) (hv : 0 < A.linear v) {a : ℝ}
    (hdplane : d ⊆ {x | A x = a})
    (hU : IsOpen U) (hV : IsOpen V)
    (hUD : closure U ⊆ interior D) (hVD : closure V ⊆ interior D)
    (hUf : frontier U = b ∪ d) (hVf : frontier V = c ∪ d)
    (hUB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure U) (b ∪ d))
    (hVB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure V) (c ∪ d))
    (hUE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ U ×ˢ {1}) ((b ∪ d) ×ˢ {1}))
    (hVE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ V ×ˢ {1}) ((c ∪ d) ×ˢ {1}))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hD : IsCompact D) (hcv : Convex ℝ D) (hne : (interior D).Nonempty)
    (hKD : K.space = D) :
    ∃ W : Set E, IsOpen W ∧ IsConnected W ∧ frontier W = b ∪ c ∧
      closure W ⊆ interior D ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure W) (b ∪ c) ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
        (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ W ×ˢ {1}) ((b ∪ c) ×ˢ {1}) := by
  have hmodel : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = Module.finrank ℝ E := by
    simp [Module.finrank_prod, hdim]
  have hUreg : interior (closure U) = U := by
    rw [hUB.interior_eq_sdiff_of_finrank_eq hmodel, ← hUf,
      closure_sdiff_frontier, hU.interior_eq]
  have hVreg : interior (closure V) = V := by
    rw [hVB.interior_eq_sdiff_of_finrank_eq hmodel, ← hVf,
      closure_sdiff_frontier, hV.interior_eq]
  have hUc : IsConnected U := hUreg ▸ hUB.isConnected_interior_of_finrank_eq hmodel
  have hVc : IsConnected V := hVreg ▸ hVB.isConnected_interior_of_finrank_eq hmodel
  have hUb : Bornology.IsBounded U := hUB.isCompact.isBounded.subset subset_closure
  have hVb : Bornology.IsBounded V := hVB.isCompact.isBounded.subset subset_closure
  rcases alexander_bounded_region_incidence_open hb hc hbc hbd hcd A v hv hdplane
    hU hV hUb hVb hUc hVc hUf hVf with hinter | hUV | hVU
  · obtain ⟨hWc, hWf, hWB, hWE⟩ := alexander_attached_open_region_balls
      hdim hb hc hd hbd hcd hU hV hUD hVD hUf hVf hinter hUB hVB hUE hVE
      K hK hD hcv hne hKD
    refine ⟨interior (closure U ∪ closure V), isOpen_interior, hWc, hWf,
      ?_, hWB, hWE⟩
    exact (closure_minimal interior_subset (isClosed_closure.union isClosed_closure)).trans
      (union_subset hUD hVD)
  · obtain ⟨hW, hWc, hWf, hWB, hWE⟩ := alexander_nested_open_region_balls
      hdim hb hc hd hbc hbd hcd hU hV hUV hVD hUf hVf hUB hVB hUE hVE
    exact ⟨V \ closure U, hW, hWc, hWf, (closure_mono sdiff_subset).trans hVD, hWB, hWE⟩
  · obtain ⟨hW, hWc, hWf, hWB, hWE⟩ := alexander_nested_open_region_balls
      hdim hc hb hd ((inter_comm _ _).trans hbc) hcd hbd hV hU hVU hUD
      hVf hUf hVB hUB hVE hUE
    rw [union_comm c b] at hWf hWB hWE
    exact ⟨U \ closure V, hW, hWc, hWf, (closure_mono sdiff_subset).trans hUD, hWB, hWE⟩

end Set
