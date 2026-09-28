import PoincareConjecture.Proofs.M76.Triangulation.AlexanderConvexSupportSplit












set_option autoImplicit false

open Set Geometry

namespace Geometry.AlexanderSectionProfile

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]







theorem exists_recursive_sphere_split_in_prescribed_region
    (W : AlexanderSectionProfile E) (hdim : Module.finrank ℝ E = 3)
    (hbranching : W.HasBranchingCollars)
    (hnonisolated : W.HasNonisolatedHeightSigns)
    (hevents : W.HasFiniteHeightSignEvents) (c : ℝ) (hcharge : W.charge c ≠ 0)
    {D : Set F} (hD : IsCompact D) (hcv : Convex ℝ D)
    (hne : (interior D).Nonempty) (hdimD : Module.finrank ℝ F = 3)
    (e : W.carrier ≃ₜ frontier D) (he : e.IsFinitePL)
    {C : Set E} (hC : Convex ℝ C) (hWC : W.carrier ⊆ interior C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : E, W.height.linear v = 1 ∧ ∃ d s s' rim : Set E,
      IsFinitePLBallPair (ℝ × ℝ) d rim ∧
      IsFinitePLBallPair (ℝ × ℝ) s rim ∧
      IsFinitePLBallPair (ℝ × ℝ) s' rim ∧
      d ⊆ {x | W.height x = c} ∧ d ∩ W.carrier = rim ∧
      s ∪ s' = W.carrier ∧ s ∩ s' = rim ∧
      s ∩ d = rim ∧ s' ∩ d = rim ∧ d ⊆ interior C ∧
      ∃ δ : ℝ, δ ∈ Ioo 0 ε ∧ ∃ H G : E ≃ₜ E,
        (∀ K : SimplicialComplex ℝ E, K.faces.Finite →
          FinitePiecewiseAffineOn (H : E → E) K.space) ∧
        (∀ K : SimplicialComplex ℝ E, K.faces.Finite →
          FinitePiecewiseAffineOn (G : E → E) K.space) ∧
        (∀ x, x ∉ interior C → H x = x ∧ G x = x) ∧
        (∀ x, δ ≤ |W.height x - c| → H x = x ∧ G x = x) ∧
        H '' C = C ∧ G '' C = C ∧
        ∃ L R : AlexanderSectionProfile E,
          L.carrier = H '' (s ∪ d) ∧ R.carrier = G '' (s' ∪ d) ∧
          L.height = W.height - AffineMap.const ℝ E c ∧
          R.height = W.height - AffineMap.const ℝ E c ∧
          L.carrier ⊆ interior C ∧ R.carrier ⊆ interior C ∧
          L.complexity + R.complexity < W.complexity ∧
          L.HasBranchingCollars ∧ R.HasBranchingCollars ∧
          L.HasNonisolatedHeightSigns ∧ R.HasNonisolatedHeightSigns ∧
          L.HasFiniteHeightSignEvents ∧ R.HasFiniteHeightSignEvents ∧
          (∃ eL : L.carrier ≃ₜ frontier (TriangularRoofModel.halfBall 1), eL.IsFinitePL) ∧
          (∃ eR : R.carrier ≃ₜ frontier (TriangularRoofModel.halfBall 1), eR.IsFinitePL) := by
  have hzero : (W.recenter c).charge 0 ≠ 0 := by
    simpa only [recenter_charge_apply, zero_add] using hcharge
  obtain ⟨v, hv, d, s, s', rim, hd, hs, hs', hdplane, hcap, hss, hinter,
      hsd, hs'd, hdC, δ, hδ, H, G, hglobalH, hglobalG, hfix, hslab, _, _,
      L, R, hL, hR, hLA, hRA, hLC, hRC, hdecrease, hLbranch, hRbranch,
      hLsigns, hRsigns, hLevents, hRevents, hmodelL, hmodelR⟩ :=
    (W.recenter c).exists_recursive_sphere_split_in_convex_open_at_zero hdim
      (hbranching.recenter c) (hnonisolated.recenter c) (hevents.recenter c) hzero
      hD hcv hne hdimD e he isOpen_interior hC.interior hWC hε
  have hHC : H '' C = C := H.image_eq_self_of_eqOn_compl
    (fun x hx => (hfix x (fun hi => hx (interior_subset hi))).1)
  have hGC : G '' C = C := G.image_eq_self_of_eqOn_compl
    (fun x hx => (hfix x (fun hi => hx (interior_subset hi))).2)
  have hv' : W.height.linear v = 1 := by
    simpa only [recenter, AffineMap.sub_linear, AffineMap.const_linear, sub_zero] using hv
  refine ⟨v, hv', d, s, s', rim, hd, hs, hs', ?_, hcap, hss, hinter,
    hsd, hs'd, hdC, δ, hδ, H, G, hglobalH, hglobalG, hfix, ?_, hHC, hGC,
    L, R, hL, hR, hLA, hRA, hLC, hRC, ?_, hLbranch, hRbranch,
    hLsigns, hRsigns, hLevents, hRevents, hmodelL, hmodelR⟩
  · simpa only [recenter_height_apply, sub_eq_zero] using hdplane
  · exact hslab
  · simpa only [complexity_recenter] using hdecrease

end Geometry.AlexanderSectionProfile
