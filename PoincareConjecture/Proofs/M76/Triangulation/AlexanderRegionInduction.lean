import PoincareConjecture.Proofs.M76.Triangulation.AlexanderRegionCertificates
import PoincareConjecture.Proofs.M76.Triangulation.AlexanderPrescribedRegionSplit











set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace Geometry.AlexanderSectionProfile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem hasAlexanderRegionBalls_of_zero_charge_supplier
    (hdim : Module.finrank ℝ E = 3)
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hne : (interior C).Nonempty)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKC : K.space = C)
    (base : ∀ W : AlexanderSectionProfile E,
      W.HasNonisolatedHeightSigns → W.HasFiniteHeightSignEvents →
      (∀ c, W.charge c = 0) → W.carrier ⊆ interior C →
      (∃ e : W.carrier ≃ₜ frontier (halfBall 1), e.IsFinitePL) →
      HasAlexanderRegionBalls W.carrier C)
    (W : AlexanderSectionProfile E) (hbranching : W.HasBranchingCollars)
    (hnonisolated : W.HasNonisolatedHeightSigns)
    (hevents : W.HasFiniteHeightSignEvents) (hWC : W.carrier ⊆ interior C)
    (hmodel : ∃ e : W.carrier ≃ₜ frontier (halfBall 1), e.IsFinitePL) :
    HasAlexanderRegionBalls W.carrier C := by
  let Admissible (P : AlexanderSectionProfile E) : Prop :=
    P.HasBranchingCollars ∧ P.HasNonisolatedHeightSigns ∧
      P.HasFiniteHeightSignEvents ∧ P.carrier ⊆ interior C ∧
      ∃ e : P.carrier ≃ₜ frontier (halfBall 1), e.IsFinitePL
  have hhalfCv : Convex ℝ (halfBall 1) := by
    rw [halfBall_eq_halfspaces]
    simp only [ofPred_forall]
    exact convex_iInter fun i => (convex_Iic 0).affine_preimage (halfBallForms 1 i)
  apply binary_induction (Admissible := Admissible)
    (Q := fun S => HasAlexanderRegionBalls S C) ?_ ?_ W
    ⟨hbranching, hnonisolated, hevents, hWC, hmodel⟩
  · rintro P ⟨_, hPsigns, hPevents, hPC, hPmodel⟩ hzero
    exact base P hPsigns hPevents hzero hPC hPmodel
  · rintro P ⟨hPbranch, hPsigns, hPevents, hPC, e, he⟩ c hc
    obtain ⟨v, hv, d, s, s', rim, hd, hs, hs', hdplane, _, hss, hinter,
        hsd, hs'd, _, _, _, H, G, hglobalH, hglobalG, _, _, hHC, hGC,
        L, R, hL, hR, _, _, hLC, hRC, hdecrease, hLbranch, hRbranch,
        hLsigns, hRsigns, hLevents, hRevents, hmodelL, hmodelR⟩ :=
      P.exists_recursive_sphere_split_in_prescribed_region hdim
        hPbranch hPsigns hPevents c hc (isCompact_halfBall (Or.inl rfl))
        hhalfCv (interior_halfBall_nonempty (Or.inl rfl))
        (by simp [Module.finrank_prod]) e he hcv hPC zero_lt_one
    refine ⟨L, R, ⟨hLbranch, hLsigns, hLevents, hLC, hmodelL⟩,
      ⟨hRbranch, hRsigns, hRevents, hRC, hmodelR⟩, hdecrease, ?_⟩
    intro hLB hRB
    have hleft : HasAlexanderRegionBalls (H '' (s ∪ d)) C := hL ▸ hLB
    have hright : HasAlexanderRegionBalls (G '' (s' ∪ d)) C := hR ▸ hRB
    have hparent := HasAlexanderRegionBalls.of_deformed_caps hdim hs hs' hd
      hinter hsd hs'd P.height v (by rw [hv]; exact zero_lt_one) hdplane
      H G hglobalH hglobalG hHC hGC hleft hright K hK hC hcv hne hKC
    exact hss ▸ hparent

end Geometry.AlexanderSectionProfile
