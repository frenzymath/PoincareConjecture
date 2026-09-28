import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.FinitePLImageFaceBounds
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.PLSurfaceCount

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem finitePL_ball_surfaceEulerCount
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s r : Set E} (hs : IsFinitePLBallPair V s r) (hdim : Module.finrank ℝ V ≤ 2)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKs : K.space = s) :
    (∀ a ∈ K.faces, a.card ≤ 3) ∧ K.surfaceEulerCount = 1 := by
  classical
  obtain ⟨_,C,hC,hcv,hne,H,hH,_⟩ := hs
  obtain ⟨f,hf,hfH⟩ := hH.symm
  obtain ⟨L,hL,hLC,hLf⟩ := hf
  have hf : FinitePiecewiseAffineOn f L.space := ⟨L,hL,rfl,hLf⟩
  have hfi : InjOn f L.space := by
    intro x hx y hy he
    exact congrArg Subtype.val (H.symm.injective (Subtype.ext
      ((hfH ⟨x,hLC.subset hx⟩).trans (he.trans (hfH ⟨y,hLC.subset hy⟩).symm))))
  have himage : f '' L.space = K.space := by
    rw [hKs]
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (hfH ⟨x,hLC.subset hx⟩) ▸ (H.symm ⟨x,hLC.subset hx⟩).property
    · intro hy
      let x := H ⟨y,hy⟩
      exact ⟨x,hLC.symm.subset x.property,(hfH x).symm.trans
        (congrArg Subtype.val (H.symm_apply_apply _))⟩
  have hdimL : ∀ a ∈ L.faces, a.card ≤ 3 := by
    intro a ha
    have h := (L.indep ha).card_le_finrank_succ.trans
      (Nat.add_le_add_right ((Submodule.finrank_le _).trans hdim) 1)
    simpa only [Fintype.card_coe] using h
  have hdimK := hf.face_card_le_of_image hL hdimL K himage.symm.subset
  have hcountL : L.surfaceEulerCount = 1 := by
    apply L.surfaceEulerCount_eq_one_of_convex_low_dimension hL (hLC.symm ▸ hcv)
      (hLC.symm ▸ hne.mono interior_subset) ⊤ (subset_univ _) ?_
    exact (Submodule.finrank_le _).trans hdim
  exact ⟨hdimK,(hf.surfaceEulerCount_eq_of_injOn hL hK hdimL hdimK hfi himage).symm.trans hcountL⟩

end PoincareConjecture.M76.PrismBelt
