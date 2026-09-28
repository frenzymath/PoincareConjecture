import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.BoundaryCount.TetrahedronBoundaryCount
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalTetrahedronBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets








set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem finitePL_ball_boundary_surfaceEulerCount
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (K : SimplicialComplex ℝ E) {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    {B R : Set F} (hB : IsFinitePLBallPair (Fin 3 → ℝ) B R)
    (L : SimplicialComplex ℝ F) (hL : L.faces.Finite) (hLR : L.space = R) :
    (∀ a ∈ L.faces, a.card ≤ 3) ∧ L.surfaceEulerCount = 2 := by
  classical
  have hT := isFinitePLBallPair_independent_tetrahedron t (K.indep ht) ht4
  obtain ⟨J,hJ,hJr,hdimJ,hcountJ⟩ := exists_tetrahedron_boundary_count_model K ht ht4
  obtain ⟨H,hH,hHr⟩ := hT.exists_homeomorph hB
  let e := H.restrictSubsets hT.1 hB.1 hHr
  have he : e.IsFinitePL := hH.restrictSubsets hT.1 hB.1 hHr J hJ hJr
  obtain ⟨f,hf,hfe⟩ := he
  have hfJ : FinitePiecewiseAffineOn f J.space := hJr.symm ▸ hf
  have hfi : InjOn f J.space := by
    intro x hx y hy heq
    exact congrArg Subtype.val (e.injective (Subtype.ext
      ((hfe ⟨x,hJr.subset hx⟩).trans (heq.trans (hfe ⟨y,hJr.subset hy⟩).symm))))
  have himage : f '' J.space = L.space := by
    rw [hLR]
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (hfe ⟨x,hJr.subset hx⟩) ▸ (e ⟨x,hJr.subset hx⟩).property
    · intro hy
      let x := e.symm ⟨y,hy⟩
      exact ⟨x,hJr.symm.subset x.property,(hfe x).symm.trans
        (congrArg Subtype.val (e.apply_symm_apply _))⟩
  have hdimL := hfJ.face_card_le_of_image hJ hdimJ L himage.symm.subset
  exact ⟨hdimL,(hfJ.surfaceEulerCount_eq_of_injOn hJ hL hdimJ hdimL hfi himage).symm.trans
    hcountJ⟩

end PoincareConjecture.M76.PrismBelt
