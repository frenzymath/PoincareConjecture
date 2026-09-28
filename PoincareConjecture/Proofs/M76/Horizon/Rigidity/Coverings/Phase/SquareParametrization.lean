import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.PeriodicSquarePL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusSquareMap
import PoincareConjecture.Proofs.M76.Rigidity.StandardHierarchyParameterPL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.Adjustments.PhaseMap








set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "p" => (4 * (16 : ℝ))
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_PL_torus_parametrization_of_square_map
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d : κ → OpenPartialHomeomorph X0 (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    (u : ℝ × ℝ → E) (hu : FinitePiecewiseAffineOn u (Icc 0 p ×ˢ Icc 0 p))
    (himage : u '' (Icc 0 p ×ˢ Icc 0 p) = J.space)
    (hfib : ∀ z w : PeriodicSquare.Square p,
      u (z.1, z.2) = u (w.1, w.2) ↔
        PeriodicSquare.projection p z = PeriodicSquare.projection p w) :
    ∃ h : (C0 × C0) ≃ₜ J.space,
      (∀ z : PeriodicSquare.Square p,
        (h (PeriodicSquare.projection p z) : E) = u (z.1, z.2)) ∧
      ∀ theta : C0, PolyhedralPLInCharts d
        (hamiltonZeroCollarPhaseTarget J ⟨h.symm, h.symm.continuous⟩ theta) J.space := by
  classical
  let v : PeriodicSquare.Square p → ℝ × ℝ := fun z => (z.1, z.2)
  have hv : Continuous v := continuous_subtype_val.prodMap continuous_subtype_val
  have hvS (z : PeriodicSquare.Square p) : v z ∈ Icc 0 p ×ˢ Icc 0 p :=
    ⟨z.1.property, z.2.property⟩
  let f : C(PeriodicSquare.Square p, J.space) :=
    ⟨fun z => ⟨u (v z), himage.subset ⟨v z, hvS z, rfl⟩⟩,
      (hu.continuousOn.comp_continuous hv hvS).subtype_mk _⟩
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨z, hz, he⟩ := himage.symm.subset x.property
    exact ⟨(⟨z.1, hz.1⟩, ⟨z.2, hz.2⟩), Subtype.ext he⟩
  have hffib (z w : PeriodicSquare.Square p) :
      f z = f w ↔ Relation.EqvGen (PeriodicSquare.SidePair p) z w := by
    rw [← PeriodicSquare.projection_eq_iff]
    exact Subtype.ext_iff.trans (hfib z w)
  obtain ⟨h, hval⟩ := PeriodicSquare.exists_homeomorph_of_square_map p f hsurj hffib
  refine ⟨h, fun z => congrArg Subtype.val (hval z), ?_⟩
  intro theta
  let F := hamiltonZeroCollarPhaseTarget J ⟨h.symm, h.symm.continuous⟩ theta
  have hF : ContinuousOn F J.space := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hh : Continuous (fun x : J.space => (Q0).symm (h.symm x, theta)) :=
      (Q0).symm.continuous.comp (h.symm.continuous.prodMk continuous_const)
    exact hh.congr (fun x => by simp [F, hamiltonZeroCollarPhaseTarget])
  apply PeriodicSquare.polyhedralPL_descent p d hd.domain.cover hd.domain.compatible J hJ
    u hu himage (fun z w he => (hfib z w).mp he) F hF
  obtain ⟨t, ht, htval⟩ := AddCircle.eq_coe_Ico theta
  have hball := (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < p)).prod
    (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < p))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hball
  let a : (ℝ × ℝ) →ᴬ[ℝ] ((ℝ × ℝ) × ℝ) :=
    (ContinuousAffineMap.id ℝ (ℝ × ℝ)).prod (ContinuousAffineMap.const ℝ (ℝ × ℝ) t)
  have ha : FinitePiecewiseAffineOn a K.space :=
    (K.affineOnFaces_affine a).finitePiecewiseAffineOn hK
  have hamap : MapsTo a K.space ((Icc 0 p ×ˢ Icc 0 p) ×ˢ Icc 0 p) :=
    fun z hz => ⟨hKs.subset hz, ht.1, ht.2.le⟩
  have hPL := hd.polyhedralPL_zeroCutParameter.comp_finitePiecewiseAffineOn K hK ha hamap
  rw [← hKs]
  apply hPL.congr
  intro z hz
  have hzS := hKs.subset hz
  let w : PeriodicSquare.Square p := (⟨z.1, hzS.1⟩, ⟨z.2, hzS.2⟩)
  have hzu : u z ∈ J.space := himage.subset ⟨z, hzS, rfl⟩
  have hwinv : h.symm ⟨u z, hzu⟩ = PeriodicSquare.projection p w := by
    apply h.injective
    rw [h.apply_symm_apply, hval]
    rfl
  simp only [Function.comp_apply, F, hamiltonZeroCollarPhaseTarget, dif_pos hzu,
    ContinuousMap.coe_mk, hwinv]
  apply (Q0).injective
  rw [Homeomorph.apply_symm_apply]
  change (((z.1 : C0), (z.2 : C0)), (t : C0)) = _
  exact Prod.ext rfl htval




theorem exists_PL_torus_parametrization_of_source_square_map
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {d : κ → OpenPartialHomeomorph X0 (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {K : SimplicialComplex ℝ E} (hK : K.faces.Finite)
    (M : PoincareConjecture.M76.PeriodicSquare.SourceSquareMap p K) :
    ∃ h : (C0 × C0) ≃ₜ K.space,
      (∀ z : PoincareConjecture.M76.PeriodicSquare.Square p,
        (h (PoincareConjecture.M76.PeriodicSquare.projection p z) : E) = M.map z) ∧
      ∀ theta : C0, PolyhedralPLInCharts d
        (hamiltonZeroCollarPhaseTarget K ⟨h.symm, h.symm.continuous⟩ theta) K.space := by
  obtain ⟨u, hu, huv⟩ := M.finite_piecewise_affine
  have himage : u '' (Icc 0 p ×ˢ Icc 0 p) = K.space := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      let q : PeriodicSquare.Square p := (⟨z.1, hz.1⟩, ⟨z.2, hz.2⟩)
      rw [show u z = (M.map q : E) by simpa [q] using huv q]
      exact (M.map q).property
    · intro hy
      obtain ⟨z, hz⟩ := M.surjective ⟨y, hy⟩
      refine ⟨(z.1, z.2), ⟨z.1.property, z.2.property⟩, ?_⟩
      calc
        u (z.1, z.2) = (M.map z : E) := huv z
        _ = y := congrArg Subtype.val hz
  have hfib : ∀ z w : PeriodicSquare.Square p,
      u (z.1, z.2) = u (w.1, w.2) ↔
        PeriodicSquare.projection p z = PeriodicSquare.projection p w := by
    intro z w
    have hcoerce : (M.map z : E) = (M.map w : E) ↔ M.map z = M.map w := by
      constructor
      · intro h
        exact Subtype.ext h
      · exact congrArg Subtype.val
    rw [huv z, huv w, hcoerce, M.fibers, PeriodicSquare.projection_eq_iff]
  obtain ⟨h, hvalue, hPL⟩ := exists_PL_torus_parametrization_of_square_map
    hd K hK u hu himage hfib
  refine ⟨h, ?_, hPL⟩
  intro z
  exact (hvalue z).trans (huv z)

end PoincareConjecture.M76
