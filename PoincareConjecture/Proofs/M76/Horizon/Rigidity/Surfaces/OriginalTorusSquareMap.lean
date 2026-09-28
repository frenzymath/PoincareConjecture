import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusPeriodicSquareBoundary
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph












set_option autoImplicit false

open Set Topology Geometry

namespace PoincareConjecture.M76.PeriodicSquare

variable (p : ℝ) [Fact (0 < p)]

def squareCarrier : Set (ℝ × ℝ) := Icc (0 : ℝ) p ×ˢ Icc (0 : ℝ) p

def squareCarrierEquiv : Square p ≃ₜ (squareCarrier p) :=
  { toFun := fun z => ⟨(z.1, z.2), z.1.property, z.2.property⟩
    invFun := fun z =>
      (⟨z.1.1, z.2.1.1, z.2.1.2⟩, ⟨z.1.2, z.2.2.1, z.2.2.2⟩)
    left_inv := by
      intro z
      rfl
    right_inv := by
      intro z
      apply Subtype.ext
      rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }





structure SourceSquareMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : SimplicialComplex ℝ E) where
  map : C(Square p, K.space)
  surjective : Function.Surjective map
  fibers : ∀ z w, map z = map w ↔ Relation.EqvGen (SidePair p) z w
  finite_piecewise_affine :
      ∃ F : (ℝ × ℝ) → E,
      FinitePiecewiseAffineOn F (squareCarrier p) ∧
        ∀ z : Square p, F (z.1, z.2) = (map z : E)




noncomputable def SourceSquareMap.of_closed_filling
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : SimplicialComplex ℝ E}
    (f : C(Square p, K.space))
    (hsurjective : Function.Surjective f)
    (hside : ∀ (i : Fin 2) (t : Icc (0 : ℝ) p),
      f (sidePoint p i false t) = f (sidePoint p i true t))
    (hno_extra : ∀ z w, f z = f w → projection p z = projection p w)
    (hfpa : ∃ F : (ℝ × ℝ) → E,
      FinitePiecewiseAffineOn F (squareCarrier p) ∧
        ∀ z : Square p, F (z.1, z.2) = (f z : E)) :
    SourceSquareMap p K := by
  have hpair : ∀ z w : Square p, SidePair p z w → f z = f w := by
    intro z w hzw
    rcases hzw with ⟨hz, hw, ht⟩ | ⟨hz, hw, hs⟩
    · have hz' : z = sidePoint p 1 false z.2 := by
        apply Prod.ext
        · apply Subtype.ext
          exact hz
        · rfl
      have hw' : w = sidePoint p 1 true z.2 := by
        apply Prod.ext
        · apply Subtype.ext
          exact hw
        · exact ht.symm
      rw [hz', hw']
      exact hside 1 z.2
    · have hz' : z = sidePoint p 0 false z.1 := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          exact hz
      have hw' : w = sidePoint p 0 true z.1 := by
        apply Prod.ext
        · exact hs.symm
        · apply Subtype.ext
          exact hw
      rw [hz', hw']
      exact hside 0 z.1
  have hfib : ∀ z w : Square p,
      f z = f w ↔ Relation.EqvGen (SidePair p) z w := by
    intro z w
    constructor
    · intro hzw
      exact (projection_eq_iff p).mp (hno_extra z w hzw)
    · intro hzw
      induction hzw with
      | rel z w h => exact hpair z w h
      | refl z => rfl
      | symm z w h ih => exact ih.symm
      | trans z w v hzw hwv ihzw ihwv => exact ihzw.trans ihwv
  refine { map := f, surjective := hsurjective, fibers := hfib, finite_piecewise_affine := ?_ }
  exact hfpa




noncomputable def SourceSquareMap.of_ambient_closed_filling
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : SimplicialComplex ℝ E}
    (f : C(Square p, K.space))
    (F : (ℝ × ℝ) → E)
    (hF : FinitePiecewiseAffineOn F (squareCarrier p))
    (hvalue : ∀ z : Square p, F (z.1, z.2) = (f z : E))
    (hsurjective : Function.Surjective f)
    (hside : ∀ (i : Fin 2) (t : Icc (0 : ℝ) p),
      F ((sidePoint p i false t).1, (sidePoint p i false t).2) =
        F ((sidePoint p i true t).1, (sidePoint p i true t).2))
    (hno_extra : ∀ z w : Square p,
      F (z.1, z.2) = F (w.1, w.2) → projection p z = projection p w) :
    SourceSquareMap p K := by
  apply SourceSquareMap.of_closed_filling (p := p) f hsurjective
  · intro i t
    apply Subtype.ext
    calc
      (f (sidePoint p i false t) : E) =
          F ((sidePoint p i false t).1, (sidePoint p i false t).2) :=
        (hvalue (sidePoint p i false t)).symm
      _ = F ((sidePoint p i true t).1, (sidePoint p i true t).2) := hside i t
      _ = (f (sidePoint p i true t) : E) := hvalue (sidePoint p i true t)
  · intro z w hzw
    apply hno_extra z w
    calc
      F (z.1, z.2) = (f z : E) := hvalue z
      _ = (f w : E) := congrArg Subtype.val hzw
      _ = F (w.1, w.2) := (hvalue w).symm
  · exact ⟨F, hF, hvalue⟩

noncomputable def SourceSquareMap.of_ambient_family
    {E η : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : η → SimplicialComplex ℝ E}
    (f : ∀ i, C(Square p, (K i).space))
    (F : ∀ i, (ℝ × ℝ) → E)
    (hF : ∀ i, FinitePiecewiseAffineOn (F i) (squareCarrier p))
    (hvalue : ∀ (i : η) (z : Square p), F i (z.1, z.2) = (f i z : E))
    (hsurjective : ∀ i : η, Function.Surjective (f i))
    (hside : ∀ (i : η) (j : Fin 2) (t : Icc (0 : ℝ) p),
      F i ((sidePoint p j false t).1, (sidePoint p j false t).2) =
        F i ((sidePoint p j true t).1, (sidePoint p j true t).2))
    (hno_extra : ∀ (i : η) (z w : Square p),
      F i (z.1, z.2) = F i (w.1, w.2) → projection p z = projection p w) :
    ∀ i, SourceSquareMap p (K i) := by
  intro i
  exact SourceSquareMap.of_ambient_closed_filling (p := p) (f i) (F i)
    (hF i) (hvalue i) (hsurjective i) (hside i) (hno_extra i)

noncomputable def SourceSquareMap.of_ambient_dependent_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {η : Bool → Type*} {K : ∀ s, η s → SimplicialComplex ℝ E}
    (f : ∀ s i, C(Square p, (K s i).space))
    (F : ∀ s i, (ℝ × ℝ) → E)
    (hF : ∀ s i, FinitePiecewiseAffineOn (F s i) (squareCarrier p))
    (hvalue : ∀ (s : Bool) (i : η s) (z : Square p),
      F s i (z.1, z.2) = (f s i z : E))
    (hsurjective : ∀ (s : Bool) (i : η s), Function.Surjective (f s i))
    (hside : ∀ (s : Bool) (i : η s) (j : Fin 2) (t : Icc (0 : ℝ) p),
      F s i ((sidePoint p j false t).1, (sidePoint p j false t).2) =
        F s i ((sidePoint p j true t).1, (sidePoint p j true t).2))
    (hno_extra : ∀ (s : Bool) (i : η s) (z w : Square p),
      F s i (z.1, z.2) = F s i (w.1, w.2) → projection p z = projection p w) :
    ∀ s i, SourceSquareMap p (K s i) := by
  intro s i
  exact SourceSquareMap.of_ambient_closed_filling (p := p) (f s i) (F s i)
    (hF s i) (hvalue s i) (hsurjective s i) (hside s i) (hno_extra s i)





noncomputable def SourceSquareMap.of_torusHomeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : SimplicialComplex ℝ E}
    (h : (AddCircle p × AddCircle p) ≃ₜ K.space)
    (u : ℝ × ℝ → E)
    (hu : FinitePiecewiseAffineOn u (squareCarrier p))
    (hvalue : ∀ z : Square p, u (z.1, z.2) = (h (projection p z) : E)) :
    SourceSquareMap p K := by
  let map : C(Square p, K.space) :=
    ⟨fun z => h (projection p z), h.continuous.comp (projection p).continuous⟩
  have hsurj : Function.Surjective map := by
    intro y
    obtain ⟨z, hz⟩ := surjective_projection p (h.symm y)
    refine ⟨z, ?_⟩
    apply Subtype.ext
    dsimp [map]
    rw [hz, h.apply_symm_apply]
  have hfib (z w : Square p) :
      map z = map w ↔ Relation.EqvGen (SidePair p) z w := by
    change h (projection p z) = h (projection p w) ↔ _
    rw [h.injective.eq_iff, projection_eq_iff p]
  refine { map := map, surjective := hsurj, fibers := hfib, finite_piecewise_affine := ?_ }
  refine ⟨u, hu, ?_⟩
  intro z
  exact hvalue z

theorem SourceSquareMap.map_sidePair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : SimplicialComplex ℝ E} (M : SourceSquareMap p K)
    (i : Fin 2) (t : Icc (0 : ℝ) p) :
    M.map (sidePoint p i false t) = M.map (sidePoint p i true t) := by
  apply (M.fibers _ _).2
  exact Relation.EqvGen.rel _ _ (sidePoint_sidePair p i t)

theorem SourceSquareMap.continuous_side
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : SimplicialComplex ℝ E} (M : SourceSquareMap p K)
    (i : Fin 2) (b : Bool) :
    Continuous (fun t : Icc (0 : ℝ) p => M.map (sidePoint p i b t)) := by
  exact M.map.continuous.comp (continuous_sidePoint p i b)

theorem exists_homeomorph_of_sourceSquareMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : SimplicialComplex ℝ E} (M : SourceSquareMap p K) :
    ∃ h : (AddCircle p × AddCircle p) ≃ₜ K.space,
      ∀ z, h (projection p z) = M.map z := by
  exact exists_homeomorph_of_square_map p M.map M.surjective M.fibers

omit [Fact (0 < p)] in
theorem sourceSquareMap_finite_piecewise_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : SimplicialComplex ℝ E} (M : SourceSquareMap p K) :
    ∃ F : (ℝ × ℝ) → E,
      FinitePiecewiseAffineOn F (squareCarrier p) ∧
        ∀ z : Square p, F (z.1, z.2) = (M.map z : E) :=
  M.finite_piecewise_affine

theorem SourceSquareMap.exists_ambientRepresentative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : SimplicialComplex ℝ E} (M : SourceSquareMap p K) :
    ∃ u : (ℝ × ℝ) → E,
      FinitePiecewiseAffineOn u (squareCarrier p) ∧
        u '' squareCarrier p = K.space ∧
        ∀ z w : Square p,
          u (z.1, z.2) = u (w.1, w.2) ↔
            projection p z = projection p w := by
  obtain ⟨u, hu, huv⟩ := M.finite_piecewise_affine
  refine ⟨u, hu, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      let q : Square p := (⟨z.1, hz.1⟩, ⟨z.2, hz.2⟩)
      rw [show u z = (M.map q : E) by simpa [q] using huv q]
      exact (M.map q).property
    · intro hy
      obtain ⟨z, hz⟩ := M.surjective ⟨y, hy⟩
      refine ⟨(z.1, z.2), ?_, ?_⟩
      · exact ⟨z.1.property, z.2.property⟩
      · calc
          u (z.1, z.2) = (M.map z : E) := huv z
          _ = y := congrArg Subtype.val hz
  · intro z w
    have hcoerce : (M.map z : E) = (M.map w : E) ↔ M.map z = M.map w := by
      constructor
      · intro h
        exact Subtype.ext h
      · exact congrArg Subtype.val
    rw [huv z, huv w, hcoerce, M.fibers, projection_eq_iff p]





theorem SourceSquareMap.exists_family_ambient_data
    {E η : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : η → SimplicialComplex ℝ E}
    (M : ∀ i, SourceSquareMap p (K i)) :
    ∃ (u : η → (ℝ × ℝ → E)),
      (∀ i, FinitePiecewiseAffineOn (u i) (squareCarrier p)) ∧
      (∀ i, u i '' squareCarrier p = (K i).space) ∧
      (∀ i (z w : Square p),
        u i (z.1, z.2) = u i (w.1, w.2) ↔
          projection p z = projection p w) := by
  choose u hu himage hfib using fun i => (M i).exists_ambientRepresentative
  refine ⟨u, hu, himage, ?_⟩
  intro i z w
  exact hfib i z w

theorem SourceSquareMap.exists_dependent_family_ambient_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {η : Bool → Type*} {K : ∀ s, η s → SimplicialComplex ℝ E}
    (M : ∀ s i, SourceSquareMap p (K s i)) :
    ∃ (u : ∀ s i, ℝ × ℝ → E),
      (∀ s i, FinitePiecewiseAffineOn (u s i) (squareCarrier p)) ∧
      (∀ s i, u s i '' squareCarrier p = (K s i).space) ∧
      (∀ s i (z w : Square p),
        u s i (z.1, z.2) = u s i (w.1, w.2) ↔
          projection p z = projection p w) := by
  choose u hu himage hfib using fun s i => (M s i).exists_ambientRepresentative
  refine ⟨u, hu, himage, ?_⟩
  intro s i z w
  exact hfib s i z w

end PoincareConjecture.M76.PeriodicSquare
