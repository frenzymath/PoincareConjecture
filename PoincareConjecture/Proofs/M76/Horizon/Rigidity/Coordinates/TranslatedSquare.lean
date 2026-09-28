import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.SourceTorusBand
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.PeriodicSquare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E}

theorem SourceSquareMap.finitePiecewiseAffineOn_halfTranslate
    (M : SourceSquareMap p K) (h : (AddCircle p × AddCircle p) ≃ₜ K.space)
    (hh : ∀ z, h (projection p z) = M.map z) :
    FinitePiecewiseAffineOn
      (fun x : ℝ × ℝ => (h (((x.1 + p / 2 : ℝ) : AddCircle p),
        ((x.2 + p / 2 : ℝ) : AddCircle p)) : E)) (squareCarrier p) := by
  obtain ⟨u, hu, huv⟩ := M.finite_piecewise_affine
  have hp : 0 < p := Fact.out
  let lo (b : Bool) : ℝ := if b then p / 2 else 0
  let hi (b : Bool) : ℝ := if b then p else p / 2
  let shift (b : Bool) : ℝ := if b then -(p / 2) else p / 2
  let T (b : Bool × Bool) := Icc (lo b.1) (hi b.1) ×ˢ Icc (lo b.2) (hi b.2)
  have hlt (b : Bool) : lo b < hi b := by cases b <;> dsimp [lo, hi] <;> linarith
  have hmaps (b : Bool) (x : ℝ) (hx : x ∈ Icc (lo b) (hi b)) :
      x + shift b ∈ Icc (0 : ℝ) p := by
    cases b <;> dsimp [lo, hi, shift] at hx ⊢ <;> constructor <;> linarith [hx.1, hx.2]
  have hcoe (b : Bool) (x : ℝ) :
      ((x + shift b : ℝ) : AddCircle p) = ((x + p / 2 : ℝ) : AddCircle p) := by
    cases b
    · rfl
    · change ((x + -(p / 2) : ℝ) : AddCircle p) = _
      rw [show x + -(p / 2) = x + p / 2 - p by ring,
        AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
  have hpiece (b : Bool × Bool) : FinitePiecewiseAffineOn
      (fun x : ℝ × ℝ => (h (((x.1 + p / 2 : ℝ) : AddCircle p),
        ((x.2 + p / 2 : ℝ) : AddCircle p)) : E)) (T b) := by
    let A : (ℝ × ℝ) →ᴬ[ℝ] (ℝ × ℝ) :=
      ContinuousAffineMap.id ℝ (ℝ × ℝ) + ContinuousAffineMap.const ℝ (ℝ × ℝ)
        (shift b.1, shift b.2)
    have hA (x : ℝ × ℝ) : A x = (x.1 + shift b.1, x.2 + shift b.2) := rfl
    have hball := (isFinitePLBallPair_Icc (hlt b.1)).prod (isFinitePLBallPair_Icc (hlt b.2))
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ := hball
    have ha : FinitePiecewiseAffineOn A (T b) := by
      change FinitePiecewiseAffineOn A (Icc (lo b.1) (hi b.1) ×ˢ Icc (lo b.2) (hi b.2))
      rw [← hJs]
      exact (J.affineOnFaces_affine A).finitePiecewiseAffineOn hJ
    have hm : MapsTo A (T b) (squareCarrier p) := by
      intro x hx
      rw [hA]
      exact ⟨hmaps b.1 x.1 hx.1, hmaps b.2 x.2 hx.2⟩
    apply (hu.comp ha hm).congr
    intro x hx
    let z : Square p := (⟨x.1 + shift b.1, hmaps b.1 x.1 hx.1⟩,
      ⟨x.2 + shift b.2, hmaps b.2 x.2 hx.2⟩)
    change u (A x) = _
    rw [hA, huv z, ← hh z]
    change (h (((x.1 + shift b.1 : ℝ) : AddCircle p),
      ((x.2 + shift b.2 : ℝ) : AddCircle p)) : E) = _
    rw [hcoe, hcoe]
  have hcover : (⋃ b : Bool × Bool, T b) = squareCarrier p := by
    ext x
    constructor
    · intro hx
      obtain ⟨b, hx⟩ := mem_iUnion.mp hx
      have hbound (b : Bool) {t : ℝ} (ht : t ∈ Icc (lo b) (hi b)) : t ∈ Icc 0 p := by
        cases b <;> dsimp [lo, hi] at ht <;> constructor <;> linarith [ht.1, ht.2]
      exact ⟨hbound b.1 hx.1, hbound b.2 hx.2⟩
    · intro hx
      have hchoose {t : ℝ} (ht : t ∈ Icc 0 p) : ∃ b : Bool, t ∈ Icc (lo b) (hi b) := by
        by_cases hmid : t ≤ p / 2
        · exact ⟨false, ht.1, hmid⟩
        · exact ⟨true, (lt_of_not_ge hmid).le, ht.2⟩
      obtain ⟨b, hb⟩ := hchoose hx.1
      obtain ⟨c, hc⟩ := hchoose hx.2
      exact mem_iUnion.mpr ⟨(b, c), hb, hc⟩
  rw [← hcover]
  exact FinitePiecewiseAffineOn.iUnion hpiece

noncomputable def SourceSquareMap.halfTranslate
    (M : SourceSquareMap p K) (h : (AddCircle p × AddCircle p) ≃ₜ K.space)
    (hh : ∀ z, h (projection p z) = M.map z) : SourceSquareMap p K where
  map := ⟨fun z => h (projection p z + (((p / 2 : ℝ) : AddCircle p), ((p / 2 : ℝ) : AddCircle p))),
    by fun_prop⟩
  surjective := h.surjective.comp ((Homeomorph.addRight
    ((((p / 2 : ℝ) : AddCircle p), ((p / 2 : ℝ) : AddCircle p)))).surjective.comp
      (surjective_projection p))
  fibers z w := by
    change h (_ + _) = h (_ + _) ↔ _
    rw [h.injective.eq_iff, add_right_cancel_iff, projection_eq_iff]
  finite_piecewise_affine := by
    refine ⟨_, M.finitePiecewiseAffineOn_halfTranslate h hh, ?_⟩
    intro z
    simp only [projection, AddCircle.coe_add]
    rfl

theorem SourceSquareMap.halfTranslate_map
    (M : SourceSquareMap p K) (h : (AddCircle p × AddCircle p) ≃ₜ K.space)
    (hh : ∀ z, h (projection p z) = M.map z) (z : Square p) :
    (M.halfTranslate h hh).map z = h (projection p z +
      (((p / 2 : ℝ) : AddCircle p), ((p / 2 : ℝ) : AddCircle p))) := rfl

theorem SourceSquareMap.exists_halfTranslate (M : SourceSquareMap p K) :
    ∃ (h : (AddCircle p × AddCircle p) ≃ₜ K.space) (M' : SourceSquareMap p K),
      (∀ z, h (projection p z) = M.map z) ∧
      ∀ z, M'.map z = h (projection p z +
        (((p / 2 : ℝ) : AddCircle p), ((p / 2 : ℝ) : AddCircle p))) := by
  obtain ⟨h, hh⟩ := exists_homeomorph_of_sourceSquareMap p M
  exact ⟨h, M.halfTranslate h hh, hh, M.halfTranslate_map h hh⟩

theorem SourceSquareMap.halfTranslate_homeomorph_eq
    (M : SourceSquareMap p K) (h ht : (AddCircle p × AddCircle p) ≃ₜ K.space)
    (hh : ∀ z, h (projection p z) = M.map z)
    (hht : ∀ z, ht (projection p z) = (M.halfTranslate h hh).map z) :
    ht = (Homeomorph.addRight
      ((((p / 2 : ℝ) : AddCircle p), ((p / 2 : ℝ) : AddCircle p)))).trans h := by
  apply Homeomorph.ext
  intro x
  obtain ⟨z, rfl⟩ := surjective_projection p x
  exact (hht z).trans (M.halfTranslate_map h hh z)

end PoincareConjecture.M76.PeriodicSquare
