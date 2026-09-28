import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.Lift



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "I" => unitInterval
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem finitePL_projected_annular_lift {r : ℝ → P2}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1))
    (hheight : ∀ t : I, (r t).2 ∈ Icc (-1 : ℝ) 1) :
    FinitePiecewiseAffineOn
      (fun t => annulusMap 8 (by norm_num) (((r t).1 : Circle), (r t).2))
      (Icc 0 1) := by
  apply (locallyPiecewiseAffineOn_annulusMap_lift (L := 8) (d := 3 / 2)
    (by norm_num) (by norm_num) (by norm_num)).comp_finitePiecewiseAffineOn hr
  intro t ht
  have h := hheight ⟨t, ht⟩
  exact ⟨mem_univ _, by dsimp at h ⊢; constructor <;> linarith [h.1, h.2]⟩

theorem annular_lift_translate_separation
    (gamma : C(I, Ann)) (hinj : Function.Injective gamma) {r : ℝ → P2}
    (hproj : ∀ t : I, annulusMap 8 (by norm_num)
      (((r t).1 : Circle), (r t).2) = gamma t) :
    ∀ (s t : ℝ), s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      ∀ k : ℤ, r s = r t + (32 * (k : ℝ), 0) → s = t ∧ k = 0 := by
  intro s t hs ht k heq
  have hp : ((32 * (k : ℝ) : ℝ) : Circle) = 0 :=
    (AddCircle.coe_eq_zero_iff (4 * (8 : ℝ))).mpr
      ⟨k, by simp [zsmul_eq_mul]; ring⟩
  have hgamma : gamma ⟨s, hs⟩ = gamma ⟨t, ht⟩ := by
    apply Subtype.ext
    rw [← hproj ⟨s, hs⟩, ← hproj ⟨t, ht⟩]
    change annulusMap 8 _ (((r s).1 : Circle), (r s).2) =
      annulusMap 8 _ (((r t).1 : Circle), (r t).2)
    rw [heq]
    simp only [Prod.fst_add, Prod.snd_add, add_zero, AddCircle.coe_add, hp]
  have hst : s = t := congrArg Subtype.val (hinj hgamma)
  refine ⟨hst, ?_⟩
  subst s
  have ha := congrArg Prod.fst heq
  have hk : (k : ℝ) = 0 := by dsimp at ha; linarith
  exact_mod_cast hk

theorem injOn_annular_lift
    (gamma : C(I, Ann)) (hinj : Function.Injective gamma) {r : ℝ → P2}
    (hproj : ∀ t : I, annulusMap 8 (by norm_num)
      (((r t).1 : Circle), (r t).2) = gamma t) :
    InjOn r (Icc (0 : ℝ) 1) := by
  intro s hs t ht heq
  exact (annular_lift_translate_separation gamma hinj hproj s t hs ht 0
    (by simpa only [Int.cast_zero, mul_zero, ← Prod.zero_eq_mk, add_zero] using heq)).1

theorem annular_lift_zero_winding_endpoints
    (gamma : C(I, Ann)) {r : ℝ → P2}
    (hproj : ∀ t : I, annulusMap 8 (by norm_num)
      (((r t).1 : Circle), (r t).2) = gamma t)
    (hr0 : r 0 = (0, -1)) (hr1 : r 1 = (0, 1)) :
    gamma 0 = annulusRimPoint false 0 ∧ gamma 1 = annulusRimPoint true 0 := by
  constructor
  · apply Subtype.ext
    rw [← hproj 0]
    change annulusMap 8 _ (((r 0).1 : Circle), (r 0).2) = _
    rw [hr0]
    rfl
  · apply Subtype.ext
    rw [← hproj 1]
    change annulusMap 8 _ (((r 1).1 : Circle), (r 1).2) = _
    rw [hr1]
    rfl

end PoincareConjecture.M76.Dehn
