import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.SupportedFullEdgeMove
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.ProperArcPairConfinement

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Z" => (Set.preimage (Prod.snd : (ℝ × ℝ) → ℝ) ({0} : Set ℝ))

theorem exists_original_constructed_axis_ambient_move
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (T : P3 ≃ᴬ[ℝ] V3)
    {W B : Set P2} {a b : P2}
    (hW : IsFinitePLBallPair ℝ W {a, b})
    (hab : a.1 < b.1) (ha : a.2 = 0) (hb : b.2 = 0)
    (hup : ∀ z ∈ W, 0 ≤ z.2) (hWaxis : W ∩ Z = {a, b})
    (hB : IsFinitePLBallPair P2 B (segment ℝ a b ∪ W))
    {U : Set X} (hU : IsOpen U)
    (hzeroB : ∀ z ∈ B, T (z, 0) ∈ Q.target ∧ Q.symm (T (z, 0)) ∈ U)
    {Sigma edge : Set X} {u v : X}
    (havoid : Disjoint W ((fun z : P2 => Q.symm (T (z, 0))) ⁻¹' Sigma))
    (hcontact : ((fun z : P2 => Q.symm (T (z, 0))) '' segment ℝ a b) ∩
      Sigma = {u, v})
    (huv : u ≠ v)
    (hwedge : ((fun z : P2 => Q.symm (T (z, 0))) '' segment ℝ a b) ⊆ edge)
    (hedgeAxis : ∀ x ∈ edge ∩ Q.source,
      (T.symm (Q x)).1 ∈ Z ∧ (T.symm (Q x)).2 = 0)
    (hfinite : (edge ∩ Sigma).Finite)
    (untouched : κ → Set X) (hprotected : ∀ i, Disjoint U (untouched i)) :
    ∃ (D : Set P2) (F : X ≃ₜ X) (C : Set X),
      IsCompact D ∧ IsFinitePLBallPair P2 D (frontier D) ∧ B ⊆ D ∧
      a ∈ frontier D ∧ b ∈ frontier D ∧
      W ⊆ D ∧ segment ℝ a b ⊆ D ∧
      W \ {a, b} ⊆ interior D ∧ segment ℝ a b \ {a, b} ⊆ interior D ∧
      D ∩ Z = segment ℝ a b ∧
      IsCompact C ∧ C ⊆ U ∧
      (∃ r : ℝ, 0 < r ∧ C = (Q.symm ∘ T) '' (D ×ˢ Icc (-r) r) ∧
        T '' (D ×ˢ Icc (-r) r) ⊆ Q.target) ∧
      (∀ y ∉ C, F y = y) ∧ (∀ y ∉ U, F y = y) ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      EqOn F id (edge \ ((fun z : P2 => Q.symm (T (z, 0))) '' segment ℝ a b)) ∧
      F '' edge = (edge \ ((fun z : P2 => Q.symm (T (z, 0))) '' segment ℝ a b)) ∪
        ((fun z : P2 => Q.symm (T (z, 0))) '' W) ∧
      edge ∩ (F.symm '' Sigma) = (edge ∩ Sigma) \ ({u, v} : Set X) ∧
      (edge ∩ (F.symm '' Sigma)).ncard = (edge ∩ Sigma).ncard - 2 ∧
      (∀ i, untouched i ∩ (F.symm '' Sigma) = untouched i ∩ Sigma) ∧
      (∀ i, (untouched i ∩ (F.symm '' Sigma)).ncard = (untouched i ∩ Sigma).ncard) := by
  let V : Set P2 := (fun z => T (z, 0)) ⁻¹' (Q.target ∩ Q.symm ⁻¹' U)
  have hV : IsOpen V := (Q.isOpen_inter_preimage_symm hU).preimage
    (T.continuous.comp (continuous_id.prodMk continuous_const))
  have hBV : B ⊆ V := fun z hz => hzeroB z hz
  obtain ⟨D, hcompact, hD, hDV, hBD, haD, hbD, hWD, hwD, hWint, hwint, hDaxis⟩ :=
    exists_confined_proper_arc_pair_disk hW hab ha hb hup hWaxis hB hV hBV
  have hab' : a ≠ b := fun h => hab.ne (congrArg Prod.fst h)
  have hw : IsFinitePLBallPair ℝ (segment ℝ a b) {a, b} := by
    have hh := isFinitePLBallPair_affine_interval zero_lt_one
      (ContinuousAffineMap.lineMap a b) (AffineMap.lineMap_injective ℝ hab').injOn
    simpa only [ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one, ← segment_eq_image_lineMap] using hh
  obtain ⟨axis, haxis, haxisa, haxisb⟩ :=
    hw.exists_marked_interval_homeomorph hW hab' hab'
  have hfix : ∀ x : segment ℝ a b,
      (x : P2) ∈ ({a, b} : Set P2) → (axis x : P2) = x := by
    intro x hx
    rcases hx with hx | hx
    · exact ((haxisa x).mpr hx).trans hx.symm
    · exact ((haxisb x).mpr hx).trans hx.symm
  have hwproper : segment ℝ a b \ {a, b} ⊆ D \ frontier D :=
    hwint.trans (hD.interior_eq_sdiff_of_finrank_eq rfl).subset
  have hWproper : W \ {a, b} ⊆ D \ frontier D :=
    hWint.trans (hD.interior_eq_sdiff_of_finrank_eq rfl).subset
  have hzero : ∀ z ∈ D, T (z, 0) ∈ Q.target ∧ Q.symm (T (z, 0)) ∈ U :=
    fun z hz => hDV hz
  obtain ⟨F, C, hmove⟩ := exists_original_supported_full_edge_move e he Q hQ T
    hD hw hW hab' haD hbD hwD hWD hwproper hWproper axis haxis hfix hDaxis
    hU hzero havoid hcontact huv hwedge hedgeAxis hfinite untouched hprotected
  exact ⟨D, F, C, hcompact, hD, hBD, haD, hbD, hWD, hwD, hWint, hwint, hDaxis, hmove⟩

end PoincareConjecture.M76
