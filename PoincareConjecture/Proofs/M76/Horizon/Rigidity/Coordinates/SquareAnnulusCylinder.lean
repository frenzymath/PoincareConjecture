import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneSquareCircle
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnularStripCharts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusDepth










set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (-(1 / 8 : ℝ)) (1 / 8)
local notation "Ann" => squareAnnulus 1 (1 / 8 : ℝ)

private noncomputable def annulusHeightEquiv : J ≃ₜ I where
  toFun := fun t => ⟨8 * (t : ℝ), by constructor <;> linarith [t.property.1, t.property.2]⟩
  invFun := fun t => ⟨(t : ℝ) / 8, by constructor <;> linarith [t.property.1, t.property.2]⟩
  left_inv := by intro t; apply Subtype.ext; dsimp; ring
  right_inv := by intro t; apply Subtype.ext; dsimp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop



theorem exists_finitePL_square_annulus_cylinder :
    ∃ C : Ann ≃ₜ (Q ×ˢ I), C.IsFinitePL ∧
      ∀ p : Ann, (C p : V2 × ℝ).2 = 8 * depth 1 p := by
  classical
  obtain ⟨a, ha⟩ := exists_annulus_homeomorph
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (by norm_num : 4 * (1 / 8 : ℝ) < 1)
  let s : AddCircle (4 * (1 : ℝ)) ≃ₜ Q :=
    (AddCircle.homeomorphAddCircle (4 * (1 : ℝ)) (4 * (2 : ℝ))
      (by norm_num) (by norm_num)).trans HamiltonIndexOne.squareCircle
  let C : Ann ≃ₜ (Q ×ˢ I) :=
    (a.symm.trans (s.prodCongr annulusHeightEquiv)).trans (Homeomorph.Set.prod Q I).symm
  have hC (p : AddCircle (4 * (1 : ℝ)) × J) :
      (C (a p) : V2 × ℝ) = ((s p.1 : V2), 8 * (p.2 : ℝ)) := by
    simp only [C, Homeomorph.trans_apply, a.symm_apply_apply]
    rfl
  let f : P2 → V2 × ℝ := fun p => if h : p ∈ Ann then C ⟨p, h⟩ else 0
  have hf (p : Ann) : f p = (C p : V2 × ℝ) := dif_pos p.property
  have hcover : (⋃ i : Fin 4, stripRegion 1 (1 / 8) i) = Ann := by
    rw [← union_four_strips (by norm_num : (0 : ℝ) ≤ 1 / 8)
      (by norm_num : 2 * (1 / 8 : ℝ) < 1)]
    ext p
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (Or.inl (Or.inl hi))
      · exact Or.inl (Or.inl (Or.inr hi))
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro (((hp | hp) | hp) | hp)
      · exact ⟨0, hp⟩
      · exact ⟨1, hp⟩
      · exact ⟨2, hp⟩
      · exact ⟨3, hp⟩
  have hSi (i : Fin 4) : stripRegion 1 (1 / 8) i ⊆ Ann :=
    fun _ hx => hcover ▸ mem_iUnion.mpr ⟨i, hx⟩
  have hfi (i : Fin 4) : FinitePiecewiseAffineOn f (stripRegion 1 (1 / 8) i) := by
    obtain ⟨b, hb, hbval⟩ := exists_rotated_strip_charts
      (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : 4 * (1 / 8 : ℝ) < 1) i
    have hbcopy := hb
    obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hbcopy
    let angle : P2 →ᴬ[ℝ] ℝ := (2 : ℝ) •
      (ContinuousAffineMap.const ℝ P2 (i.val : ℝ) +
        (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap)
    let height : P2 →ᴬ[ℝ] ℝ :=
      (8 : ℝ) • (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
    have hang : FinitePiecewiseAffineOn angle (rectangle 1 (1 / 8)) :=
      hKs ▸ (K.affineOnFaces_affine angle).finitePiecewiseAffineOn hK
    have hheight : FinitePiecewiseAffineOn height (rectangle 1 (1 / 8)) :=
      hKs ▸ (K.affineOnFaces_affine height).finitePiecewiseAffineOn hK
    let g : P2 → V2 × ℝ := fun p =>
      ((HamiltonIndexOne.squareCircle ((angle p : ℝ) : AddCircle (4 * (2 : ℝ))) : V2), height p)
    have hg : FinitePiecewiseAffineOn g (rectangle 1 (1 / 8)) :=
      (HamiltonIndexOne.finitePiecewiseAffineOn_squareCircle_comp hang).prod_mk hheight
    have hfb (p : rectangle 1 (1 / 8)) :
        f (b p) = g p := by
      let q : AddCircle (4 * (1 : ℝ)) × J :=
        (((i.val : ℝ) + (p : P2).1 : ℝ), ⟨(p : P2).2, p.property.2⟩)
      have haq : (a q : P2) = (b p : P2) := by
        rw [ha, hbval]
        have ht : 4 * |(p : P2).2| < (1 : ℝ) := by
          have h := abs_le.mpr p.property.2
          linarith
        rw [annulusMap_coe (by norm_num : (0 : ℝ) < 1) ht (by
          fin_cases i <;> constructor <;> norm_num <;>
            linarith [p.property.1.1, p.property.1.2])]
        simpa only [mul_one, add_comm, Prod.mk.eta] using wrappedStripMap_block ht p.property.1 i
      have hfp : f (b p) = (C (a q) : V2 × ℝ) := by rw [← haq, hf]
      rw [hfp, hC]
      apply Prod.ext
      · change (HamiltonIndexOne.squareCircle
          (AddCircle.homeomorphAddCircle (4 * (1 : ℝ)) (4 * (2 : ℝ))
            (by norm_num) (by norm_num) (((i.val : ℝ) + (p : P2).1 : ℝ))) : V2) = _
        rw [AddCircle.homeomorphAddCircle_apply_mk]
        congr 2
        apply congrArg (fun t : ℝ => (t : AddCircle (4 * (2 : ℝ))))
        change ((i.val : ℝ) + (p : P2).1) * ((4 * 1)⁻¹ * (4 * 2)) =
          2 * ((i.val : ℝ) + (p : P2).1)
        norm_num
        ring
      · rfl
    obtain ⟨v, hv, hvval⟩ := hb.symm
    have hvmap : MapsTo v (stripRegion 1 (1 / 8) i) (rectangle 1 (1 / 8)) := by
      intro x hx
      rw [← hvval ⟨x, hx⟩]
      exact (b.symm ⟨x, hx⟩).property
    apply (hg.comp hv hvmap).congr
    intro x hx
    rw [Function.comp_apply, ← hvval ⟨x, hx⟩, ← hfb, b.apply_symm_apply]
  have hfPL : FinitePiecewiseAffineOn f Ann := by
    rw [← hcover]
    exact FinitePiecewiseAffineOn.iUnion hfi
  refine ⟨C, ⟨f, hfPL, fun p => (hf p).symm⟩, ?_⟩
  intro p
  obtain ⟨q, rfl⟩ := a.surjective p
  rw [hC, ha]
  rw [depth_annulusMap (by norm_num : (0 : ℝ) < 1) (by
    have h := abs_le.mpr q.2.property
    linarith)]

end PoincareConjecture.M76
