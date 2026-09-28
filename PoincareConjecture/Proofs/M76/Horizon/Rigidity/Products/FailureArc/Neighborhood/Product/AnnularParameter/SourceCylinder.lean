import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.SquareAnnulusCylinder
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.CyclicPanels.Construction



set_option autoImplicit false
noncomputable section
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.AnnularParameter

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-(1/8 : ℝ)) (1/8)
local notation "Ann" => squareAnnulus (2 : ℝ) (1/8)

def depthEquiv : J ≃ₜ I where
  toFun := fun t => ⟨4*(t : ℝ)+1/2,by constructor <;> linarith [t.property.1,t.property.2]⟩
  invFun := fun t => ⟨((t : ℝ)-1/2)/4,by constructor <;> linarith [t.property.1,t.property.2]⟩
  left_inv := by intro t; apply Subtype.ext; dsimp; ring
  right_inv := by intro t; apply Subtype.ext; dsimp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem exists_source_cylinder :
    ∃ C : Ann ≃ₜ (Rim ×ˢ I), C.IsFinitePL ∧
      ∀ p : AddCircle (4*(2 : ℝ)) × J,
        ∀ x : Ann, (x : P2) = annulusMap 2 (by norm_num) (p.1,p.2) →
          (C x : V2 × ℝ) = ((HamiltonIndexOne.squareCircle p.1 : V2),4*(p.2 : ℝ)+1/2) := by
  classical
  obtain ⟨a,ha⟩ := exists_annulus_homeomorph
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) ≤ 1/8)
    (by norm_num : 4*(1/8 : ℝ) < 2)
  let C : Ann ≃ₜ (Rim ×ˢ I) :=
    (a.symm.trans (HamiltonIndexOne.squareCircle.prodCongr depthEquiv)).trans
      (Homeomorph.Set.prod Rim I).symm
  have hC (p : AddCircle (4*(2 : ℝ)) × J) :
      (C (a p) : V2 × ℝ) = ((HamiltonIndexOne.squareCircle p.1 : V2),4*(p.2 : ℝ)+1/2) := by
    simp only [C,Homeomorph.trans_apply,a.symm_apply_apply]
    rfl
  let f : P2 → V2 × ℝ := fun p => if h : p ∈ Ann then C ⟨p,h⟩ else 0
  have hf (p : Ann) : f p = (C p : V2 × ℝ) := dif_pos p.property
  have hcover : (⋃ i : Fin 4,stripRegion 2 (1/8) i) = Ann := by
    rw [← union_four_strips (by norm_num : (0 : ℝ) ≤ 1/8)
      (by norm_num : 2*(1/8 : ℝ) < 2)]
    ext p
    simp only [mem_iUnion,mem_union]
    constructor
    · rintro ⟨i,hi⟩
      fin_cases i
      · exact Or.inl (Or.inl (Or.inl hi))
      · exact Or.inl (Or.inl (Or.inr hi))
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro (((hp|hp)|hp)|hp)
      · exact ⟨0,hp⟩
      · exact ⟨1,hp⟩
      · exact ⟨2,hp⟩
      · exact ⟨3,hp⟩
  have hfi (i : Fin 4) : FinitePiecewiseAffineOn f (stripRegion 2 (1/8) i) := by
    obtain ⟨b,hb,hbval⟩ := exists_rotated_strip_charts
      (by norm_num : (0 : ℝ) < 1/8) (by norm_num : 4*(1/8 : ℝ) < 2) i
    have hbcopy := hb
    obtain ⟨_,⟨K,hK,hKs,_⟩,_⟩ := hbcopy
    let angle : P2 →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ P2 ((i.val : ℝ)*2) +
      (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
    let height : P2 →ᴬ[ℝ] ℝ :=
      (4 : ℝ) • (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap +
        ContinuousAffineMap.const ℝ P2 (1/2)
    have hang : FinitePiecewiseAffineOn angle (rectangle 2 (1/8)) :=
      hKs ▸ (K.affineOnFaces_affine angle).finitePiecewiseAffineOn hK
    have hheight : FinitePiecewiseAffineOn height (rectangle 2 (1/8)) :=
      hKs ▸ (K.affineOnFaces_affine height).finitePiecewiseAffineOn hK
    let g : P2 → V2 × ℝ := fun p =>
      ((HamiltonIndexOne.squareCircle ((angle p : ℝ) : AddCircle (4*(2 : ℝ))) : V2),height p)
    have hg : FinitePiecewiseAffineOn g (rectangle 2 (1/8)) :=
      (HamiltonIndexOne.finitePiecewiseAffineOn_squareCircle_comp hang).prod_mk hheight
    have hfb (p : rectangle 2 (1/8)) : f (b p) = g p := by
      let q : AddCircle (4*(2 : ℝ)) × J :=
        (((i.val : ℝ)*2+(p : P2).1 : ℝ),⟨(p : P2).2,p.property.2⟩)
      have haq : (a q : P2) = (b p : P2) := by
        rw [ha,hbval]
        have ht : 4*|(p : P2).2| < (2 : ℝ) := by
          have h := abs_le.mpr p.property.2
          linarith
        rw [annulusMap_coe (by norm_num : (0 : ℝ) < 2) ht (by
          fin_cases i <;> constructor <;> norm_num <;>
            linarith [p.property.1.1,p.property.1.2])]
        simpa only [add_comm,Prod.mk.eta] using wrappedStripMap_block ht p.property.1 i
      rw [← haq,hf,hC]
      rfl
    obtain ⟨v,hv,hvval⟩ := hb.symm
    have hvmap : MapsTo v (stripRegion 2 (1/8) i) (rectangle 2 (1/8)) := by
      intro x hx
      rw [← hvval ⟨x,hx⟩]
      exact (b.symm ⟨x,hx⟩).property
    apply (hg.comp hv hvmap).congr
    intro x hx
    rw [Function.comp_apply,← hvval ⟨x,hx⟩,← hfb,b.apply_symm_apply]
  have hfPL : FinitePiecewiseAffineOn f Ann := by
    rw [← hcover]
    exact FinitePiecewiseAffineOn.iUnion hfi
  refine ⟨C,⟨f,hfPL,fun p => (hf p).symm⟩,?_⟩
  intro p x hx
  have hx' : x = a p := Subtype.ext (hx.trans (ha p).symm)
  rw [hx',hC]

end PoincareConjecture.M76.Dehn.Annuli.AnnularParameter
