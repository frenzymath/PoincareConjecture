import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Coordinates.ClosedCharts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFamilyGluing



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)

theorem exists_rimCylinder_homeomorph
    (H : (Bool × Bool) → halfArmRectangle ≃ₜ halfArmRectangle)
    (hH : ∀ i, (H i).IsFinitePL)
    (hfixed : ∀ i (p : halfArmRectangle), (p : P2) ∈ frontier halfArmRectangle → H i p = p) :
    ∃ G : rimCylinder ≃ₜ rimCylinder, G.IsFinitePL ∧
      (∀ i (p : halfArmRectangle),
        (G ⟨halfArmChart i p, halfArmCarrier_cover ▸
          mem_iUnion.mpr ⟨i,mem_image_of_mem (halfArmChart i) p.property⟩⟩ : E) =
          halfArmChart i (H i p)) ∧
      ∀ x : rimCylinder, (x : E).2 = 0 ∨ (x : E).2 = -(1/2 : ℝ) ∨ (x : E).2 = 1/2 →
        G x = x := by
  classical
  choose C hC hCval using exists_halfArmChart_homeomorph
  let D (i : Bool × Bool) : halfArmCarrier i ≃ₜ halfArmCarrier i :=
    (C i).symm.trans ((H i).trans (C i))
  have hD (i : Bool × Bool) : (D i).IsFinitePL :=
    (hC i).symm.trans ((hH i).trans (hC i))
  have hDval (i : Bool × Bool) (p : halfArmRectangle) :
      (D i (C i p) : E) = halfArmChart i (H i p) := by
    simp only [D,Homeomorph.trans_apply,Homeomorph.symm_apply_apply,hCval]
  have hfix (i j : Bool × Bool) (hij : i ≠ j) (x : halfArmCarrier i)
      (hxj : (x : E) ∈ halfArmCarrier j) : D i x = x := by
    let p := (C i).symm x
    have hv : halfArmChart i p = (x : E) := by
      rw [← hCval, (C i).apply_symm_apply]
    obtain ⟨q,hq,hqval⟩ := hxj
    have hpfront := halfArmChart_overlap_frontier hij p.property hq (hv.trans hqval.symm)
    have hHp := hfixed i p hpfront
    apply Subtype.ext
    change (C i (H i p) : E) = (x : E)
    rw [hHp,hCval]
    exact hv
  have hoverlap (i j : Bool × Bool) (x : halfArmCarrier i) :
      (x : E) ∈ halfArmCarrier j ↔ (D i x : E) ∈ halfArmCarrier j := by
    by_cases hij : i=j
    · subst j
      exact iff_of_true x.property (D i x).property
    constructor
    · intro hx
      rw [hfix i j hij x hx]
      exact hx
    · intro hx
      have h := (D i).injective (hfix i j hij (D i x) hx)
      simpa only [h] using hx
  have hagree (i j : Bool × Bool) (x : E) (hi : x ∈ halfArmCarrier i)
      (hj : x ∈ halfArmCarrier j) : (D i ⟨x,hi⟩ : E) = D j ⟨x,hj⟩ := by
    by_cases hij : i=j
    · subst j; rfl
    rw [hfix i j hij ⟨x,hi⟩ hj,hfix j i (Ne.symm hij) ⟨x,hj⟩ hi]
  obtain ⟨G,hG,hGval⟩ :=
    Homeomorph.exists_iUnion_finitePL halfArmCarrier halfArmCarrier D hD hoverlap hagree
  let G' : rimCylinder ≃ₜ rimCylinder :=
    (Homeomorph.setCongr halfArmCarrier_cover.symm).trans
      (G.trans (Homeomorph.setCongr halfArmCarrier_cover))
  have hG' : G'.IsFinitePL := hG.setCongr halfArmCarrier_cover halfArmCarrier_cover
  have hkeep (i : Bool × Bool) (p : halfArmRectangle) :
      (G' ⟨halfArmChart i p, halfArmCarrier_cover ▸
        mem_iUnion.mpr ⟨i,mem_image_of_mem (halfArmChart i) p.property⟩⟩ : E) =
          halfArmChart i (H i p) := by
    have h := hGval i (C i p)
    rw [hDval] at h
    convert h using 1
    apply congrArg (fun x ↦ (G x : E))
    exact Subtype.ext (hCval i p).symm
  refine ⟨G',hG',hkeep,?_⟩
  intro x hx
  have hxunion : (x : E) ∈ ⋃ i, halfArmCarrier i := halfArmCarrier_cover.symm ▸ x.property
  obtain ⟨i,p,hp,hpv⟩ := mem_iUnion.mp hxunion
  have hpedge : p.2=0 ∨ p.2=1/2 := by
    have hv := congrArg Prod.snd hpv
    change sign i.2 * p.2 = (x : E).2 at hv
    cases ha : i.2 <;> simp only [ha,sign,Bool.false_eq_true,if_false,if_true,
      one_mul,neg_one_mul] at hv
    all_goals rcases hx with hx | hx | hx
    all_goals first | exact Or.inl (by linarith) | exact Or.inr (by linarith [hp.2.1])
  have hpfront : p ∈ frontier halfArmRectangle := by
    rw [halfArmRectangle,frontier_rectangle_eq_four_sides (by norm_num) (by norm_num)]
    rcases hpedge with hz | hz
    · exact Or.inl (Or.inl ⟨hp.1,hz⟩)
    · exact Or.inl (Or.inr ⟨hp.1,hz⟩)
  have hv := hkeep i ⟨p,hp⟩
  rw [hfixed i ⟨p,hp⟩ hpfront] at hv
  apply Subtype.ext
  convert hv.trans hpv using 1
  apply congrArg (fun y ↦ (G' y : E))
  exact Subtype.ext hpv.symm

end PoincareConjecture.M76.Dehn.Annuli.RimBands
