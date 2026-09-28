import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Coordinates.ClosedArms
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Patches.HalfPatch



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Phase" => Icc (-(1/2 : ℝ)) (3/2)

def halfArmChart (i : Bool × Bool) (p : P2) : E :=
  (armPoint i.1 p.1, sign i.2 * p.2)

def halfArmCarrier (i : Bool × Bool) : Set E := halfArmChart i '' halfArmRectangle

def rimCylinder : Set E := sphere (0 : V2) 1 ×ˢ Icc (-(1/2 : ℝ)) (1/2)

theorem halfArmChart_finitePL (i : Bool × Bool) :
    FinitePiecewiseAffineOn (halfArmChart i) halfArmRectangle := by
  have hball := (isFinitePLBallPair_Icc (show -(1/2 : ℝ) < 3/2 by norm_num)).prod
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1/2 by norm_num))
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hball
  have hid : FinitePiecewiseAffineOn (id : P2 → P2) halfArmRectangle :=
    ⟨K,hK,hKs,K.affineOnFaces_affine (ContinuousAffineMap.id ℝ P2)⟩
  exact (finitePL_armPoint
    (hid.postcomp (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap) i.1).prod_mk
      (hid.postcomp (sign i.2 • ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap)

theorem halfArmChart_injective (i : Bool × Bool) :
    InjOn (halfArmChart i) halfArmRectangle := by
  intro p hp q hq heq
  apply Prod.ext
  · exact armPoint_closed_injective i.1 hp.1 hq.1 (congrArg Prod.fst heq)
  · have h := congrArg Prod.snd heq
    cases ha : i.2 <;> simpa [halfArmChart,ha,sign] using h

theorem exists_halfArmChart_homeomorph (i : Bool × Bool) :
    ∃ H : halfArmRectangle ≃ₜ halfArmCarrier i, H.IsFinitePL ∧
      ∀ p : halfArmRectangle, (H p : E) = halfArmChart i p :=
  (halfArmChart_finitePL i).exists_homeomorph_image (halfArmChart_injective i)

theorem halfArmCarrier_cover : (⋃ i, halfArmCarrier i) = rimCylinder := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hx⟩ := mem_iUnion.mp hx
    obtain ⟨p,hp,rfl⟩ := hx
    refine ⟨(armPoint_closed_mem i.1 hp.1).1,?_⟩
    change sign i.2 * p.2 ∈ Icc (-(1/2 : ℝ)) (1/2)
    cases i.2 <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul]
    all_goals exact ⟨by linarith [hp.2.1,hp.2.2],by linarith [hp.2.1,hp.2.2]⟩
  · intro hx
    have hz : x.1 ∈ armPoint false '' Phase ∪ armPoint true '' Phase :=
      closed_arms_cover.symm ▸ hx.1
    have hex : ∃ b t, t ∈ Phase ∧ armPoint b t=x.1 := by
      rcases hz with ⟨t,ht,hv⟩ | ⟨t,ht,hv⟩
      · exact ⟨false,t,ht,hv⟩
      · exact ⟨true,t,ht,hv⟩
    obtain ⟨b,t,ht,hv⟩ := hex
    by_cases hh : 0 ≤ x.2
    · refine mem_iUnion.mpr ⟨(b,false),(t,x.2),⟨ht,hh,hx.2.2⟩,?_⟩
      exact Prod.ext hv (by simp [halfArmChart,sign])
    · refine mem_iUnion.mpr ⟨(b,true),(t,-x.2),⟨ht,by linarith,by linarith [hx.2.1]⟩,?_⟩
      exact Prod.ext hv (by simp [halfArmChart,sign])

theorem halfArmChart_overlap_frontier {i j : Bool × Bool} (hij : i ≠ j)
    {p q : P2} (hp : p ∈ halfArmRectangle) (hq : q ∈ halfArmRectangle)
    (heq : halfArmChart i p = halfArmChart j q) : p ∈ frontier halfArmRectangle := by
  rw [halfArmRectangle,frontier_rectangle_eq_four_sides (by norm_num) (by norm_num)]
  by_cases hb : i.1 = j.1
  · have ha : i.2 ≠ j.2 := fun h ↦ hij (Prod.ext hb h)
    have hv := congrArg Prod.snd heq
    have hz : p.2=0 := by
      cases hi : i.2 <;> cases hj : j.2
      all_goals simp only [hi,hj] at ha
      all_goals try exact False.elim (ha rfl)
      all_goals simp only [halfArmChart,hi,hj,sign,Bool.false_eq_true,if_false,if_true,
        one_mul,neg_one_mul] at hv
      all_goals linarith [hp.2.1,hq.2.1]
    exact Or.inl (Or.inl ⟨hp.1,hz⟩)
  · have hv := congrArg Prod.fst heq
    have hm : armPoint i.1 p.1 ∈ armPoint false '' Phase ∩ armPoint true '' Phase := by
      have hi : armPoint i.1 p.1 ∈ armPoint i.1 '' Phase := ⟨p.1,hp.1,rfl⟩
      have hj : armPoint i.1 p.1 ∈ armPoint j.1 '' Phase := ⟨q.1,hq.1,hv.symm⟩
      cases hi' : i.1 <;> cases hj' : j.1 <;> simp_all
    rw [closed_arms_overlap] at hm
    rcases hm with hm | hm
    · have ht : p.1= -(1/2 : ℝ) := armPoint_closed_injective i.1 hp.1
        (by norm_num) (hm.trans (armPoint_lower i.1).symm)
      exact Or.inr (Or.inl ⟨ht,hp.2⟩)
    · have ht : p.1=3/2 := armPoint_closed_injective i.1 hp.1
        (by norm_num) (hm.trans (armPoint_upper i.1).symm)
      exact Or.inr (Or.inr ⟨ht,hp.2⟩)

end PoincareConjecture.M76.Dehn.Annuli.RimBands
