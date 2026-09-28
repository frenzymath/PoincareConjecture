import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Patches.AttachedPatch
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.PlanarLift

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

local notation "P2" => (ℝ × ℝ)
local notation "J" => Icc (0 : ℝ) 1

def halfArmRectangle : Set P2 := Icc (-(1/2 : ℝ)) (3/2) ×ˢ Icc (0 : ℝ) (1/2)
def halfArmPatch (w : ℝ) : Set P2 := J ×ˢ Icc (0 : ℝ) w
def armAttachment : Set P2 := J ×ˢ {(0 : ℝ)}

private theorem rectangle_ball {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    IsFinitePLBallPair P2 (Icc a b ×ˢ Icc c d) (frontier (Icc a b ×ˢ Icc c d)) := by
  have h := (isFinitePLBallPair_Icc hab).prod (isFinitePLBallPair_Icc hcd)
  rwa [← h.frontier_eq_of_finrank_eq rfl] at h

theorem armAttachment_ball : IsFinitePLBallPair ℝ armAttachment {(0,0),(1,0)} := by
  let A : ℝ →ᴬ[ℝ] P2 :=
    (ContinuousLinearMap.id ℝ ℝ).toContinuousAffineMap.prod (ContinuousAffineMap.const ℝ ℝ 0)
  have hball := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
  have hball' := hball
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hball
  have hA : FinitePiecewiseAffineOn A J :=
    ⟨K,hK,hKs,K.affineOnFaces_affine A⟩
  have hAi : InjOn A J := fun _ _ _ _ heq => congrArg Prod.fst heq
  have himage : A '' J = armAttachment := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩; exact ⟨ht,rfl⟩
    · rintro ⟨hx,hz⟩
      exact ⟨x.1,hx,Prod.ext rfl hz.symm⟩
  have h := hball'.image hA hAi
  simpa [himage,image_pair,A] using h

theorem exists_half_arm_patch_extension {w : ℝ} (hw : 0 < w) (hwsmall : w < 1/2)
    {g : P2 → P2} (hg : FinitePiecewiseAffineOn g (halfArmPatch w))
    (hgi : InjOn g (halfArmPatch w))
    (hmap : MapsTo g (halfArmPatch w)
      (Ioo (-(1/2 : ℝ)) (3/2) ×ˢ Ico (0 : ℝ) (1/2)))
    (hcenter : ∀ t ∈ J, g (t,0) = (t,0))
    (hzero : ∀ p ∈ halfArmPatch w, (g p).2=0 ↔ p.2=0) :
    ∃ H : halfArmRectangle ≃ₜ halfArmRectangle, H.IsFinitePL ∧
      (∀ p : halfArmPatch w, (H ⟨p,by
        exact ⟨⟨by linarith [p.property.1.1],by linarith [p.property.1.2]⟩,
          ⟨p.property.2.1,p.property.2.2.trans hwsmall.le⟩⟩⟩ : P2) = g p) ∧
      (∀ p : halfArmRectangle, (p : P2) ∈ frontier halfArmRectangle → H p = p) ∧
      (∀ p : halfArmRectangle, (p : P2) ∈ halfArmPatch w ↔
        (H p : P2) ∈ g '' halfArmPatch w) := by
  have hs : IsFinitePLBallPair P2 halfArmRectangle (frontier halfArmRectangle) :=
    rectangle_ball (by norm_num) (by norm_num)
  have hd : IsFinitePLBallPair P2 (halfArmPatch w) (frontier (halfArmPatch w)) :=
    rectangle_ball zero_lt_one hw
  have hds : halfArmPatch w ⊆ halfArmRectangle := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩,hp.2.1,hp.2.2.trans hwsmall.le⟩
  have hub : armAttachment ⊆ frontier (halfArmPatch w) := by
    intro p hp
    rw [halfArmPatch,frontier_rectangle_eq_four_sides zero_le_one hw.le]
    exact Or.inl (Or.inl hp)
  have huq : armAttachment ⊆ frontier halfArmRectangle := by
    intro p hp
    rw [halfArmRectangle,frontier_rectangle_eq_four_sides (by norm_num) (by norm_num)]
    exact Or.inl (Or.inl ⟨⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩,hp.2⟩)
  have hcontact (p : P2) (hp : p ∈ halfArmPatch w) :
      p ∈ frontier halfArmRectangle ↔ p ∈ armAttachment := by
    constructor
    · intro h
      rw [halfArmRectangle,frontier_rectangle_eq_four_sides (by norm_num) (by norm_num)] at h
      rcases h with (h | h) | (h | h)
      · exact ⟨hp.1,h.2⟩
      · have hh : p.2=1/2 := h.2
        exfalso; linarith [hp.2.2]
      · have hh : p.1= -(1/2 : ℝ) := h.1
        exfalso; linarith [hp.1.1]
      · have hh : p.1=3/2 := h.1
        exfalso; linarith [hp.1.2]
    · exact fun hp => huq hp
  have hgcontact (p : P2) (hp : p ∈ halfArmPatch w) :
      g p ∈ frontier halfArmRectangle ↔ p ∈ armAttachment := by
    have hm := hmap hp
    have hz : (g p).2=0 ↔ p ∈ armAttachment := (hzero p hp).trans
      (by exact ⟨fun h => ⟨hp.1,h⟩,fun h => h.2⟩)
    constructor
    · intro h
      rw [halfArmRectangle,frontier_rectangle_eq_four_sides (by norm_num) (by norm_num)] at h
      apply hz.mp
      rcases h with (h | h) | (h | h)
      · exact h.2
      · have hh : (g p).2=1/2 := h.2
        exfalso; linarith [hm.2.2]
      · have hh : (g p).1= -(1/2 : ℝ) := h.1
        exfalso; linarith [hm.1.1]
      · have hh : (g p).1=3/2 := h.1
        exfalso; linarith [hm.1.2]
    · intro h
      rw [halfArmRectangle,frontier_rectangle_eq_four_sides (by norm_num) (by norm_num)]
      exact Or.inl (Or.inl ⟨Ioo_subset_Icc_self hm.1,hz.mpr h⟩)
  exact exists_attached_patch_extension hs hd hds armAttachment_ball hub huq
    (by simp) hcontact hg hgi
    (fun p hp => ⟨Ioo_subset_Icc_self (hmap hp).1,Ico_subset_Icc_self (hmap hp).2⟩)
    (fun p hp => by
      have heq : p=(p.1,0) := Prod.ext rfl hp.2
      exact (congrArg g heq).trans ((hcenter p.1 hp.1).trans heq.symm)) hgcontact

end PoincareConjecture.M76.Dehn.Annuli.RimBands
