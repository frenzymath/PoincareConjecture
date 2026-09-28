import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Patches.SignedPatches

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem IntervalBandLift.exists_signed_arm_patches
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X} {j : V2 → X}
    {P : OriginalDiskProduct e Q j} {F : P2 → X} {b : Bool}
    (L : IntervalBandLift P F (rimArm b)) :
    ∃ (orientation : Bool) (v : ℝ), 0 < v ∧ v < 1/2 ∧ v ≤ L.width ∧
      ∃ H : Bool → halfArmRectangle ≃ₜ halfArmRectangle,
        (∀ a, (H a).IsFinitePL) ∧
        (∀ a (p : halfArmRectangle), (p : P2) ∈ frontier halfArmRectangle → H a p=p) ∧
        (∀ (a : Bool) (p : halfArmRectangle), (p : P2) ∈ halfArmPatch v →
          P.map (armPoint b (H a p : P2).1,sign a * (H a p : P2).2) =
            F (sign orientation * (sign a*(p : P2).2),(p : P2).1)) := by
  classical
  obtain ⟨w,g,hw,hwL,hg,hi,hmap,hcenter,hphysical,hzero⟩ := L.exists_planar_arm_lift
  obtain ⟨o,hG,hGi,hGc,hGz,hGp,hGn⟩ :=
    exists_oriented_strip_reparametrization hw hg hi hcenter hzero
  have hGmap : MapsTo (g ∘ stripReflection o) (parameter w)
      (Ioo (-(1/2 : ℝ)) (3/2) ×ˢ Ioo (-(1/2 : ℝ)) (1/2)) :=
    fun _ hp => hmap ((stripReflection_mem o).mpr hp)
  have hws : w ≤ 1/2 := hwL.trans L.small
  choose H hH hvalue hfrontier hpatch using fun a =>
    exists_oriented_half_patches hw hws hG hGi hGmap hGc hGz hGp hGn a
  refine ⟨o,w/2,half_pos hw,by linarith,by linarith,H,hH,hfrontier,?_⟩
  intro a p hp
  have hpinput : (sign o*(sign a*(p : P2).2),(p : P2).1) ∈ parameter w := by
    refine ⟨?_,hp.1⟩
    cases o <;> cases a <;> simp only [sign,Bool.false_eq_true,if_false,if_true,
      one_mul,neg_one_mul,neg_neg,mem_Icc]
    all_goals constructor <;> linarith [hp.2.1,hp.2.2]
  have hv := hvalue a ⟨p,hp⟩
  have hcoord :
      (armPoint b (H a p : P2).1,sign a * (H a p : P2).2) =
      (armPoint b (g (sign o*(sign a*(p : P2).2),(p : P2).1)).1,
        (g (sign o*(sign a*(p : P2).2),(p : P2).1)).2) := by
    rw [hv]
    cases a <;> simp [sign]
  exact (congrArg P.map hcoord).trans (hphysical _ hpinput)

end PoincareConjecture.M76.Dehn.Annuli.RimBands
