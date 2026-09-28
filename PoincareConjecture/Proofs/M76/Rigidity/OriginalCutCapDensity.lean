import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductCut

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

namespace OriginalDiskProduct

theorem exterior_rectangle_interior (P : OriginalDiskProduct e R j)
    (hR : IsCompact R) (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    {a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1)
    (hout : b ≤ -(1 / 2 : ℝ) ∨ (1 / 2 : ℝ) ≤ a) :
    P.map '' (ball (0 : V2) 1 ×ˢ Ioo a b) ⊆ interior P.cutCarrier := by
  rw [(P.cut_geometry hR hopen).2.1]
  rintro _ ⟨z, hz, rfl⟩
  have hzfull : z ∈ D ×ˢ I :=
    ⟨ball_subset_closedBall hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hzint : P.map z ∈ interior R := by
    apply (mem_interior_iff_notMem_frontier (P.inside hzfull)).mpr
    intro hfront
    have hq := (P.proper z hzfull).mp hfront
    have hnorm := mem_sphere_zero_iff_norm.mp hq
    have hnormlt := mem_ball_zero_iff.mp hz.1
    linarith
  refine ⟨hzint, ?_⟩
  rintro ⟨w, hw, hwz⟩
  have hwfull : w ∈ D ×ˢ I :=
    ⟨hw.1, by linarith [hw.2.1], by linarith [hw.2.2]⟩
  have ht := congrArg (fun x : E => x.2) (P.injective hwfull hzfull hwz)
  rcases hout with h | h
  · linarith [hw.2.1, hz.2.2]
  · linarith [hw.2.2, hz.2.1]

theorem exterior_closed_rectangle_closure (P : OriginalDiskProduct e R j)
    (hR : IsCompact R) (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    {a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1) (hab : a < b)
    (hout : b ≤ -(1 / 2 : ℝ) ∨ (1 / 2 : ℝ) ≤ a) :
    P.map '' (D ×ˢ Icc a b) ⊆ closure (interior P.cutCarrier) := by
  have hclosure : closure (ball (0 : V2) 1 ×ˢ Ioo a b) = D ×ˢ Icc a b := by
    rw [closure_prod_eq, closure_ball _ one_ne_zero, closure_Ioo hab.ne]
  have hc : ContinuousOn P.map (closure (ball (0 : V2) 1 ×ˢ Ioo a b)) := by
    rw [hclosure]
    apply P.polyhedral.continuousOn.mono
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have h := hc.image_closure.trans
    (closure_mono (P.exterior_rectangle_interior hR hopen ha hb hout))
  rwa [hclosure] at h

theorem endDisks_subset_closure_interior_cut (P : OriginalDiskProduct e R j)
    (hR : IsCompact R) (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip)) :
    P.endDisks ⊆ closure (interior P.cutCarrier) := by
  have hneg := P.exterior_closed_rectangle_closure hR hopen
    (a := -(3 / 4 : ℝ)) (b := -(1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (Or.inl le_rfl)
  have hpos := P.exterior_closed_rectangle_closure hR hopen
    (a := (1 / 2 : ℝ)) (b := (3 / 4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (Or.inr le_rfl)
  rintro _ ⟨z, hz, rfl⟩
  have ht : z.2 = -(1 / 2 : ℝ) ∨ z.2 = 1 / 2 := hz.2
  rcases ht with ht | ht
  · apply hneg
    exact ⟨z, ⟨hz.1, by rw [ht]; norm_num⟩, rfl⟩
  · apply hpos
    exact ⟨z, ⟨hz.1, by rw [ht]; norm_num⟩, rfl⟩

end OriginalDiskProduct
end PoincareConjecture.M76
