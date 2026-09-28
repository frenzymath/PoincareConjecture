import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Cup.ExteriorCollar

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryCup

open PolygonalCrossingResolution
local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_boundary_cup_retained_core
    {X E : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {c : P2 → E} (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    {B D O S : Set E} (hS : IsCompact S) (hO : IsCompact O)
    (hBS : B ⊆ S)
    (hsource : S ⊆ O ∪ D) (hOD : O ∩ D = c '' arm 0)
    (htrim : B ∩ (c '' halfSource true) = c '' arm 1)
    (hcover : (c '' halfSource true) ∪ B = D)
    {f : E → X} (hf : ContinuousOn f S) (hfi : InjOn f S)
    {C Sigma : Set X} (hcap : C ∩ (f '' S) = f '' B)
    (hCS : f '' B ⊆ Sigma)
    {p : I × I → X}
    (hpimage : range p = f '' (c '' (I ×ˢ Icc (1 / 2 : ℝ) 1))) :
    ∃ Z : Set X, IsClosed Z ∧ Disjoint C Z ∧
      f '' S ⊆ Sigma ∪ range p ∪ Z := by
  let low := I ×ˢ Icc (0 : ℝ) (1 / 2)
  have hlow : low ⊆ source := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    constructor <;> linarith [hx.2.1, hx.2.2]
  have hlowCompact : IsCompact (c '' low) :=
    (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn (hc.continuousOn.mono hlow)
  let K := S ∩ (O ∪ c '' low)
  have hK : IsCompact K := hS.inter (hO.union hlowCompact)
  have hBD : B ⊆ D := subset_union_right.trans hcover.subset
  have hBcenter : Disjoint B (c '' arm 0) := by
    apply Set.disjoint_left.mpr
    intro x hxB hx0
    have hx1 := htrim.subset ⟨hxB, (image_mono (arm_zero_subset_halfSource true)) hx0⟩
    exact Set.disjoint_left.mp (disjoint_center_far_images c hci true) hx0 hx1
  have hBO : Disjoint B O := by
    apply Set.disjoint_left.mpr
    intro x hxB hxO
    exact Set.disjoint_left.mp hBcenter hxB (hOD.subset ⟨hxO, hBD hxB⟩)
  have hBlow : Disjoint B (c '' low) := by
    apply Set.disjoint_left.mpr
    rintro x hxB ⟨r, hr, rfl⟩
    have hrH : r ∈ halfSource true := ⟨hr.1, hr.2.1, by linarith [hr.2.2]⟩
    obtain ⟨s, hs, hsr⟩ := htrim.subset ⟨hxB, ⟨r, hrH, rfl⟩⟩
    have hsS : s ∈ source := ⟨hs.1, by rw [show s.2 = 1 from hs.2]; norm_num⟩
    have heq := hci hsS (hlow hr) hsr
    have hheight : r.2 = 1 := (congrArg Prod.snd heq).symm.trans hs.2
    have hh := hr.2.2
    rw [hheight] at hh
    norm_num at hh
  let Z := f '' K
  have hZ : IsClosed Z := (hK.image_of_continuousOn (hf.mono inter_subset_left)).isClosed
  have hCZ : Disjoint C Z := by
    apply Set.disjoint_left.mpr
    rintro z hzC ⟨x, hxK, rfl⟩
    obtain ⟨b, hb, hbx⟩ := hcap.subset ⟨hzC, ⟨x, hxK.1, rfl⟩⟩
    have hxB : x ∈ B := (hfi (hBS hb) hxK.1 hbx) ▸ hb
    rcases hxK.2 with hxO | hxLow
    · exact Set.disjoint_left.mp hBO hxB hxO
    · exact Set.disjoint_left.mp hBlow hxB hxLow
  refine ⟨Z, hZ, hCZ, ?_⟩
  rintro z ⟨x, hxS, rfl⟩
  rcases hsource hxS with hxO | hxD
  · exact Or.inr ⟨x, ⟨hxS, Or.inl hxO⟩, rfl⟩
  · rcases hcover.superset hxD with hxH | hxB
    · obtain ⟨r, hr, rfl⟩ := hxH
      by_cases hlowhalf : r.2 ≤ 1 / 2
      · exact Or.inr ⟨c r, ⟨hxS, Or.inr ⟨r, ⟨hr.1, hr.2.1, hlowhalf⟩, rfl⟩⟩, rfl⟩
      · exact Or.inl (Or.inr (hpimage.superset
          ⟨c r, ⟨r, ⟨hr.1, (lt_of_not_ge hlowhalf).le, hr.2.2⟩, rfl⟩, rfl⟩))
    · exact Or.inl (Or.inl (hCS ⟨x, hxB, rfl⟩))

end PoincareConjecture.M76.Dehn.Annuli.BoundaryCup
