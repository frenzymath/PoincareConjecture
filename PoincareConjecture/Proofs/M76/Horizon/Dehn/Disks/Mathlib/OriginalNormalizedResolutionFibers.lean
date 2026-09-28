import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.OriginalNormalizedResolutionPair
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.UpperResolutionDoubleRelation
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.AlternateResolutionDoubleRelation
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.JoinedSourceContinuity

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "D2" => closedBall (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1

structure RetainedSquareMapFacts {X : Type*} (f g : V2 → X)
    (S : Set V2) (j : S → V2) : Prop where
  old_subset : S ⊆ D2
  injective : Function.Injective j
  continuous : Continuous j
  mapsTo : ∀ x, j x ∈ D2
  keep : ∀ x, g (j x) = f x
  boundary : ∀ x, j x ∈ Q2 ↔ (x : V2) ∈ Q2
  double_relation :
    {v : V2 × V2 | v.1 ∈ D2 ∧ v.2 ∈ D2 ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} =
      (fun v : S × S ↦ (j v.1, j v.2)) ''
        {v | f v.1 = f v.2 ∧ (v.1 : V2) ≠ v.2}
  double_locus :
    {z : V2 | z ∈ D2 ∧ ∃ w ∈ D2, g z = g w ∧ z ≠ w} =
      j '' {x : S | ∃ y : S, f x = f y ∧ (x : V2) ≠ y}

variable {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X F}
  {f : V2 → X} {Z : Set X} {base : Z} {G : Subgroup (FundamentalGroup Z base)}
  {c : Bool → P2 → V2} {τ : C3 → X}
  {D : OriginalResolutionWordExclusionData f Z base G c τ (1 / 4)}

noncomputable def OriginalNormalizedResolutionPairData.retainedUpperCopy
    (P : OriginalNormalizedResolutionPairData e D) : (D.A ∪ D.C : Set V2) → V2 :=
  joinSourceCopies D.disjointAC P.sourceU.jA P.sourceU.jC

noncomputable def OriginalNormalizedResolutionPairData.retainedAlternateCopy
    (P : OriginalNormalizedResolutionPairData e D) : ((D.A ∪ D.M) ∪ D.C : Set V2) → V2 :=
  joinSourceCopies (disjoint_union_left.mpr ⟨D.disjointAC, D.disjointMC⟩)
    (joinSourceCopies D.disjointAM P.sourceV.jA P.sourceV.jM) P.sourceV.jC

theorem OriginalNormalizedResolutionPairData.retained_fibers
    (P : OriginalNormalizedResolutionPairData e D)
    (hτ : InjOn τ tube)
    (hfull : D2 ∩ f ⁻¹' (τ '' tube) = (c false '' source) ∪ (c true '' source))
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfZ : ∀ x ∈ D2, f x ∈ Z ↔ x ∈ Q2) :
    RetainedSquareMapFacts f P.gU (D.A ∪ D.C) P.retainedUpperCopy ∧
      RetainedSquareMapFacts f P.gV ((D.A ∪ D.M) ∪ D.C) P.retainedAlternateCopy := by
  have hAS : D.A ⊆ D2 := fun x hx ↦ D.cover.subset (Or.inl (Or.inl (Or.inl hx)))
  have hMS : D.M ⊆ D2 := fun x hx ↦ D.cover.subset (Or.inl (Or.inl (Or.inr hx)))
  have hCS : D.C ⊆ D2 := fun x hx ↦ D.cover.subset (Or.inl (Or.inr hx))
  have hUS : D.A ∪ D.C ⊆ D2 := union_subset hAS hCS
  have hVS : (D.A ∪ D.M) ∪ D.C ⊆ D2 := union_subset (union_subset hAS hMS) hCS
  let τ' := τ ∘ tubeArmOrientation D.s0 D.s1
  have hτ' : InjOn τ' tube := by
    intro x hx y hy hxy
    apply tubeArmOrientation_injective D.s0 D.s1
    exact hτ ((tubeArmOrientation_mem_tube D.s0 D.s1 x).mpr hx)
      ((tubeArmOrientation_mem_tube D.s0 D.s1 y).mpr hy) hxy
  have hfull' : D2 ∩ f ⁻¹' (τ' '' tube) = (c false '' source) ∪ (c true '' source) := by
    simpa only [τ', reoriented_tube_image] using hfull
  have hrange (i s : Bool) : c i '' arm (farArmParameter s) =
      range (fun t : I01 ↦ c i ((t : ℝ), farArmParameter s)) := by
    ext y
    constructor
    · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
      have he : u = farArmParameter s := hu
      subst u
      exact ⟨⟨t, ht⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨((t : ℝ), farArmParameter s), ⟨t.property, rfl⟩, rfl⟩
  have hA0 : D.A ∩ (c false '' source) =
      range (fun t : I01 ↦ c false ((t : ℝ), farArmParameter (!D.s0))) := by
    rw [inter_comm, D.strip0A, hrange]
  have hA1 : D.A ∩ (c true '' source) = ∅ := disjoint_iff_inter_eq_empty.mp D.oppositeA
  have hM0 : D.M ∩ (c false '' source) =
      range (fun t : I01 ↦ c false ((t : ℝ), farArmParameter D.s0)) := by
    rw [inter_comm, D.strip0M, hrange]
  have hM1 : D.M ∩ (c true '' source) =
      range (fun t : I01 ↦ c true ((t : ℝ), farArmParameter D.s1)) := by
    rw [inter_comm, D.strip1M, hrange]
  have hC0 : D.C ∩ (c false '' source) = ∅ := disjoint_iff_inter_eq_empty.mp D.oppositeC
  have hC1 : D.C ∩ (c true '' source) =
      range (fun t : I01 ↦ c true ((t : ℝ), farArmParameter (!D.s1))) := by
    rw [inter_comm, D.strip1C, hrange]
  have hcorners := reoriented_tube_old_arm_equations f (c false) (c true) τ h0 h1 D.s0 D.s1
  obtain ⟨hinjU, hrangeU, hkeepU, hrelU, hlocusU⟩ :=
    upper_retained_double_relation P.sourceU D.disjointAC hτ' hfull' hAS hCS hA0 hA1 hC0 hC1
      (fun t ↦ (hcorners t).1) (fun t ↦ (hcorners t).2.2.2)
  obtain ⟨hinjV, hrangeV, hkeepV, hrelV, hlocusV⟩ :=
    alternate_retained_double_relation P.sourceV D.disjointAM D.disjointAC D.disjointMC
      hτ' hfull' hAS hMS hCS hA0 hA1 hM0 hM1 hC0 hC1
      (fun t ↦ (hcorners t).1) (fun t ↦ (hcorners t).2.1)
      (fun t ↦ (hcorners t).2.2.1) (fun t ↦ (hcorners t).2.2.2)
  have hmemU (x : (D.A ∪ D.C : Set V2)) : P.retainedUpperCopy x ∈ D2 := by
    rcases hrangeU.subset (mem_range_self x) with hxA | hxC
    · exact P.sourceU.cover.subset (Or.inl (Or.inl hxA))
    · exact P.sourceU.cover.subset (Or.inr hxC)
  have hmemV (x : ((D.A ∪ D.M) ∪ D.C : Set V2)) : P.retainedAlternateCopy x ∈ D2 := by
    rcases hrangeV.subset (mem_range_self x) with (hxA | hxM) | hxC
    · exact P.sourceV.cover.subset (Or.inl (Or.inl (Or.inl (Or.inl hxA))))
    · exact P.sourceV.cover.subset (Or.inl (Or.inl (Or.inr hxM)))
    · exact P.sourceV.cover.subset (Or.inr hxC)
  refine ⟨{
    old_subset := hUS
    injective := hinjU
    continuous := P.sourceU.retainedCopy_continuous D.diskA D.diskC D.disjointAC
    mapsTo := hmemU
    keep := hkeepU
    boundary := ?_
    double_relation := hrelU
    double_locus := hlocusU }, {
    old_subset := hVS
    injective := hinjV
    continuous := P.sourceV.retainedCopy_continuous D.diskA D.diskM D.diskC
      D.disjointAM D.disjointAC D.disjointMC
    mapsTo := hmemV
    keep := hkeepV
    boundary := ?_
    double_relation := hrelV
    double_locus := hlocusV }⟩
  · intro x
    have hk : P.gU (P.retainedUpperCopy x) = f x := hkeepU x
    exact (P.properU _ (hmemU x)).symm.trans
      ((Iff.of_eq (congrArg (fun y ↦ y ∈ Z) hk)).trans (hfZ x (hUS x.property)))
  · intro x
    have hk : P.gV (P.retainedAlternateCopy x) = f x := hkeepV x
    exact (P.properV _ (hmemV x)).symm.trans
      ((Iff.of_eq (congrArg (fun y ↦ y ∈ Z) hk)).trans (hfZ x (hVS x.property)))

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
