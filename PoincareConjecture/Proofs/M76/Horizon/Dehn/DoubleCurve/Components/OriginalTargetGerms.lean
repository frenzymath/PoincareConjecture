import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedTargetGerms
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Mathlib.OriginalStripDoubleLocus









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "D2" => closedBall (0 : V2) 1

variable {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X F}
  {f : V2 → X} {Z : Set X} {base : Z} {G : Subgroup (FundamentalGroup Z base)}
  {c : Bool → P2 → V2} {τ : C3 → X}
  {D : OriginalResolutionWordExclusionData f Z base G c τ (1 / 4)}



theorem OriginalNormalizedResolutionPairData.double_targets_avoid_tube
    (P : OriginalNormalizedResolutionPairData e D)
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source D2)
    (hdisj : Disjoint (c false '' source) (c true '' source))
    (hτ : InjOn τ tube)
    (hfull : D2 ∩ f ⁻¹' (τ '' tube) = (c false '' source) ∪ (c true '' source))
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfZ : ∀ x ∈ D2, f x ∈ Z ↔ x ∈ Q2) :
    (∀ x ∈ D2, ∀ y ∈ D2, P.gU x = P.gU y → x ≠ y → P.gU x ∉ τ '' tube) ∧
    (∀ x ∈ D2, ∀ y ∈ D2, P.gV x = P.gV y → x ≠ y → P.gV x ∉ τ '' tube) := by
  have hcenters := original_strip_centers_disjoint_exteriors c hci D.s0 D.s1
    (by simpa only [inter_comm] using D.strip0A) D.oppositeA.inter_eq
    (by simpa only [inter_comm] using D.strip0M)
    (by simpa only [inter_comm] using D.strip1M) D.oppositeC.inter_eq
    (by simpa only [inter_comm] using D.strip1C)
  have hbad : doubleLocusOn f D2 ∩ f ⁻¹' (τ '' tube) ⊆
      (c false '' arm 0) ∪ (c true '' arm 0) := by
    intro x hx
    exact (original_double_locus_inter_strips c hcS hdisj hτ hfull h0 h1).subset
      ⟨hx.1, hfull.subset ⟨hx.1.1, hx.2⟩⟩
  have hKV : Disjoint ((D.A ∪ D.M) ∪ D.C)
      ((c false '' arm 0) ∪ (c true '' arm 0)) :=
    (disjoint_union_left.mpr hcenters).symm
  have hKU : Disjoint (D.A ∪ D.C) ((c false '' arm 0) ∪ (c true '' arm 0)) :=
    hKV.mono_left (union_subset (subset_union_left.trans subset_union_left) subset_union_right)
  obtain ⟨factsU, factsV⟩ := P.retained_fibers hτ hfull h0 h1 hfZ
  exact ⟨fun _ hx _ hy hxy hne ↦ factsU.double_target_avoids hbad hKU hx hy hxy hne,
    fun _ hx _ hy hxy hne ↦ factsV.double_target_avoids hbad hKV hx hy hxy hne⟩




theorem OriginalNormalizedResolutionPairData.exists_double_target_germs
    [T2Space X] (P : OriginalNormalizedResolutionPairData e D)
    (hf : ContinuousOn f D2) (hτc : ContinuousOn τ tube)
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source D2)
    (hdisj : Disjoint (c false '' source) (c true '' source))
    (hτ : InjOn τ tube)
    (hfull : D2 ∩ f ⁻¹' (τ '' tube) = (c false '' source) ∪ (c true '' source))
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfZ : ∀ x ∈ D2, f x ∈ Z ↔ x ∈ Q2)
    (partner : doubleLocusOn f D2 → doubleLocusOn f D2)
    (hunique : ∀ (x : doubleLocusOn f D2) (y : V2), y ∈ D2 →
      f x = f y → (x : V2) ≠ y → y = (partner x : V2)) :
    (∀ x ∈ D2, ∀ y ∈ D2, P.gU x = P.gU y → x ≠ y →
      ∃ W : Set X, IsOpen W ∧ P.gU x ∈ W ∧ P.gU '' D2 ∩ W = f '' D2 ∩ W) ∧
    (∀ x ∈ D2, ∀ y ∈ D2, P.gV x = P.gV y → x ≠ y →
      ∃ W : Set X, IsOpen W ∧ P.gV x ∈ W ∧ P.gV '' D2 ∩ W = f '' D2 ∩ W) := by
  obtain ⟨factsU, factsV⟩ := P.retained_fibers hτ hfull h0 h1 hfZ
  obtain ⟨havoidU, havoidV⟩ := P.double_targets_avoid_tube hci hcS hdisj hτ hfull h0 h1 hfZ
  have hMS : D.M ⊆ D2 := fun _ hx ↦ D.cover.subset (Or.inl (Or.inl (Or.inr hx)))
  have hKM : Disjoint (D.A ∪ D.C) D.M :=
    disjoint_union_left.mpr ⟨D.disjointAM, D.disjointMC.symm⟩
  have htube : IsCompact (τ '' tube) :=
    ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).image_of_continuousOn hτc
  have hM : IsCompact (f '' D.M) := D.diskM.isCompact.image_of_continuousOn (hf.mono hMS)
  have hstrips : f '' ((c false '' source) ∪ (c true '' source)) ⊆ τ '' tube := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hfull.symm.subset hz).2
  have hcoverU : D2 ⊆ (D.A ∪ D.C) ∪ (D.M ∪ ((c false '' source) ∪ (c true '' source))) := by
    intro z hz
    rcases D.cover.symm.subset hz with ((ha | hm) | hc) | hs
    · exact Or.inl (Or.inl ha)
    · exact Or.inr (Or.inl hm)
    · exact Or.inl (Or.inr hc)
    · exact Or.inr (Or.inr hs)
  constructor
  · intro x hx y hy hxy hne
    have hxM : P.gU x ∉ f '' D.M := by
      rintro ⟨z, hz, hzval⟩
      exact disjoint_left.mp hKM
        (factsU.old_fiber_subset partner hunique hx hy hxy hne ⟨hMS hz, hzval⟩) hz
    refine ⟨(f '' D.M ∪ τ '' tube)ᶜ, (hM.union htube).isClosed.isOpen_compl,
      fun h ↦ h.elim hxM (havoidU x hx y hy hxy hne), ?_⟩
    apply factsU.image_inter_eq hcoverU P.images_subset_original.1
    apply disjoint_left.mpr
    intro z hz hn
    apply hz
    rcases hn with ⟨a, ha | ha, rfl⟩ | ht
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr (hstrips ⟨a, ha, rfl⟩)
    · exact Or.inr ht
  · intro x hx y hy hxy hne
    refine ⟨(τ '' tube)ᶜ, htube.isClosed.isOpen_compl, havoidV x hx y hy hxy hne, ?_⟩
    apply factsV.image_inter_eq D.cover.symm.subset P.images_subset_original.2
    apply disjoint_left.mpr
    intro z hz hn
    exact hz (hn.elim (fun h ↦ hstrips h) id)

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
