import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Composition.Family
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.DiskChangeImages

set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ V} {j : V → t.Carrier} {R Fmark : Set M}
  {D : MarkedSurfacePositionData step K₀ A₀ j R Fmark}

namespace FiniteMarkedSurfaceRepairs

variable (F : FiniteMarkedSurfaceRepairs D)

noncomputable def composite : I → t.Carrier ≃ₜ t.Carrier :=
  composeSupportedMotions F.motion (List.finRange F.size)

theorem nonempty_projected_crossing
    (a b : D.K.space) (hab : a ≠ b)
    (hpair : (step.projection ∘ step.inclusion) (F.composite 1 (D.endpoint a)) =
      (step.projection ∘ step.inclusion) (F.composite 1 (D.endpoint b))) :
    Nonempty (ProjectedSourceCrossing s.charts (step.projection ∘ step.inclusion)
      (F.composite 1 ∘ D.endpoint) D.K.space (s.projection ⁻¹' R) a b) := by
  classical
  let p := step.projection ∘ step.inclusion
  let l := List.finRange F.size
  have hl : l.Nodup := List.nodup_finRange _
  let H := F.composite 1
  let Changed := ⋃ k ∈ l, p '' (F.small k ∪ F.motion k 1 '' F.small k)
  have himage (G : t.Carrier ≃ₜ t.Carrier) :
      (G ∘ D.endpoint) '' D.K.space = G '' (D.endpoint '' D.K.space) :=
    (image_image G D.endpoint D.K.space).symm
  change p (H (D.endpoint a)) = p (H (D.endpoint b)) at hpair
  have hPV (k : Fin F.size) : p '' (F.small k ∪ F.motion k 1 '' F.small k) ⊆ F.window k := by
    rintro y ⟨x, hx | ⟨z, hz, rfl⟩, rfl⟩
    · exact F.small_window k hx
    · exact supported_homeomorph_mapsTo (F.motion k 1) (F.outside k 1) (F.small_window k hz)
  by_cases hy : p (H (D.endpoint a)) ∈ Changed
  · obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp hy
    have hyV := hPV k hyk
    have hval (x : t.Carrier) (hx : p (F.motion k 1 x) ∈ F.window k ∨ p (H x) ∈ F.window k) :
        H x = F.motion k 1 x :=
      composeSupportedMotions_agree_of_output_mem p F.motion F.window F.outside F.disjoint
        l hl 1 hk hx
    have ha := hval (D.endpoint a) (Or.inr hyV)
    have hb := hval (D.endpoint b) (Or.inr (hpair ▸ hyV))
    have hpairk : p (F.motion k 1 (D.endpoint a)) = p (F.motion k 1 (D.endpoint b)) := by
      simpa only [ha, hb] using hpair
    obtain ⟨B, hBV⟩ := F.crossings k a b hab hpairk (ha ▸ hyk)
    refine ⟨B.transport ha hb ?_⟩
    intro A₀ z hz
    change z ∈ p '' ((H ∘ D.endpoint) '' D.K.space ∩ A₀) ↔
      z ∈ p '' ((F.motion k 1 ∘ D.endpoint) '' D.K.space ∩ A₀)
    rw [himage H, himage (F.motion k 1)]
    exact composeSupportedMotions_branch_iff p F.motion F.window F.outside F.disjoint
      l hl 1 hk (D.endpoint '' D.K.space) A₀ (hBV hz)
  · have hclosed : IsClosed Changed := isClosed_finite_disk_change p
      (step.projection.continuous.comp step.inclusion.continuous)
        F.motion F.small F.compact l 1
    have hval (x : V) (hx : x ∈ D.K.space)
        (hz : p (D.endpoint x) ∉ Changed ∨ p (H (D.endpoint x)) ∉ Changed) :
        H (D.endpoint x) = D.endpoint x :=
      composeSupportedMotions_disk_agree_off_change p F.motion F.window F.outside F.disjoint
        (D.endpoint '' D.K.space) F.small F.small_window F.source_fixed l hl 1
        (mem_image_of_mem D.endpoint hx) hz
    have ha := hval a a.property (Or.inr hy)
    have hb := hval b b.property (Or.inr (hpair ▸ hy))
    have hpairOld : D.projected a = D.projected b := by
      change p (D.endpoint a) = p (D.endpoint b)
      simpa only [ha, hb] using hpair
    have haOld : p (D.endpoint a) ∉ Changed := ha ▸ hy
    have hex : D.projected a ∉ D.exceptionalValues := by
      intro he
      have heD : D.projected a ∈ (fun z : V × V => D.projected z.1) '' D.repairPairs :=
        ⟨(a, b), (D.mem_repairPairs_iff a.property b.property
          (fun h => hab (Subtype.ext h)) hpairOld).mpr he, rfl⟩
      obtain ⟨k, x, hx, hval⟩ := mem_iUnion.mp (F.cover heD)
      exact haOld (mem_iUnion₂.mpr ⟨k, List.mem_finRange _, x, Or.inl hx, hval⟩)
    obtain ⟨w, T, hlabels, hpoint, hsource, _, hPL, _, _, hleft, hright⟩ :=
      D.exists_whole_projected_crossing a.property b.property
        (fun h ↦ hab (Subtype.ext h)) hpairOld hex Changedᶜ hclosed.isOpen_compl haOld
    let B : ProjectedSourceCrossing s.charts p D.endpoint D.K.space
        (s.projection ⁻¹' R) a b := {
      window := w
      chart := T
      labels := hlabels
      point := hpoint
      source := fun _ hz ↦ (hsource hz).2.2
      compatible := hPL
      left_image := fun z hz ↦ (hleft z hz).trans
        ⟨fun h ↦ ⟨h, interior_subset (hsource hz).2.1⟩, And.left⟩
      right_image := fun z hz ↦ (hright z hz).trans
        ⟨fun h ↦ ⟨h, interior_subset (hsource hz).2.1⟩, And.left⟩
      region := Or.inl (fun _ hz ↦ (hsource hz).2.1) }
    refine ⟨B.transport ha hb ?_⟩
    intro A₀ z hz
    have hzC := (hsource hz).1
    change z ∉ ⋃ k ∈ l, p '' (F.small k ∪ F.motion k 1 '' F.small k) at hzC
    have heq := composeSupportedMotions_disk_branch_image_off_change p F.motion F.window
      F.outside F.disjoint (D.endpoint '' D.K.space) F.small F.small_window F.source_fixed
      l hl 1 A₀
    have hm := congrArg (fun Z : Set s.Carrier ↦ z ∈ Z) heq
    change z ∈ p '' ((H ∘ D.endpoint) '' D.K.space ∩ A₀) ↔
      z ∈ p '' (D.endpoint '' D.K.space ∩ A₀)
    rw [himage H]
    change z ∈ p '' (composeSupportedMotions F.motion l 1 '' D.endpoint '' D.K.space ∩ A₀) ↔ _
    exact Eq.to_iff (by simpa only [mem_sdiff, hzC, not_false_eq_true, and_true] using hm)

end FiniteMarkedSurfaceRepairs
end Geometry.OriginalPLTower
