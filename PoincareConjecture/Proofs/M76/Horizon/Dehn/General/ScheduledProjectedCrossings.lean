import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.OriginalOldProjectedCrossings
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.DiskChangeImages
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.ScheduledMarkedDisk

set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

variable {M ι α : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t} {R Fmark : Set M}
  {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
  {old : StageMarkedDisk t R Fmark base Jgroup}

theorem OriginalGeneralPositionData.nonempty_scheduled_projected_crossing
    (data : OriginalGeneralPositionData step old)
    (F : α → I → t.Carrier ≃ₜ t.Carrier) (V : α → Set s.Carrier)
    (hfix : ∀ k u, EqOn (F k u) id ((step.projection ∘ step.inclusion) ⁻¹' V k)ᶜ)
    (hdis : Pairwise (fun k j ↦ Disjoint (V k) (V j)))
    (Small : α → Set t.Carrier) (hSmall : ∀ k, IsCompact (Small k))
    (hSV : ∀ k, Small k ⊆ (step.projection ∘ step.inclusion) ⁻¹' V k)
    (hdisk : ∀ k u, EqOn (F k u) id (data.initial.map '' D2 \ Small k))
    (l : List α) (hl : l.Nodup)
    (hcover : ∀ z ∈ data.exceptional,
      step.projection (step.inclusion (data.initial.map z.1)) ∈
        ⋃ k ∈ l, (step.projection ∘ step.inclusion) '' Small k)
    (hrepair : ∀ k ∈ l, ∀ a b : D2, a ≠ b →
      step.projection (step.inclusion (F k 1 (data.initial.map a))) =
        step.projection (step.inclusion (F k 1 (data.initial.map b))) →
      step.projection (step.inclusion (F k 1 (data.initial.map a))) ∈
        (step.projection ∘ step.inclusion) '' (Small k ∪ F k 1 '' Small k) →
      ∃ B : ProjectedDiskCrossing s.charts (step.projection ∘ step.inclusion)
        (F k 1 ∘ data.initial.map) (s.projection ⁻¹' R) a b,
        B.chart.source ⊆ V k)
    (a b : D2) (hab : a ≠ b)
    (hpair : step.projection (step.inclusion (composeSupportedMotions F l 1 (data.initial.map a))) =
      step.projection (step.inclusion (composeSupportedMotions F l 1 (data.initial.map b)))) :
    Nonempty (ProjectedDiskCrossing s.charts (step.projection ∘ step.inclusion)
      (composeSupportedMotions F l 1 ∘ data.initial.map) (s.projection ⁻¹' R) a b) := by
  classical
  let p := step.projection ∘ step.inclusion
  let H := composeSupportedMotions F l 1
  let Changed := ⋃ k ∈ l, p '' (Small k ∪ F k 1 '' Small k)
  have himage (G : t.Carrier ≃ₜ t.Carrier) :
      (G ∘ data.initial.map) '' D2 = G '' (data.initial.map '' D2) :=
    (image_image G data.initial.map D2).symm
  change p (H (data.initial.map a)) = p (H (data.initial.map b)) at hpair
  have hPV (k : α) : p '' (Small k ∪ F k 1 '' Small k) ⊆ V k := by
    rintro y ⟨x, hx | ⟨z, hz, rfl⟩, rfl⟩
    · exact hSV k hx
    · exact supported_homeomorph_mapsTo (F k 1) (hfix k 1) (hSV k hz)
  by_cases hy : p (H (data.initial.map a)) ∈ Changed
  · obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp hy
    have hyV := hPV k hyk
    have hval (x : t.Carrier) (hx : p (F k 1 x) ∈ V k ∨ p (H x) ∈ V k) :
        H x = F k 1 x :=
      composeSupportedMotions_agree_of_output_mem p F V hfix hdis l hl 1 hk hx
    have ha := hval (data.initial.map a) (Or.inr hyV)
    have hb := hval (data.initial.map b) (Or.inr (hpair ▸ hyV))
    have hpairk : p (F k 1 (data.initial.map a)) = p (F k 1 (data.initial.map b)) := by
      simpa only [ha, hb] using hpair
    obtain ⟨B, hBV⟩ := hrepair k hk a b hab hpairk (ha ▸ hyk)
    refine ⟨B.transport ha hb ?_⟩
    intro A z hz
    change z ∈ p '' ((H ∘ data.initial.map) '' D2 ∩ A) ↔
      z ∈ p '' ((F k 1 ∘ data.initial.map) '' D2 ∩ A)
    rw [himage H, himage (F k 1)]
    exact composeSupportedMotions_branch_iff p F V hfix hdis l hl 1 hk
      (data.initial.map '' D2) A (hBV hz)
  · have hclosed : IsClosed Changed := isClosed_finite_disk_change p
      (step.projection.continuous.comp step.inclusion.continuous) F Small hSmall l 1
    have hval (x : V2) (hx : x ∈ D2)
        (hz : p (data.initial.map x) ∉ Changed ∨ p (H (data.initial.map x)) ∉ Changed) :
        H (data.initial.map x) = data.initial.map x :=
      composeSupportedMotions_disk_agree_off_change p F V hfix hdis
        (data.initial.map '' D2) Small hSV hdisk l hl 1
        (mem_image_of_mem data.initial.map hx) hz
    have ha := hval a a.property (Or.inr hy)
    have hb := hval b b.property (Or.inr (hpair ▸ hy))
    have hpairOld : p (data.initial.map a) = p (data.initial.map b) := by
      simpa only [ha, hb] using hpair
    have haOld : p (data.initial.map a) ∉ Changed := ha ▸ hy
    have hex : ((a : V2), (b : V2)) ∉ data.exceptional := by
      intro he
      obtain ⟨k, hk, x, hx, hval⟩ := mem_iUnion₂.mp (hcover _ he)
      exact haOld (mem_iUnion₂.mpr ⟨k, hk, x, Or.inl hx, hval⟩)
    obtain ⟨B, hB⟩ := data.exists_old_projected_crossing a b hab hpairOld hex
      Changedᶜ hclosed.isOpen_compl haOld
    refine ⟨B.transport ha hb ?_⟩
    intro A z hz
    have hzC := hB hz
    change z ∉ ⋃ k ∈ l, p '' (Small k ∪ F k 1 '' Small k) at hzC
    have heq := composeSupportedMotions_disk_branch_image_off_change p F V hfix hdis
      (data.initial.map '' D2) Small hSV hdisk l hl 1 A
    have hm := congrArg (fun Z : Set s.Carrier ↦ z ∈ Z) heq
    change z ∈ p '' ((H ∘ data.initial.map) '' D2 ∩ A) ↔
      z ∈ p '' (data.initial.map '' D2 ∩ A)
    rw [himage H]
    exact Eq.to_iff (by simpa only [mem_sdiff, hzC, not_false_eq_true, and_true] using hm)

theorem OriginalGeneralPositionData.exists_scheduled_crossed_marked_disk
    (data : OriginalGeneralPositionData step old)
    (F : α → I → t.Carrier ≃ₜ t.Carrier)
    (hF : ∀ k, Continuous (fun z : I × t.Carrier ↦ F k z.1 z.2))
    (hzero : ∀ k x, F k 0 x = x)
    (hPL : ∀ k i j, (t.charts i).symm.trans
      ((F k 1).toOpenPartialHomeomorph.trans (t.charts j)) ∈ piecewiseAffineGroupoid V3)
    (hregion : ∀ k u, (F k u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R)
    (hmark : ∀ k u, (F k u) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark)
    (V : α → Set s.Carrier)
    (hfix : ∀ k u, EqOn (F k u) id ((step.projection ∘ step.inclusion) ⁻¹' V k)ᶜ)
    (hdis : Pairwise (fun k j ↦ Disjoint (V k) (V j)))
    (Small : α → Set t.Carrier) (hSmall : ∀ k, IsCompact (Small k))
    (hSV : ∀ k, Small k ⊆ (step.projection ∘ step.inclusion) ⁻¹' V k)
    (hdisk : ∀ k u, EqOn (F k u) id (data.initial.map '' D2 \ Small k))
    (l : List α) (hl : l.Nodup)
    (hcover : ∀ z ∈ data.exceptional,
      step.projection (step.inclusion (data.initial.map z.1)) ∈
        ⋃ k ∈ l, (step.projection ∘ step.inclusion) '' Small k)
    (hrepair : ∀ k ∈ l, ∀ a b : D2, a ≠ b →
      step.projection (step.inclusion (F k 1 (data.initial.map a))) =
        step.projection (step.inclusion (F k 1 (data.initial.map b))) →
      step.projection (step.inclusion (F k 1 (data.initial.map a))) ∈
        (step.projection ∘ step.inclusion) '' (Small k ∪ F k 1 '' Small k) →
      ∃ B : ProjectedDiskCrossing s.charts (step.projection ∘ step.inclusion)
        (F k 1 ∘ data.initial.map) (s.projection ⁻¹' R) a b,
        B.chart.source ⊆ V k) :
    ∃ (new : StageMarkedDisk t R Fmark base Jgroup)
      (eta : data.initial.rim.Homotopy new.rim),
      new.map = composeSupportedMotions F l 1 ∘ data.initial.map ∧
      (∀ u x, (eta (u, x) : M) =
        t.projection (composeSupportedMotions F l u (data.initial.map x))) ∧
      new.basepath = data.initial.basepath.trans (eta.evalAt squareRimBase) ∧
      ∀ a b : D2, a ≠ b →
        step.projection (step.inclusion (new.map a)) =
          step.projection (step.inclusion (new.map b)) →
        Nonempty (ProjectedDiskCrossing s.charts (step.projection ∘ step.inclusion)
          new.map (s.projection ⁻¹' R) a b) := by
  obtain ⟨new, eta, hmap, hvalues, hbase⟩ :=
    data.initial.exists_finite_moved_marked_disk F hF hzero hPL hregion hmark l
  refine ⟨new, eta, hmap, hvalues, hbase, ?_⟩
  intro a b hab hpair
  rw [hmap] at hpair ⊢
  exact data.nonempty_scheduled_projected_crossing F V hfix hdis Small hSmall hSV
    hdisk l hl hcover hrepair a b hab hpair

end Geometry.OriginalPLTower
