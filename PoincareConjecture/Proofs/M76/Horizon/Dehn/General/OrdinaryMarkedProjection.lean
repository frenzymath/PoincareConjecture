import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.InteriorExceptionRepair
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.BoundaryExceptionRepair
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.OriginalGeneralPositionSchedule
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.ScheduledProjectedCrossings
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.OriginalStageModel











set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem Step.exists_ordinary_marked_projection
    {M ι : Type*} [TopologicalSpace M]
    {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
    {f : V2 → M} {r : M → ℝ} {C : Set M}
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    (old : StageMarkedDisk t R Fmark base Jgroup) :
    ∃ new : StageMarkedDisk t R Fmark base Jgroup,
      Nonempty (OrdinaryDoubleCurveModel s.charts
        (step.projection ∘ step.inclusion ∘ new.map) (s.projection ⁻¹' R)) := by
  classical
  let data := step.originalGeneralPositionData he hF hopen old
  obtain ⟨n, q, w, V, hV, hdis, _hpre, _hbranches⟩ := data.exists_exception_schedule
  let p := step.projection ∘ step.inclusion
  have repairs (k : Fin n) :
      ∃ (G : I → t.Carrier ≃ₜ t.Carrier) (Small : Set t.Carrier),
        Continuous (fun z : I × t.Carrier ↦ G z.1 z.2) ∧
        Continuous (fun z : I × t.Carrier ↦ (G z.1).symm z.2) ∧
        (∀ x, G 0 x = x) ∧
        (∀ i j, (t.charts i).symm.trans
          ((G 1).toOpenPartialHomeomorph.trans (t.charts j)) ∈ piecewiseAffineGroupoid V3) ∧
        (∀ u, (G u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R) ∧
        (∀ u, (G u) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark) ∧
        (∀ u, EqOn (G u) id (p ⁻¹' V k)ᶜ) ∧
        IsCompact Small ∧ Small ⊆ p ⁻¹' V k ∧
        (∀ u, EqOn (G u) id (data.initial.map '' D2 \ Small)) ∧
        (q k : s.Carrier) ∈ p '' Small ∧
        ∀ x y : D2, x ≠ y →
          p (G 1 (data.initial.map x)) = p (G 1 (data.initial.map y)) →
          p (G 1 (data.initial.map x)) ∈ p '' (Small ∪ G 1 '' Small) →
          ∃ B : ProjectedDiskCrossing s.charts p (G 1 ∘ data.initial.map)
            (s.projection ⁻¹' R) x y, B.chart.source ⊆ V k := by
    obtain ⟨hopenV, hqV, _hcompactV, _hwindow, _hisolate, a, b, hab,
      hex, _ha, _hb, hvalue⟩ := hV k
    have hpair : p (data.initial.map a) = p (data.initial.map b) :=
      (data.relation_space.subset (data.exceptional_eq.subset hex).1).2.2.1
    have haV : p (data.initial.map a) ∈ V k := by
      change step.projection (step.inclusion (data.initial.map a)) ∈ V k
      rw [hvalue]
      exact hqV
    rw [← hvalue]
    by_cases haRim : (a : V2) ∈ Q2
    · exact data.exists_boundary_exception_repair he hF hopen a b hab haRim
        hpair (V k) hopenV haV
    · exact data.exists_interior_exception_repair he hF hopen a b hab haRim
        hpair (V k) hopenV haV
  choose G Small hG hGinv hzero hPL hregion hmark hfix hSmall hSV hdisk hcenter hrepair
    using repairs
  let l : List (Fin n) := List.ofFn id
  have hl : l.Nodup := List.nodup_ofFn.mpr Function.injective_id
  have hmem (k : Fin n) : k ∈ l := by simp [l]
  have hdisV : Pairwise (fun k j ↦ Disjoint (V k) (V j)) :=
    fun k j hkj ↦ (hdis hkj).mono subset_closure subset_closure
  have hcover : ∀ z ∈ data.exceptional,
      p (data.initial.map z.1) ∈ ⋃ k ∈ l, p '' Small k := by
    intro z hz
    let point : (fun z : V2 × V2 ↦ p (data.initial.map z.1)) '' data.exceptional :=
      ⟨p (data.initial.map z.1), ⟨z, hz, rfl⟩⟩
    let k := q.symm point
    have hk : (q k : s.Carrier) = p (data.initial.map z.1) :=
      congrArg Subtype.val (q.apply_symm_apply point)
    exact mem_iUnion₂.mpr ⟨k, hmem k, hk ▸ hcenter k⟩
  obtain ⟨new, _eta, _hmap, _hvalues, _hbase, hcross⟩ :=
    data.exists_scheduled_crossed_marked_disk G hG hzero hPL hregion hmark
      V hfix hdisV Small hSmall hSV hdisk l hl hcover (fun k _ ↦ hrepair k)
  refine ⟨new, step.nonempty_ordinary_double_curve_model new ?_⟩
  intro x hx y hy hne hpair
  obtain ⟨B⟩ := hcross ⟨x, hx⟩ ⟨y, hy⟩
    (fun h ↦ hne (congrArg Subtype.val h)) hpair
  exact ⟨B.window, B.chart, B.labels, B.point, B.source, B.compatible,
    B.left_image, B.right_image, B.region⟩

end Geometry.OriginalPLTower
