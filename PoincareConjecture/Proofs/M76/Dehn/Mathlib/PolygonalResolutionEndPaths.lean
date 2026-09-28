import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonalStripDiskAttachment
import PoincareConjecture.Proofs.M76.Mathlib.ConvexSubtypePaths

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "C3" => ((ℝ × ℝ) × ℝ)

def endSquare (t : ℝ) : Set C3 :=
  (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ {t}

def endCenter (t : ℝ) : endSquare t := ⟨((0, 0), t), by
  norm_num [endSquare]⟩

private theorem convex_endSquare (t : ℝ) : Convex ℝ (endSquare t) :=
  ((convex_Icc (-1 : ℝ) 1).prod (convex_Icc (-1 : ℝ) 1)).prod (convex_singleton t)

theorem exists_resolution_end_path
    {X : Type*} [TopologicalSpace X] {b : ℝ} (hb : b < 1)
    (t : unitInterval) (alternatePair positive : Bool) :
    ∃ (a c : endSquare (t : ℝ)) (p : Path a c)
      (ra : Path (endCenter t) a) (rc : Path (endCenter t) c),
      (a : C3) = resolutionMap 0 alternatePair positive ((t : ℝ), -1) ∧
      (c : C3) = resolutionMap 0 alternatePair positive ((t : ℝ), 1) ∧
      (∀ s : unitInterval, (p s : C3) =
        resolutionMap b alternatePair positive ((t : ℝ), 2 * (s : ℝ) - 1)) ∧
      (∀ s : unitInterval, (ra s : C3) =
        AffineMap.lineMap ((0, 0), (t : ℝ)) (a : C3) (s : ℝ)) ∧
      (∀ s : unitInterval, (rc s : C3) =
        AffineMap.lineMap ((0, 0), (t : ℝ)) (c : C3) (s : ℝ)) ∧
      p.Homotopic (ra.symm.trans rc) ∧
      ∀ f : C(endSquare (t : ℝ), X),
        (p.map f.continuous).Homotopic
          ((ra.map f.continuous).symm.trans (rc.map f.continuous)) := by
  have hres : Continuous (resolutionMap b alternatePair positive) := by
    cases alternatePair with
    | false => exact (continuous_maps b positive).1
    | true => exact (continuous_maps b positive).2
  have hmem (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      resolutionMap b alternatePair positive ((t : ℝ), u) ∈ endSquare (t : ℝ) := by
    have hp : ((t : ℝ), u) ∈ source := ⟨t.property, hu⟩
    cases alternatePair with
    | false =>
      exact ⟨((mapsTo_tube hb.le positive).1 hp).1, rfl⟩
    | true =>
      exact ⟨((mapsTo_tube hb.le positive).2 hp).1, rfl⟩
  let a : endSquare (t : ℝ) :=
    ⟨resolutionMap b alternatePair positive ((t : ℝ), -1), hmem (-1) (by norm_num)⟩
  let c : endSquare (t : ℝ) :=
    ⟨resolutionMap b alternatePair positive ((t : ℝ), 1), hmem 1 (by norm_num)⟩
  have hparam (s : unitInterval) : 2 * (s : ℝ) - 1 ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [s.property.1, s.property.2]
  have hparam_cont : Continuous
      (fun s : unitInterval => ((t : ℝ), 2 * (s : ℝ) - 1)) := by fun_prop
  let p : Path a c :=
    { toFun := fun s =>
        ⟨resolutionMap b alternatePair positive ((t : ℝ), 2 * (s : ℝ) - 1),
          hmem _ (hparam s)⟩
      continuous_toFun := (hres.comp hparam_cont).subtype_mk _
      source' := by apply Subtype.ext; simp [a]
      target' := by apply Subtype.ext; norm_num [c] }
  let ra := Path.segmentIn (endSquare (t : ℝ)) (endCenter t) a
    ((convex_endSquare t).segment_subset (endCenter t).property a.property)
  let rc := Path.segmentIn (endSquare (t : ℝ)) (endCenter t) c
    ((convex_endSquare t).segment_subset (endCenter t).property c.property)
  have hpath : p.Homotopic (ra.symm.trans rc) :=
    Path.homotopic_of_convex_range (convex_endSquare t) Subset.rfl p
      (ra.symm.trans rc) (fun s => (p s).property)
      (fun s => ((ra.symm.trans rc) s).property)
  have hkeep (u : ℝ) (hu : |u| = 1) :
      resolutionMap b alternatePair positive ((t : ℝ), u) =
        resolutionMap 0 alternatePair positive ((t : ℝ), u) := by
    have hbound : b ≤ |((t : ℝ), u).2| := by simpa only [hu] using hb.le
    cases alternatePair with
    | false => exact (eq_zero_of_outer positive _ hbound).1
    | true => exact (eq_zero_of_outer positive _ hbound).2
  refine ⟨a, c, p, ra, rc, hkeep (-1) (by norm_num), hkeep 1 (by norm_num),
    fun _ => rfl, fun _ => rfl, fun _ => rfl, hpath, ?_⟩
  intro f
  have h := hpath.map f
  rw [Path.map_trans, ← Path.map_symm] at h
  exact h

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
