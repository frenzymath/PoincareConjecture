import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.Sectors.Intersections
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch

universe u
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] {r : M → ℝ} {p : M}
variable (P : ChartCircleArrangementVertexPatch r p)

noncomputable def radialMap (d : Bool × Bool) (t : ℝ) : M :=
  P.sectorCoordinates (d.2, d.2) (if d.1 then (t, 0) else (0, t))

def radialSide (d : Bool × Bool) (ε : ℝ) : Set M := P.radialMap d '' Icc (0 : ℝ) ε

theorem radialMap_zero (d : Bool × Bool) : P.radialMap d 0 = p := by
  rw [radialMap]
  simp only [ite_self]
  exact P.sectorCoordinates_zero (d.2, d.2)

theorem firstSide_eq_radialSide (i : Bool × Bool) (ε : ℝ) :
    P.firstSide i ε = P.radialSide (true, i.1) ε :=
  P.firstSide_eq_of_fst_eq (i := i) (j := (i.1, i.1)) rfl ε

theorem secondSide_eq_radialSide (i : Bool × Bool) (ε : ℝ) :
    P.secondSide i ε = P.radialSide (false, i.2) ε :=
  P.secondSide_eq_of_snd_eq (i := i) (j := (i.2, i.2)) rfl ε

private theorem radialPoint_mem_square (d : Bool × Bool) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) P.width) :
    (if d.1 then (t, 0) else (0, t)) ∈
      Icc (0 : ℝ) P.width ×ˢ Icc (0 : ℝ) P.width := by
  cases d.1 <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact ⟨⟨le_rfl, P.width_pos.le⟩, ht⟩
  · exact ⟨ht, le_rfl, P.width_pos.le⟩

theorem radialMap_mem_carrier (d : Bool × Bool) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) P.width) : P.radialMap d t ∈ P.carrier := by
  apply P.closedSector_subset_carrier (d.2, d.2)
  rw [← P.sectorCoordinates_image_square]
  exact mem_image_of_mem _ (P.radialPoint_mem_square d ht)

theorem radialMap_injective (d : Bool × Bool) :
    InjOn (P.radialMap d) (Icc (0 : ℝ) P.width) := by
  intro s hs t ht heq
  have h := (P.sectorCoordinates (d.2, d.2)).injOn
    (P.sectorCoordinates_square_source _ (P.radialPoint_mem_square d hs))
    (P.sectorCoordinates_square_source _ (P.radialPoint_mem_square d ht)) heq
  cases hd : d.1
  · simpa only [hd, Bool.false_eq_true, ite_false, Prod.mk.injEq, true_and] using h
  · simpa only [hd, ite_true, Prod.mk.injEq, and_true] using h

theorem radialMap_continuousOn (d : Bool × Bool) :
    ContinuousOn (P.radialMap d) (Icc (0 : ℝ) P.width) := by
  apply (P.sectorCoordinates (d.2, d.2)).continuousOn.comp
  · cases d.1 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
  · intro t ht
    exact P.sectorCoordinates_square_source _ (P.radialPoint_mem_square d ht)

theorem radialMap_eq_center_iff (d : Bool × Bool) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) P.width) : P.radialMap d t = p ↔ t = 0 := by
  constructor
  · intro h
    exact P.radialMap_injective d ht ⟨le_rfl, P.width_pos.le⟩
      (h.trans (P.radialMap_zero d).symm)
  · rintro rfl
    exact P.radialMap_zero d

theorem radialSide_subset_carrier (d : Bool × Bool) {ε : ℝ} (hε : ε ≤ P.width) :
    P.radialSide d ε ⊆ P.carrier := by
  rintro _ ⟨t, ht, rfl⟩
  exact P.radialMap_mem_carrier d ⟨ht.1, ht.2.trans hε⟩

theorem radialSide_sdiff_center (d : Bool × Bool) {ε : ℝ} (hε : ε ≤ P.width) :
    P.radialSide d ε \ {p} = P.radialMap d '' Ioc (0 : ℝ) ε := by
  ext q
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hne⟩
    refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, ht.2⟩, rfl⟩
    intro heq
    exact hne (by rw [← heq, P.radialMap_zero]; exact mem_singleton _)
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩, ?_⟩
    intro heq
    exact ht.1.ne' ((P.radialMap_eq_center_iff d ⟨ht.1.le, ht.2.trans hε⟩).mp heq)

theorem isPreconnected_radialSide_sdiff_center (d : Bool × Bool) {ε : ℝ}
    (hε : ε ≤ P.width) : IsPreconnected (P.radialSide d ε \ {p}) := by
  rw [P.radialSide_sdiff_center d hε]
  exact (convex_Ioc (0 : ℝ) ε).isPreconnected.image _
    ((P.radialMap_continuousOn d).mono (fun _ ht => ⟨ht.1.le, ht.2.trans hε⟩))

theorem center_mem_closure_radialSide_sdiff (d : Bool × Bool) {ε : ℝ}
    (hε : 0 < ε) (hwidth : ε ≤ P.width) : p ∈ closure (P.radialSide d ε \ {p}) := by
  rw [P.radialSide_sdiff_center d hwidth]
  have hc : P.radialMap d 0 ∈ closure (P.radialMap d '' Ioc (0 : ℝ) ε) := by
    apply ((P.radialMap_continuousOn d) 0 ⟨le_rfl, P.width_pos.le⟩).mono
      (show Ioc (0 : ℝ) ε ⊆ Icc (0 : ℝ) P.width from
        fun _ ht => ⟨ht.1.le, ht.2.trans hwidth⟩) |>.mem_closure_image
    rw [closure_Ioc hε.ne]
    exact left_mem_Icc.mpr hε.le
  simpa only [P.radialMap_zero] using hc

theorem radialSide_inter_subset_center {d e : Bool × Bool} (hde : d ≠ e)
    {ε : ℝ} (hwidth : ε ≤ P.width) :
    P.radialSide d ε ∩ P.radialSide e ε ⊆ {p} := by
  rintro _ ⟨⟨s, hs, rfl⟩, t, ht, heq⟩
  by_cases hs0 : s = 0
  · simpa only [hs0, P.radialMap_zero] using mem_singleton p
  by_cases ht0 : t = 0
  · simpa only [ht0, P.radialMap_zero, mem_singleton_iff] using heq.symm
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hds := (P.sectorCoordinates_square_source (d.2, d.2)
    (P.radialPoint_mem_square d ⟨hs.1, hs.2.trans hwidth⟩)).2
  have hes := (P.sectorCoordinates_square_source (e.2, e.2)
    (P.radialPoint_mem_square e ⟨ht.1, ht.2.trans hwidth⟩)).2
  have hcoords := P.productCoordinates.injOn hes hds heq
  change sectorParameterEquiv P.center (e.2, e.2) (if e.1 then (t, 0) else (0, t)) =
    sectorParameterEquiv P.center (d.2, d.2) (if d.1 then (s, 0) else (0, s)) at hcoords
  have hfst := congrArg Prod.fst hcoords
  have hsnd := congrArg Prod.snd hcoords
  exfalso
  rcases d with ⟨d₁, d₂⟩
  rcases e with ⟨e₁, e₂⟩
  cases d₁ <;> cases d₂ <;> cases e₁ <;> cases e₂ <;>
    simp at hde <;>
    simp [sectorParameterEquiv_apply] at hfst hsnd <;> linarith

theorem radialSide_subset_circles_of_mem (d : Bool × Bool) {ε : ℝ}
    (hwidth : ε ≤ P.width) {q : M} (hq : q ∈ P.radialSide d ε)
    (hne : q ≠ p) (hcircles : q ∈ P.circles) : P.radialSide d ε ⊆ P.circles := by
  obtain ⟨s, hs, rfl⟩ := hq
  have hs0 : s ≠ 0 := fun h => hne (h ▸ P.radialMap_zero d)
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) ε) :=
    P.coordinates_mem_circles_iff
      ((P.sectorCoordinates_square_source (d.2, d.2)
        (P.radialPoint_mem_square d ⟨ht.1, ht.2.trans hwidth⟩)).2.2)
  have hsaxes := (hmem s hs).mp hcircles
  have hproj₀ (z : ℝ × ℝ) : (collarParameterEquiv.symm z) 0 = z.1 := rfl
  have hproj₁ (z : ℝ × ℝ) : (collarParameterEquiv.symm z) 1 = z.2 := rfl
  rintro _ ⟨t, ht, rfl⟩
  apply (hmem t ht).mpr
  cases P with
  | single x Q =>
    cases hd : d.1 <;> cases he : d.2 <;>
      simp [axes, sectorParameterEquiv_apply, center, hd, he, hproj₀] at hsaxes ⊢ <;>
      contradiction
  | crossing x y hxy Q =>
    cases hd : d.1 <;> cases he : d.2 <;>
      simp [axes, sectorParameterEquiv_apply, center, hproj₀, hproj₁]

end PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch
