import PoincareConjecture.Proofs.M76.Mathlib.MarkedPolygonArcs
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityOrdinaryDiskBoundary
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIncidence

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.exists_boundary_arcs {d c : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d c) {a b : E}
    (ha : a ∈ c) (hb : b ∈ c) (hab : a ≠ b) :
    ∃ U V : Set E, IsFinitePLBallPair ℝ U {a, b} ∧
      IsFinitePLBallPair ℝ V {a, b} ∧ U ∪ V = c ∧ U ∩ V = {a, b} := by
  obtain ⟨n, P, hPi, hP, hPc⟩ := hd.exists_polygon_boundary
  simpa only [hPc] using
    P.exists_arcs_at_marks hP hPi (hPc.symm ▸ ha) (hPc.symm ▸ hb) hab

omit [FiniteDimensional ℝ E] in

theorem isFinitePLBallPair_signed_halves_of_arcs {U V c : Set E} {a b : E}
    (hU : IsFinitePLBallPair ℝ U {a, b}) (hV : IsFinitePLBallPair ℝ V {a, b})
    (hUV : U ∪ V = c) (A : E → ℝ) (hA : ContinuousOn A c)
    (hzero : c ∩ {x | A x = 0} = {a, b})
    (hneg : ∃ x ∈ c, A x < 0) (hpos : ∃ x ∈ c, 0 < A x) :
    IsFinitePLBallPair ℝ (c ∩ {x | A x ≤ 0}) {a, b} ∧
      IsFinitePLBallPair ℝ (c ∩ {x | 0 ≤ A x}) {a, b} := by
  have hmark (x : E) (hx : x ∈ ({a, b} : Set E)) : A x = 0 :=
    (hzero.symm.subset hx).2
  have hUs : U ⊆ c := subset_union_left.trans hUV.subset
  have hVs : V ⊆ c := subset_union_right.trans hUV.subset
  have hnonzero {W : Set E} (hW : W ⊆ c) :
      ∀ x ∈ W \ {a, b}, A x ≠ 0 := by
    intro x hx hax
    exact hx.2 (hzero.subset ⟨hW hx.1, hax⟩)
  have hsignU := hU.isConnected_sdiff.isPreconnected.mapsTo_Ioi_or_Iio
    (hA.mono (sdiff_subset.trans hUs)) (hnonzero hUs)
  have hsignV := hV.isConnected_sdiff.isPreconnected.mapsTo_Ioi_or_Iio
    (hA.mono (sdiff_subset.trans hVs)) (hnonzero hVs)
  have hrecognize {W Z : Set E}
      (hW : IsFinitePLBallPair ℝ W {a, b}) (hZ : IsFinitePLBallPair ℝ Z {a, b})
      (hWZ : W ∪ Z = c) (hWneg : MapsTo A (W \ {a, b}) (Iio 0))
      (hZpos : MapsTo A (Z \ {a, b}) (Ioi 0)) :
      IsFinitePLBallPair ℝ (c ∩ {x | A x ≤ 0}) {a, b} ∧
        IsFinitePLBallPair ℝ (c ∩ {x | 0 ≤ A x}) {a, b} := by
    have hWeq : W = c ∩ {x | A x ≤ 0} := by
      ext x
      constructor
      · intro hx
        refine ⟨hWZ.subset (Or.inl hx), ?_⟩
        by_cases hm : x ∈ ({a, b} : Set E)
        · exact (hmark x hm).le
        · exact (show A x < 0 from hWneg ⟨hx, hm⟩).le
      · rintro ⟨hx, hax⟩
        rcases hWZ.symm.subset hx with hxW | hxZ
        · exact hxW
        · by_cases hm : x ∈ ({a, b} : Set E)
          · exact hW.1 hm
          · exact (not_lt_of_ge (show A x ≤ 0 from hax)
              (show 0 < A x from hZpos ⟨hxZ, hm⟩)).elim
    have hZeq : Z = c ∩ {x | 0 ≤ A x} := by
      ext x
      constructor
      · intro hx
        refine ⟨hWZ.subset (Or.inr hx), ?_⟩
        by_cases hm : x ∈ ({a, b} : Set E)
        · exact (hmark x hm).ge
        · exact (show 0 < A x from hZpos ⟨hx, hm⟩).le
      · rintro ⟨hx, hax⟩
        rcases hWZ.symm.subset hx with hxW | hxZ
        · by_cases hm : x ∈ ({a, b} : Set E)
          · exact hZ.1 hm
          · exact (not_lt_of_ge (show 0 ≤ A x from hax)
              (show A x < 0 from hWneg ⟨hxW, hm⟩)).elim
        · exact hxZ
    exact ⟨hWeq ▸ hW, hZeq ▸ hZ⟩
  rcases hsignU with hUpos | hUneg
  · rcases hsignV with hVpos | hVneg
    · obtain ⟨x, hx, hax⟩ := hneg
      have hm : x ∉ ({a, b} : Set E) := fun h => hax.ne (hmark x h)
      rcases hUV.symm.subset hx with hxU | hxV
      · exact (lt_asymm hax (hUpos ⟨hxU, hm⟩)).elim
      · exact (lt_asymm hax (hVpos ⟨hxV, hm⟩)).elim
    · exact hrecognize hV hU (union_comm V U |>.trans hUV) hVneg hUpos
  · rcases hsignV with hVpos | hVneg
    · exact hrecognize hU hV hUV hUneg hVpos
    · obtain ⟨x, hx, hax⟩ := hpos
      have hm : x ∉ ({a, b} : Set E) := fun h => hax.ne' (hmark x h)
      rcases hUV.symm.subset hx with hxU | hxV
      · exact (lt_asymm hax (hUneg ⟨hxU, hm⟩)).elim
      · exact (lt_asymm hax (hVneg ⟨hxV, hm⟩)).elim

end Set

namespace Polygon

theorem isFinitePLBallPair_signed_halves {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (A : E → ℝ) (hA : ContinuousOn A (P.boundary ℝ))
    {a b : E} (hab : a ≠ b)
    (hzero : P.boundary ℝ ∩ {x | A x = 0} = {a, b})
    (hneg : ∃ x ∈ P.boundary ℝ, A x < 0)
    (hpos : ∃ x ∈ P.boundary ℝ, 0 < A x) :
    IsFinitePLBallPair ℝ (P.boundary ℝ ∩ {x | A x ≤ 0}) {a, b} ∧
      IsFinitePLBallPair ℝ (P.boundary ℝ ∩ {x | 0 ≤ A x}) {a, b} := by
  have ha : a ∈ P.boundary ℝ := (hzero.symm.subset (by simp)).1
  have hb : b ∈ P.boundary ℝ := (hzero.symm.subset (by simp)).1
  obtain ⟨U, V, hU, hV, hUV, _⟩ := P.exists_arcs_at_marks hP hinj ha hb hab
  exact Set.isFinitePLBallPair_signed_halves_of_arcs hU hV hUV A hA hzero hneg hpos

end Polygon
