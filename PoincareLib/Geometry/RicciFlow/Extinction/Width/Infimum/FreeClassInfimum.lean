import PoincareLib.Geometry.RicciFlow.Extinction.Width.Infimum.FamilyMaximum

/-!
# The infimum over free representatives

Morgan--Tian Definition 18.17, printed p. 430, uses all continuous null
sphere families freely homotopic to the anchor. This nonempty range is
bounded below by zero and has epsilon near-minimizers. Homotopic anchors
have identical ranges; no minimizing family or based restriction is added.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- Definition 18.17, p. 430: a free homotopy preserves the full competitor range. -/
theorem m61FreeClassWidthRange_eq_of_homotopic (g : RiemannianMetric 3 M)
    {F G : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
    (hFG : F.Homotopic G) :
    m61FreeClassWidthRange g F = m61FreeClassWidthRange g G := by
  ext w
  constructor
  · rintro ⟨H, hnull, hFH, hwidth⟩
    exact ⟨H, hnull, hFG.symm.trans hFH, hwidth⟩
  · rintro ⟨H, hnull, hGH, hwidth⟩
    exact ⟨H, hnull, hFG.trans hGH, hwidth⟩

/-- M60's filling service gives the free-class infimum properties of
Definition 18.17, p. 430, with epsilon approximants and unchanged raw competitors. -/
theorem m61FreeClassWidth_from_M60 (g : RiemannianMetric 3 M)
    (P60 : M60FillingAreaProperties g)
    (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)))
    (hnull : M61NullFamily F) : M61FreeClassWidthProperties g F := by
  have hnonempty : (m61FreeClassWidthRange g F).Nonempty :=
    ⟨m61FamilyWidth g F, F, hnull, ContinuousMap.Homotopic.refl F, rfl⟩
  have hzero : ∀ w ∈ m61FreeClassWidthRange g F, 0 ≤ w := by
    rintro _ ⟨G, hGnull, _, rfl⟩
    exact (m61FamilyWidth_from_M60 g P60 G hGnull).nonnegative
  have hbounded : BddBelow (m61FreeClassWidthRange g F) := ⟨0, hzero⟩
  refine
    { nonempty := hnonempty
      bounded_below := hbounded
      nonnegative := le_csInf hnonempty hzero
      le_member := ?_
      near_minimizer := ?_
      homotopy_invariant := ?_ }
  · intro G hGnull hFG
    exact csInf_le hbounded ⟨G, hGnull, hFG, rfl⟩
  · intro epsilon hepsilon
    obtain ⟨w, ⟨G, hGnull, hFG, rfl⟩, hw⟩ :=
      exists_lt_of_csInf_lt hnonempty (lt_add_of_pos_right
        (m61FreeClassWidth g F) hepsilon)
    exact ⟨G, hGnull, hFG, hw⟩
  · intro G _ hFG
    exact congrArg sInf (m61FreeClassWidthRange_eq_of_homotopic g hFG)

end PoincareMT
