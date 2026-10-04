import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Basic.DoubleCollar
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.OpenSubsetTransition
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Basic.TwoPieceOverlap

/-!
# The compact Hausdorff double of a cylindrical cap

Morgan-Tian Theorem 12.5, p. 297. The two pieces are actual open
truncations. Their overlap is cylinder reflection; its closed relative
graph makes the quotient Hausdorff. The two retained closed cores give
compact representatives for every quotient point.
-/

set_option autoImplicit false

open Set Topology Poincare.Gluing

namespace PoincareMT.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

/-- One open piece of the double cut at height L+1
(Theorem 12.5 compact-double construction, p. 297). -/
abbrev EndDoublePiece (e : StandardCylindricalEnd g) (L : ℝ) :=
  endTruncation e (L + 1)

/-- A zero-height cylinder point witnesses nonemptiness of each piece
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endDoublePiece_nonempty (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : Nonempty (EndDoublePiece e L) := by
  let z : StandardCylinderSpace := ((e.inverse 0).1, 0)
  exact ⟨⟨e.coordinate z,
    (endTruncation_coordinate_iff e (L := L + 1) (by linarith)
      (z := z) (by simp [z])).mpr (by dsimp [z]; linarith)⟩⟩

/-- The actual reflected transition between two open truncations
(Theorem 12.5 compact-double construction, p. 297). -/
noncomputable def endDoubleTransition (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    OpenPartialHomeomorph (EndDoublePiece e L) (EndDoublePiece e L) := by
  let := endDoublePiece_nonempty e hL
  exact (endDoubleCollarHomeomorph e hL).onOpenSubset
    (endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))

/-- Restriction leaves precisely the prescribed collar as transition source
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endDoubleTransition_source (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    (endDoubleTransition e hL).source =
      (Subtype.val : EndDoublePiece e L → StandardCapSpace) ⁻¹' endDoubleCollar e L := by
  let := endDoublePiece_nonempty e hL
  exact OpenPartialHomeomorph.onOpenSubset_source (endDoubleCollarHomeomorph e hL)
    (endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
    (endDoubleCollar_subset_truncation e hL)

/-- The restricted transition has the ambient reflection value on its source
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endDoubleTransition_apply_coe (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) {x : EndDoublePiece e L}
    (hx : (x : StandardCapSpace) ∈ endDoubleCollar e L) :
    ((endDoubleTransition e hL x : EndDoublePiece e L) : StandardCapSpace) =
      endAxialReflection e (2 * L) x := by
  let := endDoublePiece_nonempty e hL
  exact OpenPartialHomeomorph.onOpenSubset_apply_coe (endDoubleCollarHomeomorph e hL)
    (endTruncation_isOpen e (show 0 ≤ L + 1 by linarith)) x
    (endDoubleCollar_subset_truncation e hL (endAxialReflection_maps_collar e hL hx))

/-- Both off-diagonal transitions are literally the same partial homeomorphism
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endDoubleTransition_symm (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    (endDoubleTransition e hL).symm = endDoubleTransition e hL := by
  let := endDoublePiece_nonempty e hL
  exact OpenPartialHomeomorph.onOpenSubset_symm_eq (endDoubleCollarHomeomorph e hL)
    (endTruncation_isOpen e (show 0 ≤ L + 1 by linarith)) (endDoubleCollarHomeomorph_symm e hL)

/-- The transition graph is closed relative to the product of open pieces
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endDoubleTransition_closed (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    IsClosed {p : EndDoublePiece e L × EndDoublePiece e L |
      p.1 ∈ (endDoubleTransition e hL).source ∧ endDoubleTransition e hL p.1 = p.2} := by
  have heq : {p : EndDoublePiece e L × EndDoublePiece e L |
      p.1 ∈ (endDoubleTransition e hL).source ∧ endDoubleTransition e hL p.1 = p.2} =
      (fun p : EndDoublePiece e L × EndDoublePiece e L =>
        ((p.1 : StandardCapSpace), (p.2 : StandardCapSpace))) ⁻¹'
          endClosedReflectionGraph e L := by
    ext p
    rw [mem_preimage, endClosedReflectionGraph_iff e hL p.1.property p.2.property]
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [endDoubleTransition_source]
    constructor
    · rintro ⟨hx, hxy⟩
      exact ⟨hx, (endDoubleTransition_apply_coe e hL hx).symm.trans
        (congrArg Subtype.val hxy)⟩
    · rintro ⟨hx, hxy⟩
      exact ⟨hx, Subtype.ext ((endDoubleTransition_apply_coe e hL hx).trans hxy)⟩
  rw [heq]
  exact (endClosedReflectionGraph_isCompact e hL).isClosed.preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

/-- The two-copy overlap system of the supplied cap
(Theorem 12.5 compact-double construction, p. 297). -/
noncomputable def endDoubleOverlap (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : OverlapSystem (fun _ : Bool => EndDoublePiece e L) :=
  twoPieceOverlap (endDoubleTransition e hL) (endDoubleTransition_symm e hL)

/-- The underlying quotient carrier of the reflected cap double
(Theorem 12.5 compact-double construction, p. 297). -/
abbrev EndDouble (e : StandardCylindricalEnd g) {L : ℝ} (hL : 1 < L) :=
  Quotient (endDoubleOverlap e hL).setoid

/-- The cap double has its actual Hausdorff quotient topology
(Theorem 12.5 compact-double construction, p. 297). -/
instance endDouble_t2Space (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : T2Space (EndDouble e hL) :=
  (endDoubleOverlap e hL).quotient_t2Space
    (twoPieceOverlap_closed _ _ (endDoubleTransition_closed e hL))

/-- The quotient is second countable because its two pieces are
(Theorem 12.5 compact-double construction, p. 297). -/
instance endDouble_secondCountableTopology (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : SecondCountableTopology (EndDouble e hL) :=
  (endDoubleOverlap e hL).quotient_secondCountableTopology

/-- The retained closed core is a compact subset of the open piece
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endDoublePiece_compactCore (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    IsCompact ((Subtype.val : EndDoublePiece e L → StandardCapSpace) ⁻¹'
      endTruncatedCore e L) := by
  apply Subtype.isCompact_iff.mpr
  rw [image_preimage_eq_of_subset]
  · exact endTruncatedCore_isCompact e (by linarith)
  · simpa only [Subtype.range_coe] using
      endTruncatedCore_subset_truncation e (show L < L + 1 by linarith)

/-- Every representative outside the closed core reflects into the other core
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endDoublePiece_core_cover (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) (x : EndDoublePiece e L) :
    (x : StandardCapSpace) ∈ endTruncatedCore e L ∨
      x ∈ (endDoubleTransition e hL).source ∧
      ((endDoubleTransition e hL x : EndDoublePiece e L) : StandardCapSpace) ∈
        endTruncatedCore e L := by
  by_cases hx : (x : StandardCapSpace) ∈ endTruncatedCore e L
  · exact Or.inl hx
  have ht : (x : StandardCapSpace) ∈ e.coordinate '' (univ ×ˢ Ioi L) := not_not.mp hx
  obtain ⟨z, hz, hxz⟩ := ht
  have hlower : L < z.2 := hz.2
  have hzpos : 0 ≤ z.2 := by linarith
  have hupper : z.2 < L + 1 :=
    (endTruncation_coordinate_iff e (L := L + 1) (by linarith) hzpos).mp
      (by rw [hxz]; exact x.property)
  have hcollar : (x : StandardCapSpace) ∈ endDoubleCollar e L :=
    ⟨z, ⟨mem_univ _, by linarith, hupper⟩, hxz⟩
  refine Or.inr ⟨?_, ?_⟩
  · rw [endDoubleTransition_source]
    exact hcollar
  · rw [endDoubleTransition_apply_coe e hL hcollar, ← hxz,
      endAxialReflection_coordinate e (2 * L) hzpos]
    exact (endTruncatedCore_coordinate_iff e (L := L) (by linarith)
      (z := (z.1, 2 * L - z.2)) (by dsimp only; linarith)).mpr
        (by dsimp only; linarith)

/-- Two compact retained cores cover the quotient, making the double compact
(Theorem 12.5 compact-double construction, p. 297). -/
instance endDouble_compactSpace (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : CompactSpace (EndDouble e hL) :=
  twoPieceOverlap_compactSpace _ _ (endDoublePiece_compactCore e hL)
    (endDoublePiece_core_cover e hL)

end PoincareMT.M34
