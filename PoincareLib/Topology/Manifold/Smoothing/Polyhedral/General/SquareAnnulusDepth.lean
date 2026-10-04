import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.SquareAnnulusFiber

/-!
# The signed transverse coordinate of the square annulus

The minimum of the four signed boundary coordinates is the
literal transverse input of the actual annulus map. Its closed
and open level bands identify the annulus and its open interior.
See Hatcher p. 7, Hamilton 1976, p. 66 and M76 derivation 270.
-/

set_option autoImplicit false

open Set

namespace PLAnnularStrip

/-- The signed distance in coordinate units from the four
square sides. Negative values lie outside the central square.
See Hatcher p. 7 and M76 derivation 270. -/
noncomputable def depth (L : ℝ) (p : ℝ × ℝ) : ℝ :=
  min (min p.1 p.2) (min (L - p.1) (L - p.2))

/-- The signed square depth is continuous on the whole plane.
See M76 derivation 270. -/
theorem continuous_depth (L : ℝ) : Continuous (depth L) := by
  unfold depth
  fun_prop

/-- The closed square annulus is exactly its closed signed
depth band, including both boundary components. See
Hatcher p. 7 and M76 derivation 270. -/
theorem mem_squareAnnulus_iff_depth {L d : ℝ} {p : ℝ × ℝ} :
    p ∈ squareAnnulus L d ↔ depth L p ∈ Icc (-d) d := by
  constructor
  · intro hp
    rcases hp with ⟨⟨hx, hy⟩, hinner⟩
    refine ⟨le_min (le_min hx.1 hy.1)
      (le_min (by linarith [hx.2]) (by linarith [hy.2])), ?_⟩
    by_contra hn
    have h : d < depth L p := lt_of_not_ge hn
    have hcoords := lt_min_iff.mp h
    have hxy := lt_min_iff.mp hcoords.1
    have hxy' := lt_min_iff.mp hcoords.2
    exact hinner ⟨⟨hxy.1, by linarith [hxy'.1]⟩,
      ⟨hxy.2, by linarith [hxy'.2]⟩⟩
  · rintro ⟨hlow, hupp⟩
    have hcoords := le_min_iff.mp hlow
    have hxy := le_min_iff.mp hcoords.1
    have hxy' := le_min_iff.mp hcoords.2
    refine ⟨⟨⟨hxy.1, by linarith [hxy'.1]⟩,
      ⟨hxy.2, by linarith [hxy'.2]⟩⟩, ?_⟩
    intro hinner
    have h : d < depth L p := lt_min
      (lt_min hinner.1.1 hinner.2.1)
      (lt_min (by linarith [hinner.1.2]) (by linarith [hinner.2.2]))
    exact (not_lt_of_ge hupp) h

/-- Each actual quarter turn preserves signed square depth.
See M76 derivation 270. -/
theorem depth_stripRotation (L : ℝ) (i : Fin 4) (p : ℝ × ℝ) :
    depth L (stripRotation L i p) = depth L p := by
  fin_cases i <;>
    simp [depth, stripRotation, sub_sub_cancel, min_comm, min_left_comm]

/-- On the bottom strip the signed square depth is exactly
the original transverse coordinate. See M76 derivation 270. -/
theorem depth_stripMap {L s t : ℝ} (ht : 4 * |t| < L) (hs : s ∈ Icc 0 L) :
    depth L (stripMap L (s, t)) = t := by
  have hu := coordinate_mem_Icc ht hs
  have htd : t ≤ L - t := by linarith [le_abs_self t, abs_nonneg t]
  change min (min (coordinate L s t) t)
    (min (L - coordinate L s t) (L - t)) = t
  rw [min_eq_right hu.1]
  exact min_eq_left (le_min (by linarith [hu.2]) htd)

/-- The actual circle map retains its transverse input as
signed square depth, for every circle point including seams.
See Hatcher p. 7 and M76 derivation 270. -/
theorem depth_annulusMap {L t : ℝ} (hL : 0 < L) (ht : 4 * |t| < L)
    (z : AddCircle (4 * L)) : depth L (annulusMap L hL (z, t)) = t := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  let r : ℝ := AddCircle.equivIco (4 * L) 0 z
  have hr : r ∈ Icc 0 (4 * L) := by
    have h := (AddCircle.equivIco (4 * L) 0 z).property
    exact ⟨h.1, by simpa only [zero_add] using h.2.le⟩
  have hrcoe : (r : AddCircle (4 * L)) = z := AddCircle.coe_equivIco
  obtain ⟨i, s, hs, he⟩ := exists_period_block hr
  rw [← hrcoe, annulusMap_coe hL ht hr, he, wrappedStripMap_block ht hs i,
    depth_stripRotation]
  exact depth_stripMap ht hs

end PLAnnularStrip
