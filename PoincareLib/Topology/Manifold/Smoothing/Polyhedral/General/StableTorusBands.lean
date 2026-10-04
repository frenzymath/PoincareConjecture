import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.PLBandCutoff
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.PLChartFamilies

/-!
# Actual nested coordinate bands and their PL widths

All bands are literal images of short intervals in the
period64 circle. The repeated coordinate maximum supplies
genuine PL cutoffs on the two- and three-torus. See
Hamilton 1976, p. 66 and M76 derivation270.
-/

set_option autoImplicit false

open Set Geometry

namespace StableTorus

/-- The actual period64 circle used at every stable step.
See M76 derivation270. -/
abbrev Circle := AddCircle (4 * (16 : ℝ))

/-- A literal open short coordinate band.
See M76 derivation270. -/
def arc (r : ℝ) : Set Circle := ((↑) : ℝ → Circle) '' Ioo (-r) r

/-- The two coordinate bands in the actual product torus.
See Hamilton p. 66 and M76 derivation270. -/
def twoBands (r : ℝ) : Set (Circle × Circle) :=
  (arc r ×ˢ univ) ∪ (univ ×ˢ arc r)

/-- The three coordinate bands, in left-associated order.
See Hamilton p. 66 and M76 derivation270. -/
def threeBands (r : ℝ) : Set ((Circle × Circle) × Circle) :=
  (twoBands r ×ˢ univ) ∪ (univ ×ˢ arc r)

/-- Shorter actual arc bands are contained in longer ones.
See M76 derivation270. -/
theorem arc_mono {r R : ℝ} (hrR : r ≤ R) : arc r ⊆ arc R := by
  rintro z ⟨s, hs, rfl⟩
  exact ⟨s, ⟨by linarith [hs.1], by linarith [hs.2]⟩, rfl⟩

/-- Every actual short band is open in the circle.
See M76 derivation270. -/
theorem isOpen_arc {r : ℝ} (hr : r < 32) : IsOpen (arc r) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  rw [show arc r = (AddCircle.shortArcQuotient (4 * (16 : ℝ)) r).target from
    (AddCircle.shortArcQuotient_target (4 * (16 : ℝ)) (by norm_num; exact hr)).symm]
  exact (AddCircle.shortArcQuotient (4 * (16 : ℝ)) r).open_target

/-- The full two-band union is open. See derivation270. -/
theorem isOpen_twoBands {r : ℝ} (hr : r < 32) : IsOpen (twoBands r) :=
  ((isOpen_arc hr).prod isOpen_univ).union (isOpen_univ.prod (isOpen_arc hr))

/-- The full three-band union is open. See derivation270. -/
theorem isOpen_threeBands {r : ℝ} (hr : r < 32) : IsOpen (threeBands r) :=
  ((isOpen_twoBands hr).prod isOpen_univ).union (isOpen_univ.prod (isOpen_arc hr))

/-- The smaller two-band union lies in the larger one.
See M76 derivation270. -/
theorem twoBands_mono {r R : ℝ} (hrR : r ≤ R) : twoBands r ⊆ twoBands R := by
  intro z hz
  rcases hz with hx | hy
  · exact Or.inl ⟨arc_mono hrR hx.1, mem_univ _⟩
  · exact Or.inr ⟨mem_univ _, arc_mono hrR hy.2⟩

/-- An actual circle cutoff has its entire closed smaller
arc at value1, hence its open smaller band as well. See
M76 derivation270, periodic cutoff construction. -/
theorem exists_arc_cutoff {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < 32) :
    letI : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
    ∃ w : Circle → ℝ, Continuous w ∧ (∀ z, w z ∈ Icc 0 1) ∧
      (∀ z, z ∉ arc R → w z = 0) ∧ (∀ z ∈ arc r, w z = 1) ∧
      ∀ a, LocallyPiecewiseAffineOn (w ∘ AddCircle.quotientCharts (4 * (16 : ℝ)) a)
        (AddCircle.quotientCharts (4 * (16 : ℝ)) a).source := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨w, hc, hw, hcore, hout, hPL⟩ :=
    AddCircle.exists_shortArc_PL_cutoff (4 * (16 : ℝ)) hr hrR (by norm_num; exact hR)
  refine ⟨w, hc, hw, hout, ?_, hPL⟩
  rintro z ⟨s, hs, rfl⟩
  exact hcore s (abs_lt.mpr hs).le

/-- Two coordinate copies of one actual periodic cutoff
give a genuine whole two-band PL width. See derivation270. -/
theorem exists_twoBand_cutoff {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < 32) :
    letI : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
    let Q := AddCircle.quotientCharts (4 * (16 : ℝ))
    ∃ w : Circle × Circle → ℝ, Continuous w ∧ (∀ z, w z ∈ Icc 0 1) ∧
      (∀ z, z ∉ twoBands R → w z = 0) ∧ (∀ z ∈ twoBands r, w z = 1) ∧
      ∀ a, LocallyPiecewiseAffineOn (w ∘ prodCharts Q Q a) (prodCharts Q Q a).source := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨v, hc, hv, hout, hcore, hPL⟩ := exists_arc_cutoff hr hrR hR
  obtain ⟨hcw, hw, hwo, hwc⟩ := PLBandCutoff.unionWidth_properties v v hc hc hv hv
    (arc R) (arc r) (arc R) (arc r) hout hout hcore hcore
  refine ⟨PLBandCutoff.unionWidth v v, hcw, hw, hwo, hwc, ?_⟩
  intro a
  exact PLBandCutoff.locallyPiecewiseAffineOn_unionWidth v v _ _ (hPL a.1) (hPL a.2)

/-- The nested maximum is an actual three-band PL width
with full support and core controls. See derivation270. -/
theorem exists_threeBand_cutoff {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < 32) :
    letI : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
    let Q := AddCircle.quotientCharts (4 * (16 : ℝ))
    let T := prodCharts (prodCharts Q Q) Q
    ∃ w : (Circle × Circle) × Circle → ℝ, Continuous w ∧ (∀ z, w z ∈ Icc 0 1) ∧
      (∀ z, z ∉ threeBands R → w z = 0) ∧ (∀ z ∈ threeBands r, w z = 1) ∧
      ∀ a, LocallyPiecewiseAffineOn (w ∘ T a) (T a).source := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨v, hcv, hv, hvo, hvc, hvPL⟩ := exists_twoBand_cutoff hr hrR hR
  obtain ⟨u, hcu, hu, huo, huc, huPL⟩ := exists_arc_cutoff hr hrR hR
  obtain ⟨hcw, hw, hwo, hwc⟩ := PLBandCutoff.unionWidth_properties v u hcv hcu hv hu
    (twoBands R) (twoBands r) (arc R) (arc r) hvo huo hvc huc
  refine ⟨PLBandCutoff.unionWidth v u, hcw, hw, hwo, hwc, ?_⟩
  intro a
  exact PLBandCutoff.locallyPiecewiseAffineOn_unionWidth v u _ _ (hvPL a.1) (huPL a.2)

end StableTorus
