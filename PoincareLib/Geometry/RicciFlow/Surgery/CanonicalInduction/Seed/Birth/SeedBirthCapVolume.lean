import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Seed.Birth.SeedBirthCapHeight
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Seed.Nonnegative.SeedNonnegativeVolume
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.Cylinders.CanonicalBall

/-!
# Uniform volume at a nonnegative birth-cap contact

The actual scalar buffer bounds the cap height below. Its retained seed
ball lies in a controlled multiple of that height about the joint point.
Nonnegative Ricci preserves the resulting fixed cubic volume density.
Source: Theorem 1.34 and Uniform Seed, MT pp. 19 and 392-393.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareMT.Proofs.M47

/-- The positive birth-cap density depends only on the fixed standard
model and the verified retained half-neck volume floor. -/
noncomputable def birthCapSeedDensity (g0 : StandardInitialMetric) : ℝ :=
  (M46.canonicalSphereVolumeFloor / 512) / (6 * (g0.cylindrical_end.radius + 5) + 3) ^ 3

theorem birthCapSeedDensity_pos (g0 : StandardInitialMetric) : 0 < birthCapSeedDensity g0 := by
  unfold birthCapSeedDensity
  apply div_pos (div_pos M46.canonicalSphereVolumeFloor_pos (by norm_num))
  apply pow_pos
  linarith [g0.cylindrical_end.radius_pos]

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

/-- A cap meeting the inner birth ball supplies a uniform density on
every smaller ball of the actual nonnegative component. Every seed and
distance is obtained from the actual event, without a volume premise. -/
theorem seed_birth_cap_volume [CompactSpace (slice T).carrier]
    (E : SurgeryEventData g0 K P slice metric T) (D : LeviCivitaData (metric T))
    (i : Fin E.cap_count) (q z : (slice T).carrier) {r H s : ℝ}
    (hr : 0 < r) (hH : 0 < H) (hbudget : H * r ^ 2 ≤ 1)
    (hz : z ∈ (E.caps i).carrier) (hclose : (metric T).edist q z < ENNReal.ofReal r)
    (hscalar : ∀ y ∈ (metric T).ball q (2 * r), D.scalarCurvature y ≤ H)
    (hRic : ∀ y ∈ connectedComponent q, ∀ v : TangentSpace (𝓡 3) y, 0 ≤ D.ricci y v v)
    (hs : 0 < s) (hsr : s ≤ r) :
    ENNReal.ofReal (birthCapSeedDensity g0 * s ^ 3) ≤
      calibratedMetricVolume (metric T) ((metric T).ball q s) := by
  let d := g0.cylindrical_end.radius + 5
  let B := 4 * d + 2
  let L := 6 * d + 3
  let h := (E.necks i).neck.scale
  let c := E.local_embed i ((E.local_result i).collapse (E.necks i).neck.center)
  have hd : 0 < d := by dsimp only [d]; linarith [g0.cylindrical_end.radius_pos]
  have hB : 0 < B := by dsimp only [B]; positivity
  have hL : 0 < L := by dsimp only [L]; positivity
  have hh : 0 < h := (E.necks i).neck.scale_pos
  have hheight : r / B ≤ h := seed_birth_cap_height E D i q z hr hH hbudget hz hclose hscalar
  have hrBh : r ≤ B * h := by simpa only [mul_comm] using (div_le_iff₀ hB).mp hheight
  have hrLh : r ≤ L * h := by dsimp only [B, L] at *; nlinarith
  have hdist : (metric T).edist q c ≤ ENNReal.ofReal (r + 2 * h * d) := by
    apply (M36.metric_edist_triangle (metric T) q z c).trans
    have hcontact : (metric T).edist z c ≤ ENNReal.ofReal (2 * h * d) :=
      event_cap_contact_distance E i hz
    simpa only [ENNReal.ofReal_add hr.le (by positivity : 0 ≤ 2 * h * d)] using
      add_le_add hclose.le hcontact
  have hball : (metric T).ball c h ⊆ (metric T).ball q (L * h) := by
    intro y hy
    have hsum := ENNReal.add_lt_add_left
      (a := ENNReal.ofReal (r + 2 * h * d)) ENNReal.ofReal_ne_top hy
    have hupper : r + 2 * h * d + h ≤ L * h := by dsimp only [B, L] at *; nlinarith
    calc
      (metric T).edist q y ≤ (metric T).edist q c + (metric T).edist c y :=
        M36.metric_edist_triangle (metric T) q c y
      _ ≤ ENNReal.ofReal (r + 2 * h * d) + (metric T).edist c y :=
        add_le_add hdist le_rfl
      _ < ENNReal.ofReal (r + 2 * h * d) + ENNReal.ofReal h := hsum
      _ = ENNReal.ofReal (r + 2 * h * d + h) :=
        (ENNReal.ofReal_add (by positivity) hh.le).symm
      _ ≤ ENNReal.ofReal (L * h) := ENNReal.ofReal_le_ofReal hupper
  have hvolume : ENNReal.ofReal (birthCapSeedDensity g0 * (L * h) ^ 3) ≤
      calibratedMetricVolume (metric T) ((metric T).ball q (L * h)) := by
    have hseed := (event_retained_center_ball_volume E i hh le_rfl).trans (measure_mono hball)
    have hvalue : birthCapSeedDensity g0 * (L * h) ^ 3 =
        (M46.canonicalSphereVolumeFloor / 512) * h ^ 3 := by
      change ((M46.canonicalSphereVolumeFloor / 512) / L ^ 3) * (L * h) ^ 3 = _
      field_simp [hL.ne']
    rwa [hvalue]
  exact seed_nonnegative_ball_volume (metric T) D q (mul_pos hL hh) hs (hsr.trans hrLh)
    isClosed_closure.isCompact
    (fun y hy v => hRic y (M46.metric_ball_subset_connectedComponent (metric T) q (L * h) hy) v)
    hvolume

end PoincareMT.Proofs.M47
