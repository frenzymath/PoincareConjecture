import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Seed.Cylinder.SeedCylinderRecenter
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Seed.Search.SeedSearchBalls
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.Prefix

/-!
# Old noncollapse on an actual interior search ball

The actual inverse-ball barrier supplies the spatial domain. Recentring
the retained search supplies the guarded parabolic test cylinder.
Source: Definition 15.7 and Uniform Seed, Morgan--Tian pp. 392-393.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareMT.Proofs.M47

/-- At an old interior search time, the old prefix gives volume on the
actual surviving inner ball. Every cylinder and coverage input required
by noncollapse is constructed from the original retained search. -/
theorem seed_search_old_noncollapsed
    (P : M47Predecessors.{u}) {K0 : MetricSurgeryConstants}
    {p : SurgeryParameterPrefix K0} {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) (hpinch : SurgeryFlowPinched F)
    {origin c K : ℝ} {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc c 0) U)
    (hU : IsOpen U) (hK : 0 ≤ K)
    (hbase : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (hRm : ∀ s (hs : s ∈ Icc c 0), ∀ x ∈ U,
      (F.connection (origin + s / 1)).curvatureTensorNorm (e.forward s hs x) ≤ K)
    (hshort : 6 * K * (-c) ≤ 1 / 2)
    (q : (F.slice origin).carrier) {R r a : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hcompact : IsCompact (closure ((F.metric origin).ball q R)))
    (hsource : closure ((F.metric origin).ball q R) ⊆ U)
    (ha : a ∈ Icc c 0) (hbackward : c ≤ a - r ^ 2)
    (hrR : r ≤ R / 2) (hrepsilon : r ≤ p.setup.epsilon) (htest : K ≤ r⁻¹ ^ 2)
    (ht : origin + a / 1 ∈ surgeryObservationInterval O ∩ prefixFinalInterval p)
    (hpositive : ¬ SurgeryPositiveComponentAt F (origin + a / 1) (e.forward a ha q)) :
    ENNReal.ofReal (p.kappa (Fin.last p.i) * r ^ 3) ≤
      calibratedMetricVolume (F.metric (origin + a / 1))
        ((F.metric (origin + a / 1)).ball (e.forward a ha q) r) := by
  have hballs := seed_search_ball_inclusions P hpinch e hU hK hbase hRm hshort
    q hR hcompact hsource a ha
  let V := (F.metric (origin + a / 1)).ball (e.forward a ha q) r
  have hV : V ⊆ e.forward a ha '' U := by
    intro x hx
    apply (image_mono (subset_closure.trans hsource))
    apply hballs.1
    exact hx.trans_le (ENNReal.ofReal_le_ofReal hrR)
  have hrange : ∀ s ∈ Icc (-r ^ 2) 0, a + 1 * s ∈ Icc c 0 := by
    intro s hs
    constructor <;> nlinarith [hs.1, hs.2, ha.2]
  obtain ⟨d, hd, hcurv⟩ := exists_seedCylinder_recenter e hU a ha hrange V hV hRm
  apply M46.prefix_noncollapsed old le_rfl (origin + a / 1) ht (O.interval_subset ht.1)
    (e.forward a ha q) hpositive r hr (by rwa [old.epsilon_eq]) d hd
  intro s hs x hx
  exact (hcurv s hs x hx).trans htest

end PoincareMT.Proofs.M47
