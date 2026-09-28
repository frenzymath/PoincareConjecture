import PoincareConjecture.Proofs.M35.CapGeometry.BufferedRadius
import PoincareConjecture.Proofs.M35.RawFlow.MetricSpace

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.CapCertificate

theorem exists_local_core_scalar_witness
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [ConnectedSpace M]
    {g : RiemannianMetric 3 M} (N : CapCertificate g) {y : M} (hy : y ∈ N.core) :
    ∃ V : Set M, IsOpen V ∧ y ∈ V ∧ ∃ r a b : ℝ,
      0 < r ∧ r < a ∧ a < b ∧ ∃ z ∈ N.carrier,
        1 < a ^ 2 * N.connection.scalarCurvature z ∧
        ∀ w ∈ V, z ∈ g.ball w r ∧ closure (g.ball w b) ⊆ N.carrier := by
  let : EMetricSpace M := g.toEMetricSpace
  obtain ⟨a, B, hra, haB, hbuffer, z, hz, hcross⟩ :=
    N.exists_buffered_core_scalar_witness hy
  have hr0 := N.core_radius_pos y hy
  obtain ⟨r, hr0r, hra'⟩ := exists_between hra
  obtain ⟨b, hab, hbB⟩ := exists_between haB
  have hr : 0 < r := hr0.trans hr0r
  have hb : 0 < b := (hr.trans hra').trans hab
  let d := min (r - N.core_radius y) (B - b) / 2
  have hd : 0 < d := half_pos (lt_min (sub_pos.mpr hr0r) (sub_pos.mpr hbB))
  have hdr : d + N.core_radius y < r := by
    have h := min_le_left (r - N.core_radius y) (B - b)
    dsimp only [d]
    linarith
  have hdb : d + b < B := by
    have h := min_le_right (r - N.core_radius y) (B - b)
    dsimp only [d]
    linarith
  let V := g.ball y d
  have hV : IsOpen V := by
    change IsOpen {w : M | edist y w < ENNReal.ofReal d}
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hyV : y ∈ V := by
    change edist y y < ENNReal.ofReal d
    simpa only [edist_self] using ENNReal.ofReal_pos.mpr hd
  refine ⟨V, hV, hyV, r, a, b, hr, hra', hab, z,
    N.core_ball_subset y hy (subset_closure hz), hcross, ?_⟩
  intro w hw
  have hyw : edist y w < ENNReal.ofReal d := hw
  have hyz : edist y z < ENNReal.ofReal (N.core_radius y) := hz
  constructor
  · change edist w z < ENNReal.ofReal r
    calc
      edist w z ≤ edist w y + edist y z := edist_triangle w y z
      _ < ENNReal.ofReal d + ENNReal.ofReal (N.core_radius y) := by
        exact ENNReal.add_lt_add (by simpa only [edist_comm] using hyw) hyz
      _ = ENNReal.ofReal (d + N.core_radius y) :=
        (ENNReal.ofReal_add hd.le hr0.le).symm
      _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal hdr.le
  · have hclosed : closure (g.ball w b) ⊆ {p : M | edist w p ≤ ENNReal.ofReal b} :=
      closure_minimal (fun p hp => (show edist w p < ENNReal.ofReal b from hp).le)
        (isClosed_le (continuous_const.edist continuous_id) continuous_const)
    intro p hp
    apply hbuffer
    apply subset_closure
    change edist y p < ENNReal.ofReal B
    calc
      edist y p ≤ edist y w + edist w p := edist_triangle y w p
      _ ≤ edist y w + ENNReal.ofReal b :=
        add_le_add le_rfl (show edist w p ≤ ENNReal.ofReal b from hclosed hp)
      _ < ENNReal.ofReal d + ENNReal.ofReal b :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hyw
      _ = ENNReal.ofReal (d + b) := (ENNReal.ofReal_add hd.le hb.le).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hdb.le

end PoincareConjecture.CapCertificate
