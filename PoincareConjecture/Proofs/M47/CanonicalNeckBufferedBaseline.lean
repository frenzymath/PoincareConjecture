import PoincareConjecture.Proofs.M47.CanonicalNeckOriginalFamily
import PoincareConjecture.Proofs.M47.CanonicalNeckTerminalMetric
import PoincareConjecture.Proofs.M47.CanonicalNeckNearbyPhysical
import PoincareConjecture.Proofs.M47.CanonicalNeckPhysicalClock









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M47



theorem eventually_original_buffer_physical_necks
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}} {T epsilon d b : ℝ}
    (N : SurgeryStrongNeck F T epsilon)
    (U : TopologicalSpace.Opens (F.slice T).carrier)
    (hU : (U : Set (F.slice T).carrier) = N.neck.carrier)
    (hd : d < -(N.neck.scale⁻¹ ^ 2)⁻¹) (hb : 0 < b)
    (E : SurgeryFlowCylinder F (F.slice T) T 1 (Icc d b) U)
    (hbased : ∀ hs x, x ∈ U → HEq (E.forward 0 hs x) x)
    (hagree : ∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
      (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc d b), ∀ x ∈ U,
        HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x) (N.cylinder.forward s hs x))
    (q : U) (hq : q.val = N.neck.center) :
    ∀ᶠ p : Icc (T + d) (T + b) × U in
      𝓝 (⟨T, ⟨by linarith [inv_pos.mpr N.cylinder.scale_pos], by linarith⟩⟩, q),
      ∃ S : SurgeryStrongNeck F p.1.val epsilon,
        ∃ ht : p.1.val - T ∈ Icc d b,
          HEq S.neck.center (E.forward (p.1.val - T) ht p.2.val) := by
  have hd0 : d < 0 := hd.trans (neg_neg_of_pos (inv_pos.mpr N.cylinder.scale_pos))
  have hdb : d < b := hd0.trans hb
  have hzero : (0 : ℝ) ∈ Icc d b := ⟨hd0.le, hb.le⟩
  obtain ⟨G, hread⟩ := exists_buffered_cylinder_ordinary P hdb U ⟨q.val, q.property⟩ E
  have hterminal := neck_ordinary_terminal_metric U E hzero hbased G
    (fun x v w => (hread 0 hzero x).1 v w)
  obtain ⟨N0, hepsilon, hscale, hconnection, hcenter, _hcarrier, hcoordinate⟩ :=
    exists_full_open_source_neck N.neck U hU (G.metric T) (G.connection T) hterminal
  have hcenter' : N0.center = q := Subtype.ext (hcenter.trans hq.symm)
  have htimes : ∀ s ∈ Ioc (-1 : ℝ) 0, s / (N.neck.scale⁻¹ ^ 2) ∈ Icc d b := by
    intro s hs
    have hp := strongNeckPhysicalClock_parameter N hs
    exact ⟨hd.le.trans hp.1.le, hp.2.trans hb.le⟩
  have hfamily := strongNeck_original_ordinary_family N U hU E G
    (fun s hs x v w => (hread s hs x).1 v w) htimes hagree N0 hepsilon hscale hcoordinate
  have hscalar : (G.connection T).scalarCurvature N0.center = N.neck.scale⁻¹ ^ 2 := by
    have hs := neck_scale_inverse_square N0
    rw [hconnection, hscale] at hs
    exact hs.symm
  have hfamily' : RoundCylinderFamilyClose N0.epsilon (Ioc (-1 : ℝ) 0)
      (fun s z v w => (G.connection T).scalarCurvature N0.center *
        roundCylinderPullback
          (G.metric (T + s / (G.connection T).scalarCurvature N0.center))
          N0.coordinate_map z v w) := by
    simpa only [hscale, hscalar] using hfamily
  let eU := neckOpenSourceCylinder U q E
  have hmetric : ∀ (s : ℝ) (hs : s ∈ Icc d b) (x : (neckOpenSourceCarrier U).carrier)
      (v w : TangentSpace (𝓡 3) x),
      eU.pullbackInner s hs x v w = (G.metric (T + s / 1)).inner x v w := by
    intro s hs x v w
    simpa only [eU, neckOpenSourceCylinder_pullbackInner, one_mul] using
      (hread s hs x).1 v w
  let t0 : Icc (T + d) (T + b) := ⟨T, by constructor <;> linarith only [hd0, hb]⟩
  have hbottom : T + d < t0.val - ((G.connection t0.val).scalarCurvature N0.center)⁻¹ := by
    change T + d < T - ((G.connection T).scalarCurvature N0.center)⁻¹
    rw [hscalar]
    linarith only [hd]
  have htop : t0.val < T + b := by dsimp only [t0]; linarith only [hb]
  have hnear := eventually_buffered_physical_strong_necks P.m04 hdb eU G hmetric t0 N0
    hconnection hbottom htop hfamily'
  rw [hcenter'] at hnear
  filter_upwards [hnear] with p hp
  obtain ⟨S, ht, hline⟩ := hp
  have heps : N0.epsilon = epsilon := hepsilon.trans N.epsilon_eq
  refine ⟨{
    neck := S.neck
    epsilon_eq := S.epsilon_eq.trans heps
    connection_eq := S.connection_eq
    cylinder := S.cylinder
    terminal_identity := S.terminal_identity
    metric_comparison := heps ▸ S.metric_comparison }, ht, ?_⟩
  exact hline

end PoincareConjecture.Proofs.M47
