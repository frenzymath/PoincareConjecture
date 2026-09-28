import PoincareConjecture.Proofs.M47.CanonicalNeckOrdinaryFamily
import PoincareConjecture.Proofs.M47.CanonicalNeckOrdinaryBridge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

theorem eventually_buffered_physical_strong_necks
    (hC : RicciFlowCurvatureTheory.{u}) {F : SurgeryFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} {origin a b : ℝ} (hab : a < b)
    (e : SurgeryFlowCylinder F C origin 1 (Icc a b) univ)
    (G : RicciFlow 3 C.carrier (Icc (origin + a) (origin + b)))
    (hmetric : ∀ (s : ℝ) (hs : s ∈ Icc a b) (x : C.carrier)
      (v w : TangentSpace (𝓡 3) x),
      e.pullbackInner s hs x v w = (G.metric (origin + s / 1)).inner x v w)
    (t0 : Icc (origin + a) (origin + b)) (N : EpsilonNeck (G.metric t0.val))
    (hconnection : N.connection = G.connection t0.val)
    (hbottom : origin + a < t0.val - ((G.connection t0.val).scalarCurvature N.center)⁻¹)
    (htop : t0.val < origin + b)
    (hfamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun u z v w => (G.connection t0.val).scalarCurvature N.center *
        roundCylinderPullback
          (G.metric (t0.val + u / (G.connection t0.val).scalarCurvature N.center))
          N.coordinate_map z v w)) :
    ∀ᶠ p : Icc (origin + a) (origin + b) × C.carrier in 𝓝 (t0, N.center),
      ∃ S : SurgeryStrongNeck F p.1.val N.epsilon,
        ∃ ht : p.1.val - origin ∈ Icc a b,
          HEq S.neck.center (e.forward (p.1.val - origin) ht p.2) := by
  have hab' : origin + a < origin + b := by linarith only [hab]
  obtain ⟨_lambda, _hlambda, hnear⟩ := exists_eventually_buffered_ordinary_necks
    hC hab' G t0 N hconnection hbottom htop hfamily
  filter_upwards [hnear] with p hp
  obtain ⟨N', hepsilon, hcenter, hconnection', _hcarrier, _hsubset,
    _hcoordinate, hnormalized⟩ := hp.2.2
  have hscale : N'.scale⁻¹ ^ 2 = (G.connection p.1.val).scalarCurvature p.2 := by
    rw [neck_scale_inverse_square, hconnection', hcenter]
  have htimes : ∀ u ∈ Ioc (-1 : ℝ) 0,
      p.1.val + u / (N'.scale⁻¹ ^ 2) ∈ Icc (origin + a) (origin + b) := by
    intro u hu
    rw [hscale]
    exact hp.2.1 u (Ioc_subset_Icc_self hu)
  have hfamily' : RoundCylinderFamilyClose N'.epsilon (Ioc (-1 : ℝ) 0)
      (fun u z v w => N'.scale⁻¹ ^ 2 *
        roundCylinderPullback (G.metric (p.1.val + u / (N'.scale⁻¹ ^ 2)))
          N'.coordinate_map z v w) := by
    rw [hepsilon, hscale]
    exact hnormalized
  obtain ⟨S, ht, hline⟩ := exists_strong_neck_of_ordinary_family e G hmetric
    N' hconnection' htimes hfamily'
  refine ⟨{
    neck := S.neck
    epsilon_eq := S.epsilon_eq.trans hepsilon
    connection_eq := S.connection_eq
    cylinder := S.cylinder
    terminal_identity := S.terminal_identity
    metric_comparison := hepsilon ▸ S.metric_comparison }, ht, ?_⟩
  exact hline.trans (heq_of_eq (congrArg (e.forward (p.1.val - origin) ht) hcenter))

end PoincareConjecture.Proofs.M47
