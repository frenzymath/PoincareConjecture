import PoincareConjecture.Proofs.M35.Thm12_28.BallGeometry
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderRigidity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.OrdinaryRealization

theorem noncollapsed (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (F : MaximalStandardCapFlow g₀) (N : StandardFlowNoncollapsingCertificate F)
    {a : ℝ} (ha : a ∈ Ico 0 F.base.lifetime) (p : (slice (Ico 0 F.base.lifetime) a).carrier) :
    GeneralizedKappaNoncollapsedAt (generalizedFlow F.base.flow) ⟨a, p⟩ N.kappa N.radius := by
  intro r hr hradius hwindow e hzero hcurv
  have hstart : r ^ 2 ≤ a := by
    by_contra h
    have hmid : (a - r ^ 2) / 2 ∈ Ioc (a - r ^ 2) a :=
      ⟨by linarith, by linarith [ha.1]⟩
    have hnonneg := (hwindow hmid).1
    linarith
  have h₀ : 0 ∈ Ioc (-(r ^ 2)) 0 := ⟨neg_neg_of_pos (sq_pos_of_pos hr), le_rfl⟩
  refine (N.bound a ha p.val r hr hradius hstart ?_).trans_eq
    (volume_ball P F.base.flow ha p.val r).symm
  intro s hs q hq
  have hnorm : s - a ∈ Ioc (-(r ^ 2)) 0 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  let q' : (slice (Ico 0 F.base.lifetime) a).carrier := ⟨q, ha⟩
  have hq' : q' ∈ (metric F.base.flow a).ball p r :=
    (ball_image P F.base.flow ha p.val r).subset ⟨q, hq, rfl⟩
  have hc := cylinder_curvature_eq P F.base.flow e isPreconnected_Ioc h₀ (hzero h₀) hnorm hq'
  have htime : a + (s - a) / 1 = s := by ring
  have heq : (generalizedFlow F.base.flow).curvatureNorm (e.pointMap (s - a) hnorm q') =
      (F.connection s).curvatureTensorNorm q :=
    hc.trans (congrArg (fun u => (F.base.flow.connection u).curvatureTensorNorm q) htime)
  have hb := hcurv (s - a) hnorm q' hq'
  exact (congrArg abs heq).symm.le.trans hb

end PoincareConjecture.M35.OrdinaryRealization
