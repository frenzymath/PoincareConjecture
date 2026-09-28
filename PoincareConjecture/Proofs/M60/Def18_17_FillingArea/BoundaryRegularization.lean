import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.IncreasingBoundaryRegularization
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.DiskReflection

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem m60Disk_regularize_boundary
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {gamma : C1FreeLoopSpace (M := M)}
    (D : LipschitzSpanningDisk g gamma) :
    ∃ D' : LipschitzSpanningDisk g gamma,
      (∀ z : LoopCircle, D'.map z = gamma z) ∧ D'.area = D.area := by
  obtain ⟨H, hlift, _⟩ := m60_exists_circle_reparameterization_lift D.reparameterization
  rcases m60CircleLift_period D.reparameterization H hlift with hpos | hneg
  · exact m60Disk_regularize_of_increasing_lift g D H hpos.1.monotone hpos.2 hlift
  · let N : ℝ ≃ₜ ℝ := (ContinuousLinearEquiv.neg ℝ (M := ℝ)).toHomeomorph
    let H' : ℝ ≃ₜ ℝ := N.trans H
    have hmono : Monotone H' := by
      intro s t hst
      exact hneg.1.antitone (neg_le_neg hst)
    have hperiod (t : ℝ) : H' (t + rampPeriod) = H' t + rampPeriod := by
      change H (-(t + rampPeriod)) = H (-t) + rampPeriod
      have h := hneg.2 (-t - rampPeriod)
      rw [sub_add_cancel] at h
      rw [show -(t + rampPeriod) = -t - rampPeriod by ring]
      linarith
    have hnewlift (t : ℝ) :
        (⟨Proofs.M58.angularPoint (H' t), Proofs.M58.norm_angularPoint (H' t)⟩ : LoopCircle) =
          (m60Disk_reflect g D).reparameterization.map
            ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩ := by
      have hr : m60CircleReflection.map
          ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩ =
          ⟨Proofs.M58.angularPoint (-t), Proofs.M58.norm_angularPoint (-t)⟩ :=
        Subtype.ext (m60PlaneReflection_angular t)
      change (⟨Proofs.M58.angularPoint (H (-t)), Proofs.M58.norm_angularPoint (H (-t))⟩ :
        LoopCircle) = D.reparameterization.map (m60CircleReflection.map _)
      rw [hr]
      exact hlift (-t)
    obtain ⟨D', hboundary, harea⟩ :=
      m60Disk_regularize_of_increasing_lift g (m60Disk_reflect g D) H' hmono hperiod hnewlift
    exact ⟨D', hboundary, harea.trans (m60Disk_reflect_area g D)⟩

end PoincareConjecture
