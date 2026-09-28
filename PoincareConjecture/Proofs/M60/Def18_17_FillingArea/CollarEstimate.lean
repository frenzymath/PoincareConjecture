import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.CollarGluing
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.LipschitzDiskArea
import PoincareConjecture.Proofs.M60.Filling











set_option autoImplicit false

open Set MeasureTheory Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] [T2Space M]




theorem m60FillingArea_le_of_lipschitz_collar (g : RiemannianMetric 3 M)
    {γ γ' : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g γ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (H : LoopPlane → M)
    (σ : CircleReparameterization)
    (hmatch : ∀ z : LoopPlane, ‖z‖ = r → D.map (r⁻¹ • z) = H z)
    (hboundary : ∀ z : LoopCircle, H z = γ' (σ.map z))
    {L : ℝ} (hL : 0 ≤ L)
    (hLipH : ∀ x ∈ loopDiskSet ∩ {z | r ≤ ‖z‖},
      ∀ y ∈ loopDiskSet ∩ {z | r ≤ ‖z‖},
        g.edist (H x) (H y) ≤ ENNReal.ofReal L * ENNReal.ofReal ‖x - y‖) :
    fillingArea g γ' ≤ D.area + (2 * L) ^ 2 * (1 - r ^ 2) * volume.real loopDiskSet := by
  obtain ⟨hint, hbound⟩ := m60AreaIntegral_bound_on_annulus g r hL hLipH
  obtain ⟨D', _, harea⟩ :=
    m60DiskGluing_of_collar g D hr hr1 H σ hmatch hboundary hL hLipH hint
  have hvol : volume.real ((closedBall (0 : LoopPlane) r)ᶜ ∩ loopDiskSet) =
      (1 - r ^ 2) * volume.real loopDiskSet := by
    simpa only [loopDiskSet, LoopPlane, finrank_euclideanSpace, Fintype.card_fin] using
      M60.haar_unit_annulus_real volume (E := LoopPlane) hr.le hr1.le
  apply (m60FillingArea_le_disk g γ' D').trans
  rw [harea]
  rw [hvol] at hbound
  nlinarith [hbound]

end PoincareConjecture
