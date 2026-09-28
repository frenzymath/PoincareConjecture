import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.LoopCollar
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.CollarGluing
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.LipschitzDiskArea












set_option autoImplicit false

open Set MeasureTheory Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]




theorem m60LoopCollar_lipschitz (g : RiemannianMetric 3 M)
    {γ₀ γ₁ : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g γ₀)
    (hD : ∀ z : LoopCircle, D.map z = γ₀ z)
    (C : ℝ × (M × M) → M) (h0 : ∀ p q, C (0, p, q) = q)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C (t, γ₁ z, γ₀ z)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ loopDiskSet ∩ {z | (1 / 2 : ℝ) ≤ ‖z‖},
      ∀ y ∈ loopDiskSet ∩ {z | (1 / 2 : ℝ) ≤ ‖z‖},
        g.edist (m60LoopCollar C γ₀ γ₁ x) (m60LoopCollar C γ₀ γ₁ y) ≤
          ENNReal.ofReal L * ENNReal.ofReal ‖x - y‖ := by
  apply m60_exists_collar_lipschitz_of_matching_disk g D (m60LoopCollar C γ₀ γ₁)
    (rho := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  · intro z hz
    exact m60LoopCollar_matches_disk g D hD C h0 (by norm_num) (by norm_num) hz
  · intro z hz
    exact m60LoopCollar_contMDiffAt C γ₀ γ₁ hC
      (norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hz))




theorem m60Disk_attach_loopCollar (g : RiemannianMetric 3 M)
    {γ₀ γ₁ : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g γ₀)
    (hD : ∀ z : LoopCircle, D.map z = γ₀ z)
    (C : ℝ × (M × M) → M) (h0 : ∀ p q, C (0, p, q) = q)
    (h1 : ∀ z : LoopCircle, C (1, γ₁ z, γ₀ z) = γ₁ z)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C (t, γ₁ z, γ₀ z)) :
    ∃ D' : LipschitzSpanningDisk g γ₁,
      (∀ z : LoopCircle, D'.map z = γ₁ z) ∧
      D'.area = D.area + ∫ z in (closedBall (0 : LoopPlane) (1 / 2 : ℝ))ᶜ ∩ loopDiskSet,
        m60AreaDensity g (m60LoopCollar C γ₀ γ₁) z := by
  classical
  let σ : CircleReparameterization := {
    map := id
    inverse := id
    left_inverse := fun _ => rfl
    right_inverse := fun _ => rfl
    continuous_map := continuous_id
    continuous_inverse := continuous_id }
  obtain ⟨L, hL, hLip⟩ := m60LoopCollar_lipschitz g D hD C h0 hC
  have hint := (m60AreaIntegral_bound_on_annulus g (1 / 2 : ℝ) hL hLip).1
  obtain ⟨D', hmap, harea⟩ := m60DiskGluing_of_collar g D
    (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (m60LoopCollar C γ₀ γ₁) σ
    (fun z hz => m60LoopCollar_matches_disk g D hD C h0 (by norm_num) le_rfl hz)
    (m60LoopCollar_boundary C γ₀ γ₁ h1) hL hLip hint
  refine ⟨D', ?_, harea⟩
  intro z
  have hz : (z : LoopPlane) ∉ closedBall (0 : LoopPlane) (1 / 2 : ℝ) := by
    simp only [mem_closedBall, dist_zero_right, z.property]
    norm_num
  rw [hmap, piecewise_eq_of_notMem _ _ _ hz]
  exact m60LoopCollar_boundary C γ₀ γ₁ h1 z

end PoincareConjecture
