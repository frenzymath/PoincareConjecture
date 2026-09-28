import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarAnnulusClampedLift
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarPolarDescent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff ENNReal NNReal Bundle

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

def scalarAnnulusCoverLift {M : Type*} (f : LoopPlane → M) (z : Cover) : M :=
  f (scalarAnnulusClamp (z.2, z.1 - 1))

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem scalarAnnulus_exists_physical_descent
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1) :
    ∃ F : Plane → M, ContinuousOn F {p | p ≠ 0} ∧
      (∀ z : Cover, 0 < z.1 → F (scalarCoverMap z) = scalarAnnulusCoverLift A.map z) ∧
      ∀ p : Plane, p ≠ 0 → ∃ L : ℝ≥0, ∃ V ∈ 𝓝 p, ∀ x ∈ V, ∀ y ∈ V,
        g.edist (F x) (F y) ≤ (L : ℝ≥0∞) * edist x y := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : R1Space M := T2Space.r1Space
  let : RegularSpace M := RegularSpace.of_hasBasis
    isCompact_isClosed_basis_nhds (fun _ _ ⟨_, _, h⟩ => h)
  let : T3Space M := ⟨⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hclamp : LocallyLipschitz (A.map ∘ scalarAnnulusClamp) :=
    (scalarAnnulus_clamped_lift A).2
  let T : Cover → Cover := fun z => (z.2, z.1 - 1)
  have hT : LipschitzWith 1 T :=
    LipschitzWith.of_dist_le_mul (fun _ _ => by simp [T, Prod.dist_eq, max_comm])
  have hlocal : LocallyLipschitz (scalarAnnulusCoverLift A.map) :=
    hclamp.comp hT.locallyLipschitz
  obtain ⟨F, hdesc⟩ := scalar_exists_periodic_cover_descent (scalarAnnulusCoverLift A.map) (by
    intro r t
    change A.map (annulusPoint (curvePeriod * (t + 1)) _) =
      A.map (annulusPoint (curvePeriod * t) _)
    rw [mul_add, mul_one, A.periodic])
  exact ⟨F, scalarCoverDescent_continuousOn hlocal.continuous hdesc, hdesc,
    scalarCoverDescent_locallyLipschitzOn hlocal hdesc⟩

omit [T2Space M] [IsManifold (𝓡 n) ∞ M] in

theorem scalarAnnulusCoverLift_contMDiffAt_of_flat_collars
    {f : LoopPlane → M} {c0 c1 : ℝ → M}
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c1)
    (hlower : ∀ p : LoopPlane, p 1 ≤ (1 / 4 : ℝ) → f p = c0 (p 0))
    (hupper : ∀ p : LoopPlane, (1 / 2 : ℝ) < p 1 → f p = c1 (p 0))
    {z : Cover} (hz : z.1 < (5 / 4 : ℝ) ∨ (3 / 2 : ℝ) < z.1) :
    ContMDiffAt 𝓘(ℝ, Cover) (𝓡 n) 1 (scalarAnnulusCoverLift f) z := by
  have hangle : ContMDiff 𝓘(ℝ, Cover) 𝓘(ℝ, ℝ) 1
      (fun w : Cover => curvePeriod * w.2) :=
    contMDiff_iff_contDiff.mpr (contDiff_const.mul contDiff_snd)
  rcases hz with hz | hz
  · apply (hc0.comp hangle).contMDiffAt.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hz] with w hw
    apply hlower
    change (projIcc 0 1 (by norm_num) (w.1 - 1) : ℝ) ≤ 1 / 4
    rw [coe_projIcc]
    exact max_le (by norm_num) ((min_le_right _ _).trans (by linarith))
  · apply (hc1.comp hangle).contMDiffAt.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hz] with w hw
    apply hupper
    change (1 / 2 : ℝ) < (projIcc 0 1 (by norm_num) (w.1 - 1) : ℝ)
    rw [coe_projIcc]
    exact (lt_min (by norm_num) (by linarith)).trans_le (le_max_right _ _)

omit [T2Space M] [IsManifold (𝓡 n) ∞ M] in

theorem scalarAnnulusDescent_contMDiffAt_of_flat_collars
    {f : LoopPlane → M} {F : Plane → M} {c0 c1 : ℝ → M}
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c1)
    (hlower : ∀ p : LoopPlane, p 1 ≤ (1 / 4 : ℝ) → f p = c0 (p 0))
    (hupper : ∀ p : LoopPlane, (1 / 2 : ℝ) < p 1 → f p = c1 (p 0))
    (hdesc : ∀ z : Cover, 0 < z.1 → F (scalarCoverMap z) = scalarAnnulusCoverLift f z)
    {p : Plane} (hp : p ≠ 0) (hr : ‖p‖ < (5 / 4 : ℝ) ∨ (3 / 2 : ℝ) < ‖p‖) :
    ContMDiffAt (𝓡 2) (𝓡 n) 1 F p := by
  obtain ⟨z, hz, rfl⟩ := scalarCoverMap_surjective_of_ne_zero hp
  have hr' : z.1 < (5 / 4 : ℝ) ∨ (3 / 2 : ℝ) < z.1 := by
    simpa only [scalarCoverMap, scalarCirclePoint_norm, abs_of_pos hz] using hr
  exact scalarCoverDescent_contMDiffAt hdesc hz
    (scalarAnnulusCoverLift_contMDiffAt_of_flat_collars hc0 hc1 hlower hupper hr')

end PoincareConjecture.M64Uniformization
