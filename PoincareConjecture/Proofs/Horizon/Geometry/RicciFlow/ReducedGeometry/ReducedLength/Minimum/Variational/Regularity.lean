import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.CompactTime








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.AncientKappaSolution

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]


theorem regularizedPotential_contMDiff (K : AncientKappaSolution 2 M) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M =>
        2 * z.1 ^ 2 * (K.flow.connection (0 - z.1 ^ 2)).scalarCurvature z.2) := by
  intro z
  let B : ℝ := |z.1| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have htime : -(B ^ 2 + 1) < 0 := by nlinarith [sq_nonneg B]
  let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow K.flow
    (show Icc (-(B ^ 2 + 1)) 0 ⊆ Iic 0 from fun _ ht => ht.2) ordConnected_Icc
    ⟨-(B ^ 2 + 1), ⟨le_rfl, htime.le⟩, 0, ⟨htime.le, le_rfl⟩, htime.ne⟩
  have hparam : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
      (fun w : ℝ × M => (0 - w.1 ^ 2, w.2)) :=
    (contMDiff_const.sub (contMDiff_fst.pow 2)).prodMk contMDiff_snd
  have hscalar : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun w : ℝ × M => (K.flow.connection (0 - w.1 ^ 2)).scalarCurvature w.2)
      (Ioo (-B) B ×ˢ univ) := by
    change ContMDiffOn _ _ ∞
      ((fun w : ℝ × M => (F.connection w.1).scalarCurvature w.2) ∘
        fun w : ℝ × M => (0 - w.1 ^ 2, w.2)) _
    apply (F.contMDiffOn_scalarCurvature_surface_Icc htime).comp hparam.contMDiffOn
    intro w hw
    have hsq : w.1 ^ 2 < B ^ 2 := by
      simpa only [sq_abs] using
        (sq_lt_sq₀ (abs_nonneg w.1) hB.le).mpr (abs_lt.mpr hw.1)
    exact ⟨⟨by nlinarith, by nlinarith [sq_nonneg w.1]⟩, mem_univ _⟩
  have hz : z ∈ Ioo (-B) B ×ˢ (univ : Set M) :=
    ⟨abs_lt.mp (show |z.1| < B by dsimp [B]; linarith), mem_univ _⟩
  have hs := (hscalar z hz).contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hz)
  exact (contMDiffAt_const.mul (contMDiffAt_fst.pow 2)).mul hs

end PoincareConjecture.AncientKappaSolution
