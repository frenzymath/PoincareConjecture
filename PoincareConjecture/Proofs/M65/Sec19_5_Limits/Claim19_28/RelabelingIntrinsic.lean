import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.RelabelingGeometry









set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}



theorem m65IntrinsicRegularity_spatial_mdiff (c : ℝ → ℝ → M)
    (hreg : M63IntrinsicRegularityOn F c (Icc a b)) {t : ℝ} (ht : t ∈ Ioo a b)
    (i : ℕ) (x : ℝ) :
    MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n))
      (fun y => (⟨c y t, m63CurvatureJet F c i t y⟩ : TangentBundle (𝓡 n) M)) x := by
  have hjet := hreg.interior_jets i
  rw [interior_Icc] at hjet
  have hj := (hjet.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (x, t) ∈ univ ×ˢ Ioo a b from ⟨mem_univ x, ht⟩))).mdifferentiableAt (by simp)
  have hslice : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun y : ℝ => (y, t)) x :=
    (show DifferentiableAt ℝ (fun y : ℝ => (y, t)) x by fun_prop).mdifferentiableAt
  exact hj.comp x hslice



theorem m65IntrinsicJetSquared_fixed_relabeling (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (hreg : M63IntrinsicRegularityOn F c (Icc a b))
    {phi : ℝ → ℝ} (hphi : Differentiable ℝ phi)
    (hpos : ∀ x, 0 < deriv phi x) {t : ℝ} (ht : t ∈ Ioo a b) (i : ℕ) (x : ℝ) :
    m63CurvatureJetSquared F (fun y r => c (phi y) r) i t x =
      m63CurvatureJetSquared F c i t (phi x) := by
  unfold m63CurvatureJetSquared
  rw [m65CurvatureJet_fixed_relabeling c hc hphi hpos (Ioo_subset_Icc_self ht)
    (fun j y => m65IntrinsicRegularity_spatial_mdiff c hreg ht j y)]



theorem m65ShrinkingEquation_fixed_relabeling (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {phi : ℝ → ℝ}
    (hphi : Differentiable ℝ phi) (hpos : ∀ x, 0 < deriv phi x)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    curveVelocity (n := n) (fun r => c (phi x) r) t =
      m62CurvatureVector F (fun y r => c (phi y) r) t x := by
  rw [m65CurvatureVector_fixed_relabeling c hc hphi hpos (Ioo_subset_Icc_self ht)]
  exact hc.equation t ht (phi x)

end PoincareConjecture
