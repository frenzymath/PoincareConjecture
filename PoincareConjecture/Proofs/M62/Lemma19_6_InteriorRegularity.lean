import PoincareConjecture.Proofs.M62.Lemma0_1_Speed
import PoincareConjecture.Proofs.M08.VariationDerivativeData
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)

theorem spatial_velocity_joint_contMDiff (hc : M62ShrinkingCurve F c) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × ℝ ↦ (⟨c z.1 z.2, curveVelocity (fun y ↦ c y z.2) z.1⟩ :
        TangentBundle (𝓡 n) M)) (Set.univ ×ˢ Set.Ioo a b) := by
  have hcurve := hc.joint_smooth
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hcurve
  have h := M08.contMDiffOn_curveVelocity_fst (isOpen_univ.prod isOpen_Ioo) _ hcurve
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact h

theorem time_velocity_joint_contMDiff (hc : M62ShrinkingCurve F c) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × ℝ ↦ (⟨c z.1 z.2, curveVelocity (fun s ↦ c z.1 s) z.2⟩ :
        TangentBundle (𝓡 n) M)) (Set.univ ×ˢ Set.Ioo a b) := by
  have hcurve := hc.joint_smooth
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hcurve
  have h := M08.contMDiffOn_curveVelocity_snd (isOpen_univ.prod isOpen_Ioo) _ hcurve
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact h

theorem curvature_joint_contMDiff (hc : M62ShrinkingCurve F c) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × ℝ ↦ (⟨c z.1 z.2, m62CurvatureVector F c z.2 z.1⟩ :
        TangentBundle (𝓡 n) M)) (Set.univ ×ˢ Set.Ioo a b) := by
  apply (time_velocity_joint_contMDiff F c hc).congr
  intro z hz
  exact congrArg (Bundle.TotalSpace.mk (c z.1 z.2)) (hc.equation z.2 hz.2 z.1).symm

theorem metric_pairing_contDiffOn
    (hc : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞
      (fun z : ℝ × ℝ ↦ c z.1 z.2) (Set.univ ×ˢ Set.Ioo a b))
    (Y Z : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2))
    (hY : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × ℝ ↦ (⟨c z.1 z.2, Y z⟩ : TangentBundle (𝓡 n) M))
      (Set.univ ×ˢ Set.Ioo a b))
    (hZ : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × ℝ ↦ (⟨c z.1 z.2, Z z⟩ : TangentBundle (𝓡 n) M))
      (Set.univ ×ˢ Set.Ioo a b)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ ↦ (F.metric z.2).inner (c z.1 z.2) (Y z) (Z z))
      (Set.univ ×ˢ Set.Ioo a b) := by
  have ht : ContMDiff (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ℝ)) ∞ (Prod.snd : ℝ × ℝ → ℝ) :=
    contDiff_snd.contMDiff
  have hg := F.smooth.comp (ht.contMDiffOn.prodMk hc)
    (fun z hz ↦ ⟨Set.Ioo_subset_Icc_self hz.2, Set.mem_univ _⟩)
  suffices ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × ℝ ↦ (F.metric z.2).inner (c z.1 z.2) (Y z) (Z z))
      (Set.univ ×ˢ Set.Ioo a b) from this.contDiffOn
  intro z hz
  have hp : ContMDiffWithinAt (𝓘(ℝ, ℝ × ℝ)) ((𝓡 n).prod (𝓘(ℝ, ℝ))) ∞
      (fun w : ℝ × ℝ ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
        (c w.1 w.2) ((F.metric w.2).inner (c w.1 w.2) (Y w) (Z w)))
      (Set.univ ×ˢ Set.Ioo a b) z :=
    (hg z hz).clm_bundle_apply₂ (hY z hz) (hZ z hz)
  exact (Bundle.contMDiffWithinAt_totalSpace.mp hp).2

theorem speed_joint_contDiffOn (hc : M62ShrinkingCurve F c) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ ↦ curveSpeed F c z.2 z.1)
      (Set.univ ×ˢ Set.Ioo a b) := by
  have hX := spatial_velocity_joint_contMDiff F c hc
  exact (metric_pairing_contDiffOn F c hc.joint_smooth _ _ hX hX).sqrt
    (fun z hz ↦ ((F.metric z.2).pos _ _
      (hc.immersed z.2 (Set.Ioo_subset_Icc_self hz.2) z.1)).ne')

theorem curvatureSquared_contDiffOn (hc : M62ShrinkingCurve F c) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ ↦ m62CurvatureSquared F c z.2 z.1)
      (Set.univ ×ˢ Set.Ioo a b) := by
  have hH := curvature_joint_contMDiff F c hc
  exact metric_pairing_contDiffOn F c hc.joint_smooth _ _ hH hH

end PoincareConjecture.M62
