import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.CirclePair.AttachmentGerm.CircleLinear
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.ChartLinearization
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.CircleAttachmentGerm

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩

theorem exists_circle_diffeomorph_of_local_germ
    (f : S1 → S1) (p : S1)
    (hf : IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ f p) :
    ∃ q : Diffeomorph (𝓡 1) (𝓡 1) S1 S1 ∞, (q : S1 → S1) =ᶠ[𝓝 p] f := by
  obtain ⟨P, hp, hPf⟩ := hf
  let R : E2 ≃ₗᵢ[Real] E2 := (Real ∙ ((f p : E2) - (p : E2)))ᗮ.reflection
  let D := linearAction R.toContinuousLinearEquiv
  have hD : D (f p) = p := by
    apply Subtype.ext
    rw [linearAction_isometry_apply]
    exact Submodule.reflection_sub (by simp)
  let d := Hemisphere.chart (norm_eq_of_mem_sphere p)
  have hd0 : d 0 = p := Subtype.ext (Hemisphere.chart_zero (norm_eq_of_mem_sphere p))
  let e := (d.trans P.toOpenPartialHomeomorph).trans D.toHomeomorph.toOpenPartialHomeomorph
  have he0 : (0 : Hemisphere.Plane (p : E2)) ∈ e.source := by
    refine ⟨⟨mem_univ _, ?_⟩, mem_univ _⟩
    change d 0 ∈ P.source
    rw [hd0]
    exact hp
  have he : ContMDiffOn 𝓘(Real, Hemisphere.Plane (p : E2)) (𝓡 1) ∞ e e.source :=
    D.contMDiff.comp_contMDiffOn ((P.contMDiffOn.comp
      (Hemisphere.contMDiff_chart (norm_eq_of_mem_sphere p)).contMDiffOn
      inter_subset_right).mono inter_subset_left)
  have hei : ContMDiffOn (𝓡 1) 𝓘(Real, Hemisphere.Plane (p : E2)) ∞ e.symm e.target := by
    have hPi : ContMDiffOn (𝓡 1) (𝓡 1) ∞ (fun y => P.symm (D.symm y)) e.target :=
      P.symm.contMDiffOn.comp D.symm.contMDiff.contMDiffOn (fun _ hy => hy.2.1)
    exact (Hemisphere.contMDiffOn_chart_symm (norm_eq_of_mem_sphere p)).comp hPi
      (fun _ hy => hy.2.2)
  have hcenter : e 0 = d 0 := by
    change D (P (d 0)) = d 0
    rw [hd0, ← hPf hp, hD]
  obtain ⟨r, hr, L, _, _, _, Phi, _, _, _, _, hPhi⟩ :=
    exists_supported_chart_linearization e d he hei
      (Hemisphere.contMDiff_chart (norm_eq_of_mem_sphere p)).contMDiffOn
      (Hemisphere.contMDiffOn_chart_symm (norm_eq_of_mem_sphere p))
      he0 (mem_univ _) hcenter
  let N := linearAction (Hemisphere.extendLinear p L)
  let q := (N.trans (Phi 1).symm).trans D.symm
  have hpdt : p ∈ d.target := by simpa only [hd0] using d.map_source (mem_univ 0)
  have hdinv : d.symm p = 0 := by simpa only [hd0] using d.left_inv (mem_univ 0)
  have hnear : ∀ᶠ y in 𝓝 p, d.symm y ∈ ball (0 : Hemisphere.Plane (p : E2)) r := by
    have hc := d.continuousOn_symm.continuousAt (d.open_target.mem_nhds hpdt)
    exact hc.preimage_mem_nhds (by rw [hdinv]; exact ball_mem_nhds 0 hr)
  refine ⟨q, ?_⟩
  filter_upwards [d.open_target.mem_nhds hpdt, P.open_source.mem_nhds hp, hnear]
    with y hyd hyp hyr
  have hyball := ball_subset_closedBall hyr
  have hmotion := hPhi (d.symm y) hyball
  have heval : e (d.symm y) = D (f y) := by
    change D (P (d (d.symm y))) = D (f y)
    rw [d.right_inv hyd, ← hPf hyp]
  have hN : N y = d (L (d.symm y)) := by
    calc
      N y = N (d (d.symm y)) := congrArg N (d.right_inv hyd).symm
      _ = d (L (d.symm y)) := linearAction_hemisphere p L (d.symm y)
  apply D.injective
  change D (D.symm ((Phi 1).symm (N y))) = D (f y)
  rw [D.apply_symm_apply]
  apply (Phi 1).injective
  change Phi 1 ((Phi 1).symm (N y)) = Phi 1 (D (f y))
  rw [(Phi 1).apply_symm_apply, hN]
  exact (heval ▸ hmotion).symm

end Poincare.Manifold.Schoenflies.CircleAttachmentGerm
