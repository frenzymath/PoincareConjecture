import PoincareConjecture.Proofs.M38.SmoothCirclePullback
import PoincareConjecture.Definitions.Ch15.SurgeryTopology










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38



theorem sphereBundle_pullback_height_regular (Q : GeneralizedSliceCarrier)
    (B : SurgerySphereBundle Q) :
    ∀ a : (circlePullbackCarrier Q B.projection B.projection_smooth).carrier,
      mfderiv (𝓡 3) 𝓘(ℝ, ℝ)
        (circlePullbackHeight Q B.projection B.projection_smooth) a ≠ 0 := by
  intro a
  let q := circlePullbackProjection Q B.projection B.projection_smooth
  let h := circlePullbackHeight Q B.projection B.projection_smooth
  let t₀ := h a
  obtain ⟨U, hU, haU, f, g, himage, hleft, _, _, hg, hproj⟩ :=
    B.local_trivialization (B.projection (q a))
  have hginv (p : UnitTwoSphere × UnitCircle) (hp : p ∈ univ ×ˢ U) :
      B.projection (g p) = p.2 := by
    obtain ⟨y, hy, hfy⟩ := himage.symm ▸ hp
    rw [← hfy, hleft hy, hproj y hy]
  have hrel : B.projection (q a) = unitCircleExp t₀ :=
    CirclePullback.projection_height B.projection a
  have hp₀ : ((f (q a)).1, unitCircleExp t₀) = f (q a) :=
    Prod.ext rfl (hrel.symm.trans (hproj (q a) haU).symm)
  let Γ : ℝ → Q.carrier := fun t => g ((f (q a)).1, unitCircleExp t)
  have hΓ₀ : Γ t₀ = q a := by
    change g ((f (q a)).1, unitCircleExp t₀) = q a
    rw [hp₀, hleft haU]
  have hΓ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) ∞ Γ t₀ :=
    (hg.contMDiffAt ((isOpen_univ.prod hU).mem_nhds
      ⟨mem_univ _, hrel ▸ haU⟩)).comp t₀
        (contMDiffAt_const.prodMk (contMDiff_unitCircleExp t₀))
  let L := (circlePullback_projection_localDiffeomorph Q
    B.projection B.projection_smooth) a
  let γ := fun t => L.localInverse (Γ t)
  have hγ₀ : γ t₀ = a := by
    change L.localInverse (Γ t₀) = a
    rw [hΓ₀]
    exact L.localInverse_left_inv L.localInverse_mem_target
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) ∞ γ t₀ := by
    apply ContMDiffAt.comp t₀ _ hΓ
    rw [hΓ₀]
    exact L.localInverse_contMDiffAt
  have hh : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ h :=
    circlePullback_height_smooth Q B.projection B.projection_smooth
  let E := isLocalDiffeomorph_unitCircleExp t₀
  have hclock : (fun t => h (γ t)) =ᶠ[𝓝 t₀] id := by
    have heU : unitCircleExp ⁻¹' U ∈ 𝓝 t₀ :=
      contMDiff_unitCircleExp.continuous.continuousAt.preimage_mem_nhds
        (hU.mem_nhds (hrel ▸ haU))
    have hΓU : Γ ⁻¹' L.localInverse.source ∈ 𝓝 t₀ :=
      hΓ.continuousAt.preimage_mem_nhds
        (by rw [hΓ₀]; exact L.localInverse.open_source.mem_nhds L.localInverse_mem_source)
    have hγE : (fun t => h (γ t)) ⁻¹' E.localInverse.target ∈ 𝓝 t₀ :=
      (hh.continuous.continuousAt.comp hγ.continuousAt).preimage_mem_nhds
        (by
          change E.localInverse.target ∈ 𝓝 (h (γ t₀))
          rw [hγ₀]
          exact E.localInverse.open_target.mem_nhds E.localInverse_mem_target)
    filter_upwards [heU, hΓU, hγE,
      E.localInverse.open_target.mem_nhds E.localInverse_mem_target] with t ht hΓt hγt htE
    have he : unitCircleExp (h (γ t)) = unitCircleExp t := by
      change unitCircleExp (CirclePullback.height B.projection (γ t)) = unitCircleExp t
      rw [← CirclePullback.projection_height B.projection (γ t)]
      change B.projection (q (L.localInverse (Γ t))) = unitCircleExp t
      exact (congrArg B.projection (L.localInverse_right_inv hΓt)).trans
        (hginv _ ⟨mem_univ _, ht⟩)
    exact (E.localInverse_left_inv hγt).symm.trans
      ((congrArg E.localInverse he).trans (E.localInverse_left_inv htE))
  intro hzero
  have hd := mfderiv_comp t₀ (hh.mdifferentiable (by simp) (γ t₀))
    (hγ.mdifferentiableAt (by simp))
  rw [hγ₀, hzero, ContinuousLinearMap.zero_comp] at hd
  have hid := hclock.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (h ∘ γ) t₀ =
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id t₀ at hid
  rw [hd, mfderiv_id] at hid
  have hbad := congrArg (fun e : ℝ →L[ℝ] ℝ => e 1) hid
  change (0 : ℝ) = 1 at hbad
  exact zero_ne_one hbad

end PoincareConjecture.M38
