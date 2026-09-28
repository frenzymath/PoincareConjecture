import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

theorem exists_smooth_unitSpherePolar [FiniteDimensional ℝ E] (q0 : sphere (0 : E) 1) :
    ∃ Q : OpenPartialHomeomorph (sphere (0 : E) 1 × ℝ) E,
      Q.source = univ ×ˢ Ioi 0 ∧ Q.target = ({0} : Set E)ᶜ ∧
      (∀ p, Q p = p.2 • p.1.val) ∧
      (∀ z, (Q.symm z).2 = ‖z‖) ∧
      (∀ z, z ≠ 0 → (Q.symm z).1.val = ‖z‖⁻¹ • z) ∧
      ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ Q ∧
      ContMDiffOn 𝓘(ℝ, E) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ Q.symm Q.target := by
  classical
  let H := homeomorphUnitSphereProd E
  let N : E → sphere (0 : E) 1 := fun z =>
    if hz : z = 0 then q0 else (H ⟨z, hz⟩).1
  let F : sphere (0 : E) 1 × ℝ → E := fun p => p.2 • p.1.val
  let G : E → sphere (0 : E) 1 × ℝ := fun z => (N z, ‖z‖)
  have hN (z : E) (hz : z ≠ 0) : (N z).val = ‖z‖⁻¹ • z := by
    dsimp only [N]
    rw [dif_neg hz]
    exact homeomorphUnitSphereProd_apply_fst_coe E ⟨z, hz⟩
  have hG (z : (({0} : Set E)ᶜ : Set E)) : G z.val = ((H z).1, ((H z).2 : ℝ)) := by
    apply Prod.ext
    · exact dif_neg z.property
    · exact (homeomorphUnitSphereProd_apply_snd_coe E z).symm
  have hFmem (p : sphere (0 : E) 1 × ℝ) (hp : p ∈ univ ×ˢ Ioi 0) : F p ≠ 0 :=
    smul_ne_zero hp.2.ne' (ne_zero_of_mem_unit_sphere p.1)
  have hGF (p : sphere (0 : E) 1 × ℝ) (hp : p ∈ univ ×ˢ Ioi 0) : G (F p) = p := by
    let pH : sphere (0 : E) 1 × Ioi (0 : ℝ) := (p.1, ⟨p.2, hp.2⟩)
    have hval : (H.symm pH).val = F p := homeomorphUnitSphereProd_symm_apply_coe E pH
    have h := hG (H.symm pH)
    rw [hval, H.apply_symm_apply] at h
    exact h
  have hFG (z : E) (hz : z ≠ 0) : F (G z) = z := by
    change ‖z‖ • (N z).val = z
    rw [hN z hz, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hFsmooth : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ F :=
    contMDiff_snd.smul (contMDiff_coe_sphere.comp contMDiff_fst)
  let U : TopologicalSpace.Opens E := ⟨({0} : Set E)ᶜ, isOpen_compl_singleton⟩
  have hn : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun y : U => ‖y.val‖) := by
    intro y
    exact (contDiffAt_norm ℝ y.property).contMDiffAt.comp y (contMDiff_subtype_val y)
  have hs : ContMDiff 𝓘(ℝ, E) (𝓡 n) ∞
      (fun y : U => (⟨‖y.val‖⁻¹ • y.val, by
        simp [norm_smul, norm_ne_zero_iff.mpr y.property]⟩ : sphere (0 : E) 1)) :=
    ((hn.inv₀ (fun y => norm_ne_zero_iff.mpr y.property)).smul
      contMDiff_subtype_val).codRestrict_sphere _
  have hGsub : ContMDiff 𝓘(ℝ, E) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
      (fun y : U => G y.val) := by
    convert hs.prodMk hn using 1
    funext y
    exact Prod.ext (Subtype.ext (hN y.val y.property)) rfl
  have hGsmooth : ContMDiffOn 𝓘(ℝ, E) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ G
      ({0} : Set E)ᶜ := by
    intro z hz
    exact (contMDiffAt_subtype_iff.mp (hGsub ⟨z, hz⟩)).contMDiffWithinAt
  let Q : OpenPartialHomeomorph (sphere (0 : E) 1 × ℝ) E :=
    { toFun := F
      invFun := G
      source := univ ×ˢ Ioi 0
      target := ({0} : Set E)ᶜ
      map_source' := hFmem
      map_target' := fun z hz => ⟨mem_univ _, norm_pos_iff.mpr hz⟩
      left_inv' := hGF
      right_inv' := hFG
      open_source := isOpen_univ.prod isOpen_Ioi
      open_target := isOpen_compl_singleton
      continuousOn_toFun := hFsmooth.continuous.continuousOn
      continuousOn_invFun := hGsmooth.continuousOn }
  exact ⟨Q, rfl, rfl, fun _ => rfl, fun _ => rfl, hN, hFsmooth, hGsmooth⟩

theorem exists_smooth_positive_polar_chart [FiniteDimensional ℝ E] (q0 : sphere (0 : E) 1)
    (rho : OpenPartialHomeomorph ℝ ℝ) (l b r0 : ℝ)
    (hsource : rho.source = Ioo l b) (htarget : rho.target = Ioi r0)
    (hr0 : 0 < r0) (hrho : ContDiffOn ℝ ∞ rho rho.source)
    (hrhoi : ContDiffOn ℝ ∞ rho.symm rho.target) :
    ∃ P : OpenPartialHomeomorph (sphere (0 : E) 1 × ℝ) E,
      P.source = univ ×ˢ Ioo l b ∧ P.target = {z | r0 < ‖z‖} ∧
      (∀ p, P p = rho p.2 • p.1.val) ∧
      (∀ z, (P.symm z).2 = rho.symm ‖z‖) ∧
      (∀ z, z ≠ 0 → (P.symm z).1.val = ‖z‖⁻¹ • z) ∧
      ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ P P.source ∧
      ContMDiffOn 𝓘(ℝ, E) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ P.symm P.target := by
  obtain ⟨Q, hQs, hQt, hQf, hQheight, hQnorm, hQ, hQi⟩ :=
    exists_smooth_unitSpherePolar (n := n) q0
  let C := (OpenPartialHomeomorph.refl (sphere (0 : E) 1)).prod rho
  let P := C.trans Q
  have hPs : P.source = univ ×ˢ Ioo l b := by
    ext p
    rw [OpenPartialHomeomorph.trans_source, hQs]
    change (p ∈ univ ×ˢ rho.source ∧ (p.1, rho p.2) ∈ univ ×ˢ Ioi 0) ↔ _
    simp only [mem_prod, mem_univ, true_and, mem_Ioi, hsource]
    refine ⟨And.left, fun hp => ⟨hp, ?_⟩⟩
    have h := rho.map_source (show p.2 ∈ rho.source by rwa [hsource])
    rw [htarget] at h
    exact hr0.trans h
  have hPt : P.target = {z | r0 < ‖z‖} := by
    ext z
    rw [OpenPartialHomeomorph.trans_target, hQt]
    change (z ∈ ({0} : Set E)ᶜ ∧ Q.symm z ∈ univ ×ˢ rho.target) ↔ r0 < ‖z‖
    simp only [mem_compl_iff, mem_singleton_iff, mem_prod, mem_univ, true_and,
      htarget, mem_Ioi, hQheight]
    exact ⟨And.right, fun hz => ⟨norm_pos_iff.mp (hr0.trans hz), hz⟩⟩
  have hC : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
      C C.source := by
    change ContMDiffOn _ _ ∞ (fun p : sphere (0 : E) 1 × ℝ => (p.1, rho p.2))
      (univ ×ˢ rho.source)
    exact contMDiff_fst.contMDiffOn.prodMk
      (hrho.contMDiffOn.comp contMDiff_snd.contMDiffOn (fun _ hz => hz.2))
  have hCi : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
      C.symm C.target := by
    change ContMDiffOn _ _ ∞ (fun p : sphere (0 : E) 1 × ℝ => (p.1, rho.symm p.2))
      (univ ×ˢ rho.target)
    exact contMDiff_fst.contMDiffOn.prodMk
      (hrhoi.contMDiffOn.comp contMDiff_snd.contMDiffOn (fun _ hz => hz.2))
  refine ⟨P, hPs, hPt, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact hQf (p.1, rho p.2)
  · intro z
    change rho.symm (Q.symm z).2 = rho.symm ‖z‖
    rw [hQheight]
  · intro z hz
    exact hQnorm z hz
  · exact hQ.comp_contMDiffOn (hC.mono inter_subset_left)
  · exact hCi.comp (hQi.mono inter_subset_left) inter_subset_right
