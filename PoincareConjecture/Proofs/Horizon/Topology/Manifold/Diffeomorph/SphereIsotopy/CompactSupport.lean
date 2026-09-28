import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereIsotopy.LocalNormalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.ParametricInverse










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric IsManifold
open scoped Manifold ContDiff

namespace Poincare.Manifold.SphereIsotopy

private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev S2 := PoincareConjecture.UnitTwoSphere



theorem exists_plane_diffeomorph
    (d : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞) (p : S2)
    {U : Set S2} (hU : IsOpen U) (hpU : p ∈ U) (hdU : EqOn d id U) :
    ∃ g : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      (∀ x, g x = centeredChart (-p) (d ((centeredChart (-p)).symm x))) ∧
      ∃ K : Set E2, IsCompact K ∧ ∀ x, x ∉ K → g x = x := by
  let c := centeredChart (-p)
  have hcsource : c.source = {p}ᶜ := by simp [c]
  have hctarget : c.target = univ := centeredChart_target _
  have hp : d p = p := hdU hpU
  have hip : d.symm p = p := by
    apply d.injective
    change d (d.symm p) = d p
    rw [d.apply_symm_apply, hp]
  have hd : MapsTo d c.source c.source := by
    intro q hq
    simp only [hcsource, mem_compl_iff, mem_singleton_iff] at hq ⊢
    exact fun h => hq (d.injective (h.trans hp.symm))
  have hdi : MapsTo d.symm c.source c.source := by
    intro q hq
    simp only [hcsource, mem_compl_iff, mem_singleton_iff] at hq ⊢
    exact fun h => hq (d.symm.injective (h.trans hip.symm))
  have hx (x : E2) : x ∈ c.target := by rw [hctarget]; trivial
  have hcx (x : E2) : c.symm x ∈ c.source := c.map_target (hx x)
  have hcm := centeredChart_mem_maximalAtlas (-p)
  have hcs := contMDiffOn_of_mem_maximalAtlas hcm
  have hcis := contMDiffOn_symm_of_mem_maximalAtlas hcm
  let g : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ := {
    toEquiv := {
      toFun := fun x => c (d (c.symm x))
      invFun := fun x => c (d.symm (c.symm x))
      left_inv := by
        intro x
        change c (d.symm (c.symm (c (d (c.symm x))))) = x
        rw [c.left_inv (hd (hcx x)), d.symm_apply_apply, c.right_inv (hx x)]
      right_inv := by
        intro x
        change c (d (c.symm (c (d.symm (c.symm x))))) = x
        rw [c.left_inv (hdi (hcx x)), d.apply_symm_apply, c.right_inv (hx x)] }
    contMDiff_toFun := by
      intro x
      change ContMDiffAt (𝓡 2) (𝓡 2) ∞ (fun x => c (d (c.symm x))) x
      exact (hcs.contMDiffAt (c.open_source.mem_nhds (hd (hcx x)))).comp x
        (d.contMDiff.contMDiffAt.comp x
          (hcis.contMDiffAt (c.open_target.mem_nhds (hx x))))
    contMDiff_invFun := by
      intro x
      change ContMDiffAt (𝓡 2) (𝓡 2) ∞ (fun x => c (d.symm (c.symm x))) x
      exact (hcs.contMDiffAt (c.open_source.mem_nhds (hdi (hcx x)))).comp x
        (d.symm.contMDiff.contMDiffAt.comp x
          (hcis.contMDiffAt (c.open_target.mem_nhds (hx x)))) }
  have hUc : Uᶜ ⊆ c.source := by
    intro q hq
    rw [hcsource]
    exact fun h => hq (h ▸ hpU)
  have hcompact : IsCompact (c '' Uᶜ) :=
    hU.isClosed_compl.isCompact.image_of_continuousOn (hcs.continuousOn.mono hUc)
  refine ⟨g, fun _ => rfl, c '' Uᶜ, hcompact, ?_⟩
  intro x hxK
  have hxU : c.symm x ∈ U := by
    by_contra h
    exact hxK ⟨c.symm x, h, c.right_inv (hx x)⟩
  change c (d (c.symm x)) = x
  rw [hdU hxU]
  exact c.right_inv (hx x)



theorem exists_sphere_isotopy_of_plane_isotopy
    (d : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞) (p : S2) (hp : d p = p)
    (F : ℝ → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hF0 : ∀ x, F 0 x = x)
    (hFs : ContDiff ℝ ∞ (fun z : ℝ × E2 => F z.1 z.2))
    {K : Set E2} (hK : IsCompact K) (hfix : ∀ t x, x ∉ K → F t x = x)
    (hF1 : ∀ x, F 1 x = centeredChart (-p) (d ((centeredChart (-p)).symm x))) :
    ∃ Φ : ℝ → Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun z : ℝ × S2 => Φ z.1 z.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun z : ℝ × S2 => (Φ z.1).symm z.2) ∧
      (∀ q, Φ 0 q = q) ∧ (∀ q, Φ 1 q = d q) ∧ (∀ t, Φ t p = p) := by
  let c := centeredChart (-p)
  have hcsource : c.source = {p}ᶜ := by simp [c]
  have hctarget : c.target = univ := centeredChart_target _
  have hcm := centeredChart_mem_maximalAtlas (-p)
  obtain ⟨_, hsupport, Φ, hΦ0, hΦs, hΦfix, hΦcoord⟩ :=
    Schoenflies.exists_supported_chart_isotopy c.symm
      (contMDiffOn_symm_of_mem_maximalAtlas hcm)
      (contMDiffOn_of_mem_maximalAtlas hcm) hK
      (by simp [c]) F hF0 hFs hfix
  have hΦp (t : ℝ) : Φ t p = p := by
    apply hΦfix
    intro h
    have h' := hsupport h
    simp [hcsource] at h'
  refine ⟨Φ, hΦs, contMDiff_diffeomorph_family_symm Φ hΦs, hΦ0, ?_, hΦp⟩
  intro q
  by_cases hq : q = p
  · subst q
    rw [hΦp, hp]
  have hqc : q ∈ c.source := by simpa [hcsource] using hq
  have hdqc : d q ∈ c.source := by
    rw [hcsource]
    exact fun h => hq (d.injective (h.trans hp.symm))
  have hx : c q ∈ c.target := c.map_source hqc
  have h := hΦcoord 1 (c q) hx
  rw [c.left_inv hqc, hF1, c.left_inv hqc, c.left_inv hdqc] at h
  exact h

end Poincare.Manifold.SphereIsotopy
