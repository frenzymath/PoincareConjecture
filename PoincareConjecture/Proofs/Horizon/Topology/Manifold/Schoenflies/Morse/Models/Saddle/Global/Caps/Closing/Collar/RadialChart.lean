import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.SphereProjection



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩


theorem sphereProjection_pos_smul (q : S2) {t : Real} (ht : 0 < t) :
    sphereProjection (t • (q : E3)) = q := by
  apply Subtype.ext
  rw [sphereProjection_coe (smul_ne_zero ht.ne' (ne_zero_of_mem_unit_sphere q)),
    norm_smul, Real.norm_eq_abs, abs_of_pos ht, norm_eq_of_mem_sphere q, mul_one,
    smul_smul, inv_mul_cancel₀ ht.ne', one_smul]



def radialDiskChart (m : OpenPartialHomeomorph E2 S2)
    (hm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m m.source)
    (hmi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m.symm m.target) :
    PartialDiffeomorph 𝓘(Real, E2 × Real) (𝓡 3) (E2 × Real) E3 ∞ where
  toFun z := (1 + z.2) • (m z.1 : E3)
  invFun z := (m.symm (sphereProjection z), ‖z‖ - 1)
  source := m.source ×ˢ Ioi (-1)
  target := {z | z ≠ 0 ∧ sphereProjection z ∈ m.target}
  map_source' := by
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    have hpos : 0 < 1 + t := by change -1 < t at ht; linarith
    refine ⟨smul_ne_zero hpos.ne' (ne_zero_of_mem_unit_sphere (m y)), ?_⟩
    rw [sphereProjection_pos_smul (m y) hpos]
    exact m.map_source hy
  map_target' := by
    intro z hz
    refine ⟨m.map_target hz.2, ?_⟩
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz.1
    change -1 < ‖z‖ - 1
    linarith
  left_inv' := by
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    have hpos : 0 < 1 + t := by change -1 < t at ht; linarith
    apply Prod.ext
    · change m.symm (sphereProjection ((1 + t) • (m y : E3))) = y
      rw [sphereProjection_pos_smul (m y) hpos, m.left_inv hy]
    · change ‖(1 + t) • (m y : E3)‖ - 1 = t
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos, norm_eq_of_mem_sphere (m y), mul_one]
      ring
  right_inv' := by
    intro z hz
    change (1 + (‖z‖ - 1)) • (m (m.symm (sphereProjection z)) : E3) = z
    rw [m.right_inv hz.2, sphereProjection_coe hz.1]
    rw [show 1 + (‖z‖ - 1) = ‖z‖ by ring, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz.1), one_smul]
  open_source := m.open_source.prod isOpen_Ioi
  open_target := by
    have hp : ContinuousOn sphereProjection ({0}ᶜ : Set E3) :=
      fun z hz => (contMDiffAt_sphereProjection hz).continuousAt.continuousWithinAt
    change IsOpen (({0}ᶜ : Set E3) ∩ sphereProjection ⁻¹' m.target)
    exact hp.isOpen_inter_preimage isClosed_singleton.isOpen_compl m.open_target
  contMDiffOn_toFun := by
    have hmc : ContDiffOn Real ∞ (fun y => (m y : E3)) m.source :=
      (contMDiff_coe_sphere.comp_contMDiffOn hm).contDiffOn
    exact ((contDiffOn_const.add contDiffOn_snd).smul
      (hmc.comp contDiffOn_fst (fun z hz => hz.1))).contMDiffOn
  contMDiffOn_invFun := by
    intro z hz
    have hp := contMDiffAt_sphereProjection hz.1
    have hms := (hmi (sphereProjection z) hz.2).contMDiffAt (m.open_target.mem_nhds hz.2)
    exact ((hms.comp z hp).contDiffAt.prodMk
      ((contDiffAt_norm Real hz.1).sub (contDiffAt_const (c := (1 : Real))))).contMDiffAt.contMDiffWithinAt

@[simp] theorem radialDiskChart_source (m : OpenPartialHomeomorph E2 S2)
    (hm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m m.source)
    (hmi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m.symm m.target) :
    (radialDiskChart m hm hmi).source = m.source ×ˢ Ioi (-1) := rfl

@[simp] theorem radialDiskChart_target (m : OpenPartialHomeomorph E2 S2)
    (hm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m m.source)
    (hmi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m.symm m.target) :
    (radialDiskChart m hm hmi).target = {z | z ≠ 0 ∧ sphereProjection z ∈ m.target} := rfl

@[simp] theorem radialDiskChart_apply (m : OpenPartialHomeomorph E2 S2)
    (hm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m m.source)
    (hmi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m.symm m.target) (z : E2 × Real) :
    radialDiskChart m hm hmi z = (1 + z.2) • (m z.1 : E3) := rfl

@[simp] theorem radialDiskChart_symm_apply (m : OpenPartialHomeomorph E2 S2)
    (hm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m m.source)
    (hmi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m.symm m.target) (z : E3) :
    (radialDiskChart m hm hmi).symm z = (m.symm (sphereProjection z), ‖z‖ - 1) := rfl

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
