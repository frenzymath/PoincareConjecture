import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverSurjective













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)





theorem scalarNormalizedCoverMap_fiber_finite {H : Plane → ℝ} {V : Cover → ℝ}
    (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hVc : ContinuousOn V scalarCoverStrip)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : 0 < P)
    (hdeck : ∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P)
    (a : scalarPotentialStrip) :
    (scalarCoverStrip ∩ scalarNormalizedCoverMap H V P ⁻¹' {(a : Cover)}).Finite := by
  let K := scalarCoverStrip ∩ scalarNormalizedCoverMap H V P ⁻¹' {(a : Cover)}
  have hK : IsCompact K := scalarNormalizedCoverMap_compact_preimage hHc hinner houter
    hVc hP hdeck isCompact_singleton (by
      intro y hy
      have heq : y = (a : Cover) := hy
      exact heq ▸ a.property)
  by_contra hinfinite
  have hinf : K.Infinite := hinfinite
  obtain ⟨z, hz, hacc⟩ := hinf.exists_accPt_of_subset_isCompact hK subset_rfl
  have hi := (scalarNormalizedCoverMap_open_and_discrete D hHc hHs hlap hinner houter
    hdV hP.ne' hz.1).2
  exact (accPt_iff_frequently_nhdsNE.mp hacc) (hi.mono fun y hy hyK =>
    hy (hyK.2.trans hz.2.symm))





theorem scalarNormalizedCover_fiber_finite {H : Plane → ℝ} {V : Cover → ℝ}
    (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hVc : ContinuousOn V scalarCoverStrip)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : 0 < P)
    (hdeck : ∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P)
    (hrange : ∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1) (a : scalarPotentialStrip) :
    (scalarNormalizedCover H V P hrange ⁻¹' {a}).Finite := by
  have hfin := scalarNormalizedCoverMap_fiber_finite D hHc hHs hlap hinner houter
    hVc hdV hP hdeck a
  have hpre := hfin.preimage (f := (Subtype.val : scalarCoverStrip → Cover))
    Subtype.val_injective.injOn
  convert hpre using 1
  ext z
  simp only [mem_preimage, mem_singleton_iff, mem_inter_iff]
  constructor
  · intro heq
    exact ⟨z.property, congrArg Subtype.val heq⟩
  · intro hz
    exact Subtype.ext hz.2

end PoincareConjecture.M64Uniformization
