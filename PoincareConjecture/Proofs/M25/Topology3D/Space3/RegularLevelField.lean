import PoincareConjecture.Proofs.M25.Topology3D.Space3.LevelTangentField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlowFirstIntegral
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlowInvariants

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D

def collarHeightLevel (ψ : UnitTwoSphere × ℝ → E3) (u : E3) (t : ℝ) : Set E3 :=
  (fun q : UnitTwoSphere => ψ (q, 0)) '' {q | ⟪u, ψ (q, 0)⟫_ℝ = t}

theorem collarHeightLevel_compact (ψ : UnitTwoSphere × ℝ → E3)
    (hψ : IsCollarEmbedding ψ) (u : E3) (t : ℝ) :
    IsCompact (collarHeightLevel ψ u t) := by
  have he := (collar_central_contMDiff ψ hψ).continuous
  exact (isClosed_eq (continuous_const.inner he) continuous_const).isCompact.image he

theorem collar_regular_height_cross_ne_zero
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (ρ : E3 → ℝ)
    (hρ : ContDiffOn ℝ ∞ ρ (ψ '' (univ ×ˢ Ioo (-1) 1)))
    (hρψ : ∀ p ∈ (univ ×ˢ Ioo (-1) 1 : Set (UnitTwoSphere × ℝ)), ρ (ψ p) = p.2)
    (hρnz : ∀ y ∈ ψ '' (univ ×ˢ Ioo (-1) 1), fderiv ℝ ρ y ≠ 0)
    (u : E3) (q : UnitTwoSphere)
    (hreg : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪u, ψ (p, 0)⟫_ℝ) q ≠ 0) :
    heightCrossMap u (gradient ρ (ψ (q, 0))) ≠ 0 := by
  let e : UnitTwoSphere → E3 := fun p => ψ (p, 0)
  have he := collar_central_contMDiff ψ hψ
  have hqU : e q ∈ ψ '' (univ ×ˢ Ioo (-1) 1) :=
    ⟨(q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hgrad : gradient ρ (e q) ≠ 0 := by
    intro hz
    apply hρnz _ hqU
    rw [← toDual_gradient, hz, map_zero]
  have hzero : ρ ∘ e = fun _ => 0 :=
    funext fun p => hρψ (p, 0) ⟨mem_univ _, by norm_num⟩
  have hd := ((hρ.contDiffAt ((collar_image_open ψ hψ).mem_nhds hqU)).differentiableAt
    (by simp)).hasFDerivAt.hasMFDerivAt.comp q
      (he.mdifferentiable (by simp) q).hasMFDerivAt
  have hmap := hd.mfderiv
  rw [hzero, mfderiv_const] at hmap
  have hheight := (InnerProductSpace.toDual ℝ E3 u).hasFDerivAt.hasMFDerivAt.comp q
    (he.mdifferentiable (by simp) q).hasMFDerivAt
  apply heightCrossMap_ne_zero_of_regular_derivative (V := E2)
    (mfderiv (𝓡 2) 𝓘(ℝ, E3) e q) _ _ hgrad
  · intro v
    rw [inner_gradient_left]
    exact congrArg (fun A => A v) hmap.symm
  · intro hz
    exact hreg (hheight.mfderiv.trans hz)

theorem exists_regular_collar_level_field
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ) (u : E3) (t : ℝ)
    (hreg : ∀ q : UnitTwoSphere, ⟪u, ψ (q, 0)⟫_ℝ = t →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪u, ψ (p, 0)⟫_ℝ) q ≠ 0) :
    ∃ g : E3 → E3, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∀ y ∈ collarHeightLevel ψ u t, g y ≠ 0) ∧
      ∀ (K L : ℝ≥0) (hK : LipschitzWith K g) (hL : ∀ y, ‖g y‖ ≤ L),
        ∀ y ∈ collarHeightLevel ψ u t, ∀ s : ℝ,
          boundedFlow g hK hL y s ∈ collarHeightLevel ψ u t := by
  obtain ⟨ρ, hρ, hρψ, hρnz⟩ := exists_sphere_collar_defining_function ψ hψ
  let U : Set E3 := ψ '' (univ ×ˢ Ioo (-1) 1)
  let W : E3 → E3 := fun y => heightCrossMap u (gradient ρ y)
  let V : Set E3 := U ∩ W ⁻¹' ({0} : Set E3)ᶜ
  have hU : IsOpen U := collar_image_open ψ hψ
  have hW : ContDiffOn ℝ ∞ W U := gradientHeightCross_contDiffOn hU ρ hρ u
  have hV : IsOpen V := hW.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hSV : collarHeightLevel ψ u t ⊆ V := by
    rintro y ⟨q, hq, rfl⟩
    refine ⟨⟨(q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩, ?_⟩
    exact collar_regular_height_cross_ne_zero ψ hψ ρ hρ hρψ hρnz u q (hreg q hq)
  obtain ⟨g, hg, hgc, hgs, hnear, hgρ, hgh⟩ :=
    exists_compact_level_tangent_field (collarHeightLevel_compact ψ hψ u t)
      hV hSV ρ (hρ.mono inter_subset_left) u
  refine ⟨g, hg, hgc, ?_, ?_⟩
  · intro y hy
    rw [subset_of_mem_nhdsSet hnear hy]
    exact (hSV hy).2
  · intro K L hK hL y hy s
    have hz (z : E3) (hz : z ∉ V) : g z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hm => hz (hgs hm))
    have hflowV := boundedFlow_mapsTo_set g hK hL hz s (hSV hy)
    have hρflow := boundedFlow_preserves_firstIntegral g hK hL hz ρ
      (fun z hz => (hρ.contDiffAt (hU.mem_nhds hz.1)).differentiableAt (by simp))
      (fun z _ => hgρ z) y (hSV hy) s
    have hhflow := boundedFlow_preserves_linear g hK hL
      (InnerProductSpace.toDual ℝ E3 u) hgh y s
    obtain ⟨q0, hq0, rfl⟩ := hy
    have hρzero : ρ (boundedFlow g hK hL (ψ (q0, 0)) s) = 0 :=
      hρflow.trans (hρψ (q0, 0) ⟨mem_univ _, by norm_num⟩)
    obtain ⟨⟨q, r⟩, hqr, heq⟩ := hflowV.1
    have hr : r = 0 := (hρψ (q, r) hqr).symm.trans ((congrArg ρ heq).trans hρzero)
    subst r
    refine ⟨q, ?_, heq⟩
    exact (congrArg (fun z => ⟪u, z⟫_ℝ) heq).trans (hhflow.trans hq0)

end PoincareConjecture.M25.Topology3D
