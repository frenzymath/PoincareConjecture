import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightBandField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularLevelField

set_option autoImplicit false

open Set Filter Function
open scoped ContDiff Manifold InnerProductSpace NNReal Topology Matrix

namespace PoincareConjecture.M25.Topology3D

theorem tangentHeightVector_ne_zero_of_heightCross (n u : E3)
    (hcross : heightCrossMap u n ≠ 0) : tangentHeightVector n u ≠ 0 := by
  intro hz
  have hu : u = (⟪n, u⟫_ℝ / ⟪n, n⟫_ℝ) • n := sub_eq_zero.mp hz
  apply hcross
  rw [hu]
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  change WithLp.ofLp n ⨯₃ ((⟪n, u⟫_ℝ / ⟪n, n⟫_ℝ) • WithLp.ofLp n) = 0
  rw [map_smul, cross_self, smul_zero]

theorem exists_regular_collar_band_field
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ) (u : E3) (a b : ℝ)
    (hreg : ∀ q : UnitTwoSphere, ⟪u, ψ (q, 0)⟫_ℝ ∈ Icc a b →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪u, ψ (p, 0)⟫_ℝ) q ≠ 0) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      (∀ᶠ z in 𝓝ˢ (Icc a b), β z = 1) ∧ (∀ z, β z ∈ Icc 0 1) ∧
      ∃ F : E3 → E3, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
        (∀ q : UnitTwoSphere, ⟪u, F (ψ (q, 0))⟫_ℝ = β ⟪u, ψ (q, 0)⟫_ℝ) ∧
        ∀ (K L : ℝ≥0) (hK : LipschitzWith K F) (hL : ∀ y, ‖F y‖ ≤ L),
          ∀ q : UnitTwoSphere, ∀ s : ℝ,
            boundedFlow F hK hL (ψ (q, 0)) s ∈ range (fun p : UnitTwoSphere => ψ (p, 0)) := by
  obtain ⟨ρ, hρ, hρψ, hρnz⟩ := exists_sphere_collar_defining_function ψ hψ
  let e : UnitTwoSphere → E3 := fun q => ψ (q, 0)
  let U : Set E3 := ψ '' (univ ×ˢ Ioo (-1) 1)
  let W : E3 → E3 := fun y => heightCrossMap u (gradient ρ y)
  have he := (collar_central_contMDiff ψ hψ).continuous
  have hU : IsOpen U := collar_image_open ψ hψ
  have heU (q : UnitTwoSphere) : e q ∈ U :=
    ⟨(q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hn (y : E3) (hy : y ∈ U) : gradient ρ y ≠ 0 := by
    intro hz
    apply hρnz y hy
    rw [← toDual_gradient, hz, map_zero]
  have hW : ContDiffOn ℝ ∞ W U := gradientHeightCross_contDiffOn hU ρ hρ u
  have hWe : Continuous (W ∘ e) := hW.continuousOn.comp_continuous he heU
  let H : UnitTwoSphere → ℝ := fun q => ⟪u, e q⟫_ℝ
  have hH : Continuous H := continuous_const.inner he
  let C : Set ℝ := H '' {q | W (e q) = 0}
  have hC : IsCompact C := (isClosed_eq hWe continuous_const).isCompact.image hH
  have hIC : Icc a b ⊆ Cᶜ := by
    intro z hz hzC
    obtain ⟨q, hq, hqz⟩ := hzC
    have hqI : ⟪u, ψ (q, 0)⟫_ℝ ∈ Icc a b := by
      change H q ∈ Icc a b
      rwa [hqz]
    exact collar_regular_height_cross_ne_zero ψ hψ ρ hρ hρψ hρnz u q (hreg q hqI) hq
  obtain ⟨β, hβ, hβc, hβs, hβnear, hβrange⟩ :=
    exists_compact_smooth_cutoff isCompact_Icc hC.isClosed.isOpen_compl hIC
  have hS : IsCompact (range e) := isCompact_range he
  have hSU : range e ⊆ U := by
    rintro y ⟨q, rfl⟩
    exact heU q
  have hproj : ∀ y ∈ range e, ⟪u, y⟫_ℝ ∈ tsupport β →
      tangentHeightVector (gradient ρ y) u ≠ 0 := by
    rintro y ⟨q, rfl⟩ hqβ
    apply tangentHeightVector_ne_zero_of_heightCross
    intro hz
    exact hβs hqβ ⟨q, hz, rfl⟩
  obtain ⟨F, hF, hFc, hFs, hFρ, hFH⟩ :=
    exists_compact_height_band_field hS hU hSU ρ hρ hn u β hβ hproj
  refine ⟨β, hβ, hβc, hβnear, hβrange, F, hF, hFc,
    fun q => hFH (e q) ⟨q, rfl⟩, ?_⟩
  intro K L hK hL q s
  have hzero (y : E3) (hy : y ∉ U) : F y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hy (hFs hm))
  have hflowU := boundedFlow_mapsTo_set F hK hL hzero s (heU q)
  have hρflow := boundedFlow_preserves_firstIntegral F hK hL hzero ρ
    (fun y hy => (hρ.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
    (fun y _ => hFρ y) (e q) (heU q) s
  have hρzero : ρ (boundedFlow F hK hL (e q) s) = 0 :=
    hρflow.trans (hρψ (q, 0) ⟨mem_univ _, by norm_num⟩)
  obtain ⟨⟨p, r⟩, hpr, heq⟩ := hflowU
  have hr : r = 0 := (hρψ (p, r) hpr).symm.trans ((congrArg ρ heq).trans hρzero)
  subst r
  exact ⟨p, heq⟩

end PoincareConjecture.M25.Topology3D
