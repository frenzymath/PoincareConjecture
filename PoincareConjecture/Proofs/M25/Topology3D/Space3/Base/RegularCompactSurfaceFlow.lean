import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularBandField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothFlow
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_regular_compact_surface_flow
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere)
    (A : Set UnitTwoSphere) (hA : IsCompact A)
    (hreg : ∀ q ∈ A,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q ≠ 0) :
    let U : Set E3 := psi '' (univ ×ˢ Ioo (-1) 1)
    let K : Set E3 := (fun q : UnitTwoSphere => psi (q, 0)) '' A
    ∃ rho : E3 → ℝ,
      ContDiffOn ℝ ∞ rho U ∧
      (∀ p ∈ (univ ×ˢ Ioo (-1) 1 : Set (UnitTwoSphere × ℝ)),
        rho (psi p) = p.2) ∧
      (∀ y ∈ U, fderiv ℝ rho y ≠ 0) ∧
      ∃ N : Set E3,
        IsCompact N ∧ K ⊆ interior N ∧ N ⊆ U ∧
        (∀ y ∈ N, tangentHeightVector (gradient rho y) (u : E3) ≠ 0) ∧
        ∃ F : E3 → E3,
          ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ U ∧
          (∀ y : E3, fderiv ℝ rho y (F y) = 0) ∧
          (∀ y ∈ N, ⟪(u : E3), F y⟫_ℝ = 1) ∧
          ∃ L M : ℝ≥0, ∃ hL : LipschitzWith L F,
            ∃ hM : ∀ y : E3, ‖F y‖ ≤ M,
              ContDiff ℝ ∞
                (fun p : E3 × ℝ => boundedFlow F hL hM p.1 p.2) ∧
              (∀ t : ℝ,
                (fun y : E3 => boundedFlow F hL hM y t) ''
                    range (fun q : UnitTwoSphere => psi (q, 0)) =
                  range (fun q : UnitTwoSphere => psi (q, 0))) ∧
              ∀ y : E3, y ∉ U → ∀ t : ℝ,
                boundedFlow F hL hM y t = y := by
  obtain ⟨rho, hrho, hrhopsi, hrhonz⟩ :=
    exists_sphere_collar_defining_function psi hpsi
  let U : Set E3 := psi '' (univ ×ˢ Ioo (-1) 1)
  let K : Set E3 := (fun q : UnitTwoSphere => psi (q, 0)) '' A
  let V : E3 → E3 := fun y => tangentHeightVector (gradient rho y) (u : E3)
  let R : Set E3 := U ∩ V ⁻¹' ({0} : Set E3)ᶜ
  have hK : IsCompact K := hA.image_of_continuousOn
    (collar_central_contMDiff psi hpsi).continuous.continuousOn
  have hU : IsOpen U := collar_image_open psi hpsi
  have hn (y : E3) (hy : y ∈ U) : gradient rho y ≠ 0 := by
    intro hz
    apply hrhonz y hy
    rw [← toDual_gradient, hz, map_zero]
  have hV : ContDiffOn ℝ ∞ V U := tangentHeightVector_contDiffOn (gradient rho)
    (contDiffOn_gradient_of_isOpen hU rho hrho) hn (u : E3)
  have hR : IsOpen R :=
    hV.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hKR : K ⊆ R := by
    rintro y ⟨q, hq, rfl⟩
    refine ⟨⟨(q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩, ?_⟩
    exact tangentHeightVector_ne_zero_of_heightCross _ _
      (collar_regular_height_cross_ne_zero psi hpsi rho hrho hrhopsi hrhonz
        (u : E3) q (hreg q hq))
  obtain ⟨N, hN, hKN, hNR⟩ := exists_compact_between hK hR hKR
  have hNU : N ⊆ U := fun y hy => (hNR hy).1
  have hNV : ∀ y ∈ N, tangentHeightVector (gradient rho y) (u : E3) ≠ 0 :=
    fun y hy => (hNR hy).2
  obtain ⟨F, hF, hFc, hFs, hFrho, hFH⟩ :=
    exists_compact_height_band_field hN hU hNU rho hrho hn (u : E3)
      (fun _ : ℝ => (1 : ℝ)) contDiff_const (fun y hy _ => hNV y hy)
  obtain ⟨L, M, hL, hM⟩ := compactField_bounds F hF hFc
  have hzero (y : E3) (hy : y ∉ U) : F y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hy (hFs hm))
  have hpreserve (y : E3) (hy : y ∈ range (fun q : UnitTwoSphere => psi (q, 0)))
      (t : ℝ) : boundedFlow F hL hM y t ∈
        range (fun q : UnitTwoSphere => psi (q, 0)) := by
    obtain ⟨q, rfl⟩ := hy
    have hqU : psi (q, 0) ∈ U := ⟨(q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
    have hflowU := boundedFlow_mapsTo_set F hL hM hzero t hqU
    have hrhoflow := boundedFlow_preserves_firstIntegral F hL hM hzero rho
      (fun v hv => (hrho.contDiffAt (hU.mem_nhds hv)).differentiableAt (by simp))
      (fun v _ => hFrho v) (psi (q, 0)) hqU t
    have hrhozero : rho (boundedFlow F hL hM (psi (q, 0)) t) = 0 :=
      hrhoflow.trans (hrhopsi (q, 0) ⟨mem_univ _, by norm_num⟩)
    obtain ⟨⟨p, s⟩, hps, heq⟩ := hflowU
    have hs : s = 0 :=
      (hrhopsi (p, s) hps).symm.trans ((congrArg rho heq).trans hrhozero)
    subst s
    exact ⟨p, heq⟩
  refine ⟨rho, hrho, hrhopsi, hrhonz, N, hN, hKN, hNU, hNV,
    F, hF, hFc, hFs, hFrho, hFH, L, M, hL, hM,
    boundedFlow_contDiff F hL hM hF hFc, ?_, ?_⟩
  · intro t
    apply subset_antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hpreserve x hx t
    · intro y hy
      refine ⟨boundedFlow F hL hM y (-t), hpreserve y hy (-t), ?_⟩
      simpa only [neg_neg] using boundedFlow_neg F hL hM y (-t)
  · intro y hy t
    exact boundedFlow_eq_self F hL hM y (hzero y hy) t

end PoincareConjecture.M25.Topology3D
