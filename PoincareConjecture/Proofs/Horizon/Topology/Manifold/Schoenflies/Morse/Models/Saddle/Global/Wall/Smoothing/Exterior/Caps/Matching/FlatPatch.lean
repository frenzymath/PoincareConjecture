import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Matching.LocalSide
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.ModelSpaces

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Matching

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev S1 := sphere (0 : E2) 1

theorem eventually_range_iff_wall_of_flat_arc
    (γ : S1 → E2)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ γ)
    {q : S1} (hflat : ∀ᶠ p in 𝓝 q, γ p 0 = 0) :
    ∀ᶠ x in 𝓝 (γ q), x ∈ range γ ↔ x 0 = 0 := by
  let L₀ : E2 →L[Real] Real := EuclideanSpace.proj 0
  let L₁ : E2 →L[Real] Real := EuclideanSpace.proj 1
  let y : S1 → Real := L₁ ∘ γ
  let dγ : E1 →L[Real] E2 := mfderiv (𝓡 1) (𝓡 2) γ q
  let dy : E1 →L[Real] Real := mfderiv (𝓡 1) 𝓘(Real, Real) y q
  have hL₀ : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ L₀ := L₀.contDiff.contMDiff
  have hL₁ : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ L₁ := L₁.contDiff.contMDiff
  have hy : ContMDiff (𝓡 1) 𝓘(Real, Real) ∞ y := L₁.contMDiff.comp hγ.contMDiff
  have hmd := hγ.contMDiff.mdifferentiable (by simp) q
  have hzero : L₀.comp dγ = 0 := by
    have he : L₀ ∘ γ =ᶠ[𝓝 q] fun _ => (0 : Real) := hflat
    have hc := mfderiv_comp q (hL₀.mdifferentiable (by simp) (γ q)) hmd
    rw [he.mfderiv_eq, mfderiv_const, mfderiv_eq_fderiv, L₀.fderiv] at hc
    exact hc.symm
  have hdy : dy = L₁.comp dγ := by
    change mfderiv (𝓡 1) 𝓘(Real, Real) (L₁ ∘ γ) q = _
    rw [mfderiv_comp q (hL₁.mdifferentiable (by simp) (γ q)) hmd,
      mfderiv_eq_fderiv, L₁.fderiv]
  have hγinj := (hγ.isImmersion.isImmersionAt q).injective_mfderiv_modelWithCornersSelf
    (by simp)
  have hyinj : Injective dy := by
    intro u v huv
    apply hγinj
    change dγ u = dγ v
    ext i
    fin_cases i
    · have hu := congrArg (fun L => L u) hzero
      have hv := congrArg (fun L => L v) hzero
      exact hu.trans hv.symm
    · rw [hdy] at huv
      exact huv
  have hybij : Bijective (mfderiv (𝓡 1) 𝓘(Real, Real) y q) :=
    ⟨hyinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := dy.toLinearMap) (by simp)).mp hyinj⟩
  have hymap := Poincare.Geometry.Manifold.map_nhds_eq_of_contMDiffAt_bijective_mfderiv_modelSpaces
    (hy q) hybij
  obtain ⟨U, hUflat, hU, hqU⟩ := _root_.mem_nhds_iff.mp hflat
  let V := (γ '' Uᶜ)ᶜ
  have hV : IsOpen V := (hU.isClosed_compl.isCompact.image hγ.contMDiff.continuous).isClosed.isOpen_compl
  have hqV : γ q ∈ V := by
    rintro ⟨p, hp, he⟩
    exact hp (hγ.isEmbedding.injective he ▸ hqU)
  have hyU : y '' U ∈ 𝓝 (y q) := hymap ▸ image_mem_map (hU.mem_nhds hqU)
  have hnear : ∀ᶠ x in 𝓝 (γ q), L₁ x ∈ y '' U :=
    L₁.continuous.continuousAt.eventually hyU
  filter_upwards [hV.mem_nhds hqV, hnear] with x hxV hxU
  constructor
  · rintro ⟨p, rfl⟩
    apply hUflat
    by_contra hp
    exact hxV ⟨p, hp, rfl⟩
  · intro hx0
    obtain ⟨p, hp, hpx⟩ := hxU
    refine ⟨p, ?_⟩
    ext i
    fin_cases i
    · exact (hUflat hp).trans hx0.symm
    · exact hpx

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Matching
