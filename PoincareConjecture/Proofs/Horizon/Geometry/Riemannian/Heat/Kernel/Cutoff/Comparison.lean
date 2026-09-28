import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.Supports
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.NoncompactMaximum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem cutoff_sub_le_heat_of_lower_supports
    (D : LeviCivitaData g) {Ω : Set M} (hΩ : IsOpen Ω)
    {η : M → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) {B b : ℝ} (hB : 0 ≤ B)
    (hsupport : ∀ x, 0 < η x → ∃ (U : Set M) (σ : M → ℝ),
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ U ∧
      σ x = η x ∧ (∀ y ∈ U, σ y ≤ η y) ∧ -B ≤ D.laplacian σ x)
    {F F' : M → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry F) (univ ×ˢ Icc 0 b))
    (hspace : ∀ t ∈ Ioc 0 b, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => F x t) Ω)
    (hderiv : ∀ x t, t ∈ Ioc 0 b → HasDerivAt (F x) (F' x t) t)
    (hheat : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 b, D.laplacian (fun y => F y t) x ≤ F' x t)
    (hnonneg : ∀ x t, t ∈ Icc 0 b → 0 ≤ F x t)
    (hinit : ∀ x, η x ≤ F x 0) :
    ∀ x t, t ∈ Icc 0 b → η x - B * t ≤ F x t := by
  let G := fun x t => η x - B * t - F x t
  let G' := fun x t => -B - F' x t
  have hc : ContinuousOn (Function.uncurry G) (univ ×ˢ Icc 0 b) :=
    (((hη.comp continuous_fst).continuousOn.sub
      (continuousOn_const.mul continuous_snd.continuousOn)).sub hcont)
  have hd (x : M) (t : ℝ) (ht : t ∈ Ioc 0 b) :
      HasDerivWithinAt (G x) (G' x t) (Icc 0 b) t := by
    have h := ((hasDerivAt_const t (η x)).sub
      ((hasDerivAt_id t).const_mul B)).sub (hderiv x t ht)
    convert! h.hasDerivWithinAt (s := Icc 0 b) using 1
    simp [G']
  have hmax (x : M) (t : ℝ) (ht : t ∈ Ioc 0 b) (hpos : 0 < G x t)
      (hm : ∀ y, G y t ≤ G x t) : G' x t ≤ 0 * G x t := by
    have hηpos : 0 < η x := by
      have hu := hnonneg x t ⟨ht.1.le, ht.2⟩
      have hBt := mul_nonneg hB ht.1.le
      dsimp [G] at hpos
      linarith
    have hxΩ : x ∈ Ω := hηΩ (subset_tsupport η (ne_of_gt hηpos))
    obtain ⟨U, σ, hU, hxU, hσ, hση, hσle, hlap⟩ := hsupport x hηpos
    obtain ⟨χ, hχ, hχσ⟩ := Poincare.Manifold.exists_contMDiff_eq_near hU hσ hxU
    obtain ⟨ψ, hψ, hψF⟩ :=
      Poincare.Manifold.exists_contMDiff_eq_near hΩ (hspace t ht) hxΩ
    have hm' : IsLocalMax (fun z => χ z - ψ z) x := by
      filter_upwards [hχσ, hψF, hU.mem_nhds hxU] with z hzχ hzψ hzU
      change χ z - ψ z ≤ χ x - ψ x
      rw [hzχ, hzψ, hχσ.self_of_nhds, hψF.self_of_nhds, hση]
      have h := hm z
      dsimp [G] at h
      linarith [hσle z hzU]
    have hl := D.laplacian_nonpos_of_isLocalMax (hχ.sub hψ) hm'
    rw [D.laplacian_sub hχ hψ,
      D.laplacian_eq_of_eventuallyEq hχσ,
      D.laplacian_eq_of_eventuallyEq hψF] at hl
    have hh := hheat x hxΩ t ht
    dsimp [G']
    simp only [zero_mul]
    linarith
  have hcompare := Poincare.Parabolic.nonpos_of_deriv_le_mul_at_max_of_nonpos_outside_compact
    hηc hc hd hmax
    (fun x => by simpa [G] using sub_nonpos.mpr (hinit x))
    (fun x hx t ht => by
      dsimp [G]
      rw [image_eq_zero_of_notMem_tsupport hx]
      have h := hnonneg x t ht
      have hBt := mul_nonneg hB ht.1
      linarith)
  intro x t ht
  exact sub_nonpos.mp (hcompare x t ht)

end PoincareConjecture.LeviCivitaData
