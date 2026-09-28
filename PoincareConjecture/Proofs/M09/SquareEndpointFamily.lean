import PoincareConjecture.Proofs.M09.EndpointFamily
import PoincareConjecture.Proofs.M09.FamilySlices
import PoincareConjecture.Proofs.M09.FamilyEndpointEquation

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem lExponentialFamily_exists_square_endpoint_family {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax : ℝ} {p : M} (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    let e := chartAt E (A.gamma Z b)
    ∃ (f : E × ℝ → M) (U : Set (E × ℝ)) (V : Set E),
      IsOpen U ∧ IsOpen V ∧ e (A.gamma Z b) ∈ V ∧ V ⊆ e.target ∧
      V ×ˢ Set.Icc 0 (Real.sqrt b) ⊆ U ∧
      ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f U ∧
      (∀ y, f (y, 0) = p) ∧ (∀ y, f (y, Real.sqrt b) = e.symm y) ∧
      ∀ s ∈ Set.Icc 0 (Real.sqrt b), f (e (A.gamma Z b), s) = A.squareFamily Z s := by
  let H := Real.sqrt b
  have hH : 0 < H := Real.sqrt_pos.mpr hb
  let D := (fun r : ℝ ↦ (Z, H * r)) ⁻¹' A.squareDomain
  let γ : ℝ → M := fun r ↦ A.squareFamily Z (H * r)
  have hi : ContDiff ℝ ∞ (fun r : ℝ ↦ H * r) := contDiff_const.mul contDiff_id
  have hD : IsOpen D := A.square_open.preimage (continuous_const.prodMk hi.continuous)
  have hI : Set.Icc (0 : ℝ) 1 ⊆ D := by
    intro r hr
    exact A.square_contains ⟨Set.mem_univ _, mul_nonneg hH.le hr.1,
      (mul_le_of_le_one_right hH.le hr.2).trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  have hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ D :=
    (lExponentialFamily_squareSlice_contMDiffOn A Z).comp hi.contMDiff.contMDiffOn
      (fun r hr ↦ hr)
  have hγ0 : γ 0 = p := by simp only [γ, mul_zero, A.square_at_zero]
  have hγ1 : γ 1 = A.gamma Z b := by
    dsimp only [γ]
    rw [mul_one, A.square_agrees Z H ⟨hH.le, Real.sqrt_lt_sqrt hb.le hmax⟩]
    rw [Real.sq_sqrt hb.le]
  obtain ⟨f, U, V, hU, hV, hyV, hVe, hVU, hf, hstart, hend, hcenter⟩ :=
    exists_smooth_endpoint_family γ D hD hI hγ
  rw [hγ0] at hstart
  rw [hγ1] at hyV hVe hend hcenter
  let k : E × ℝ → E × ℝ := fun z ↦ (z.1, z.2 / H)
  have hk : ContDiff ℝ ∞ k := contDiff_fst.prodMk (contDiff_snd.div_const _)
  refine ⟨f ∘ k, k ⁻¹' U, V, hU.preimage hk.continuous, hV, hyV, hVe, ?_,
    hf.comp hk.contMDiff.contMDiffOn (fun z hz ↦ hz), ?_, ?_, ?_⟩
  · intro z hz
    exact hVU ⟨hz.1, div_nonneg hz.2.1 hH.le, (div_le_one hH).mpr hz.2.2⟩
  · intro y
    simpa only [Function.comp_apply, k, zero_div] using hstart y
  · intro y
    change f (y, H / H) = _
    simpa only [div_self hH.ne'] using hend y
  · intro s hs
    have hr : s / H ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hs.1 hH.le, (div_le_one hH).mpr hs.2⟩
    simpa only [Function.comp_apply, k, γ, mul_div_cancel₀ _ hH.ne'] using hcenter (s / H) hr

end PoincareConjecture.Proofs.M09
