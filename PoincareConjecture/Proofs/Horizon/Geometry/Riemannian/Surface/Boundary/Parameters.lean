import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.Chart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.Reparametrization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology Interval

namespace PoincareConjecture.LeviCivitaData

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

private theorem exists_edge_coordinate {v : ℝ × ℝ} (hv : v ≠ 0) :
    ∃ L : (ℝ × ℝ) →L[ℝ] ℝ, L v = 1 := by
  by_cases h₁ : v.1 = 0
  · have h₂ : v.2 ≠ 0 := by
      intro h₂
      exact hv (Prod.ext h₁ h₂)
    refine ⟨v.2⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ, ?_⟩
    simp [h₂]
  · refine ⟨v.1⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ, ?_⟩
    simp [h₁]

omit [IsManifold (𝓡 2) ∞ S] in

theorem exists_smooth_chart_edge_parameter
    (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (p v : ℝ × ℝ) (hv : v ≠ 0) {I J : Set ℝ}
    (htarget : ∀ s ∈ J, p + s • v ∈ e.target)
    {η : ℝ → S} (hη : ∀ t ∈ I, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ η t)
    (himage : MapsTo η I ((fun s : ℝ => e.symm (p + s • v)) '' J)) :
    ∃ φ : ℝ → ℝ, (∀ t ∈ I, ContDiffAt ℝ ∞ φ t) ∧ MapsTo φ I J ∧
      (∀ t ∈ I, η t = e.symm (p + φ t • v)) ∧
      (∀ t ∈ I, ∀ s ∈ J, η t = e.symm (p + s • v) → φ t = s) := by
  obtain ⟨L, hL⟩ := exists_edge_coordinate hv
  let φ := fun t => L (e (η t) - p)
  have hrecover (t : ℝ) (s : ℝ) (hs : s ∈ J)
      (ht : η t = e.symm (p + s • v)) : φ t = s := by
    dsimp only [φ]
    rw [ht, e.right_inv (htarget s hs), add_sub_cancel_left, map_smul, hL, smul_eq_mul,
      mul_one]
  have hsource (t : ℝ) (ht : t ∈ I) : η t ∈ e.source := by
    obtain ⟨s, hs, hst⟩ := himage ht
    rw [← hst]
    exact e.map_target (htarget s hs)
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have hc : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (e ∘ η) t :=
      (he.contMDiffAt (e.open_source.mem_nhds (hsource t ht))).comp t (hη t ht)
    have hlin : ContDiff ℝ ∞ (fun z : ℝ × ℝ => L (z - p)) :=
      L.contDiff.comp (contDiff_id.sub contDiff_const)
    exact contMDiffAt_iff_contDiffAt.mp (hlin.contDiffAt.comp_contMDiffAt hc)
  · intro t ht
    obtain ⟨s, hs, hst⟩ := himage ht
    rw [hrecover t s hs hst.symm]
    exact hs
  · intro t ht
    obtain ⟨s, hs, hst⟩ := himage ht
    rw [hrecover t s hs hst.symm]
    exact hst.symm
  · intro t _ s hs ht
    exact hrecover t s hs ht

omit [IsManifold (𝓡 2) ∞ S] in

theorem deriv_reparam_ne_zero {γ η : ℝ → S} {φ : ℝ → ℝ} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ (φ t))
    (hφ : DifferentiableAt ℝ φ t)
    (heq : η =ᶠ[𝓝 t] γ ∘ φ)
    (hregular : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) η t 1 ≠ 0) :
    deriv φ t ≠ 0 := by
  intro hzero
  have hd : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) η t =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ ∘ φ) t := heq.mfderiv_eq
  have hv := congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) => L 1) hd
  have hchain := mfderiv_curve_reparam hγ hφ.hasDerivAt
  rw [hzero, zero_smul] at hchain
  exact hregular (hv.trans hchain)

omit [IsManifold (𝓡 2) ∞ S] in

theorem exists_smooth_chart_edge_reparam_of_image_eq
    (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    (p v : ℝ × ℝ) (hv : v ≠ 0) {a b c d : ℝ} (hab : a ≤ b)
    (htarget : ∀ s ∈ Icc c d, p + s • v ∈ e.target)
    {η : ℝ → S} (hη : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ η t)
    (hinj : InjOn η (Icc a b))
    (hregular : ∀ t ∈ Ioo a b, mfderiv 𝓘(ℝ, ℝ) (𝓡 2) η t 1 ≠ 0)
    (himage : η '' Icc a b = (fun s : ℝ => e.symm (p + s • v)) '' Icc c d) :
    ∃ φ : ℝ → ℝ, (∀ t ∈ Icc a b, ContDiffAt ℝ ∞ φ t) ∧
      BijOn φ (Icc a b) (Icc c d) ∧
      (∀ t ∈ Icc a b, η t = e.symm (p + φ t • v)) ∧
      (∀ t ∈ Ioo a b, deriv φ t ≠ 0) ∧
      ((φ a = c ∧ φ b = d) ∨ (φ a = d ∧ φ b = c)) := by
  obtain ⟨φ, hφ, hmaps, heq, huniq⟩ := exists_smooth_chart_edge_parameter
    e he p v hv htarget hη (fun t ht => himage ▸ mem_image_of_mem η ht)
  have hφinj : InjOn φ (Icc a b) := by
    intro s hs t ht hst
    apply hinj hs ht
    rw [heq s hs, heq t ht, hst]
  have hφsurj : SurjOn φ (Icc a b) (Icc c d) := by
    intro s hs
    have hmem := mem_image_of_mem (fun r : ℝ => e.symm (p + r • v)) hs
    rw [← himage] at hmem
    obtain ⟨t, ht, hts⟩ := hmem
    exact ⟨t, ht, huniq t ht s hs hts⟩
  have hbij : BijOn φ (Icc a b) (Icc c d) := ⟨hmaps, hφinj, hφsurj⟩
  have hcont : ContinuousOn φ (Icc a b) :=
    fun t ht => (hφ t ht).continuousAt.continuousWithinAt
  refine ⟨φ, hφ, hbij, heq, ?_, ?_⟩
  · intro t ht
    have ht' := Ioo_subset_Icc_self ht
    have hγ := (mfderiv_chart_line e he hei p v (htarget _ (hmaps ht'))).1
    apply deriv_reparam_ne_zero (hγ.mdifferentiableAt (by simp))
      ((hφ t ht').differentiableAt (by simp)) _ (hregular t ht)
    exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht)
      (fun s hs => heq s (Ioo_subset_Icc_self hs))
  · rcases hcont.strictMonoOn_of_injOn_Icc' hab hφinj with hmono | hanti
    · left
      have h := (hcont.image_Icc_of_monotoneOn hab hmono.monotoneOn).symm.trans hbij.image_eq
      exact (Icc_eq_Icc_iff (hmono.monotoneOn (left_mem_Icc.mpr hab)
        (right_mem_Icc.mpr hab) hab)).mp h
    · right
      have h := (hcont.image_Icc_of_antitoneOn hab hanti.antitoneOn).symm.trans hbij.image_eq
      have hends := (Icc_eq_Icc_iff (hanti.antitoneOn (left_mem_Icc.mpr hab)
        (right_mem_Icc.mpr hab) hab)).mp h
      exact ⟨hends.2, hends.1⟩

end PoincareConjecture.LeviCivitaData
