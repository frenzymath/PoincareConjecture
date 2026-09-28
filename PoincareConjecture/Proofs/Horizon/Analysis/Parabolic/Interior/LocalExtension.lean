import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Localization

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open Filter Set
open scoped ContDiff Topology

namespace Poincare.Parabolic.Interior

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_contDiff_compact_cutoff [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      ∀ x ∈ K, χ =ᶠ[𝓝 x] fun _ => 1 := by
  obtain ⟨W, hWo, hKW, hWc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨V, hVo, hKV, hVU⟩ := hK.exists_isOpen_closure_subset
    ((hU.inter hWo).mem_nhdsSet.mpr (subset_inter hKU hKW))
  have hVc : IsCompact (closure V) := hWc.of_isClosed_subset isClosed_closure
    (fun x hx => subset_closure (hVU hx).2)
  obtain ⟨O, hOo, hKO, hOV⟩ := hK.exists_isOpen_closure_subset
    (hVo.mem_nhdsSet.mpr hKV)
  obtain ⟨u, huSupp, hu, huRange⟩ := hVo.exists_contDiff_support_eq (n := ⊤)
  obtain ⟨v, hvSupp, hv, hvRange⟩ :=
    isClosed_closure.isOpen_compl.exists_contDiff_support_eq (n := ⊤) (s := (closure O)ᶜ)
  have hu0 (x : E) : 0 ≤ u x := (huRange (mem_range_self x)).1
  have hv0 (x : E) : 0 ≤ v x := (hvRange (mem_range_self x)).1
  have hpos (x : E) : 0 < u x + v x := by
    by_cases hx : x ∈ V
    · have hx' : u x ≠ 0 := by rwa [← Function.mem_support, huSupp]
      exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hu0 x) hx'.symm) (hv0 x)
    · have hx' : v x ≠ 0 := by
        rw [← Function.mem_support, hvSupp]
        exact fun h => hx (hOV h)
      exact add_pos_of_nonneg_of_pos (hu0 x) (lt_of_le_of_ne (hv0 x) hx'.symm)
  let χ : E → ℝ := fun x => u x / (u x + v x)
  have hsupp : tsupport χ ⊆ closure V := by
    apply closure_mono
    intro x hx
    by_contra hxV
    have huX : u x = 0 := by
      have : x ∉ Function.support u := by rwa [huSupp]
      exact Function.notMem_support.mp this
    exact hx (by simp [χ, huX])
  refine ⟨χ, hu.div (hu.add hv) (fun x => (hpos x).ne'),
    hVc.of_isClosed_subset isClosed_closure hsupp,
    hsupp.trans (fun x hx => (hVU hx).1), ?_⟩
  intro x hx
  filter_upwards [hOo.mem_nhds (hKO hx)] with y hy
  have hvY : v y = 0 := by
    apply Function.notMem_support.mp
    rw [hvSupp]
    exact not_not.mpr (subset_closure hy)
  have huY : u y ≠ 0 := by
    rw [← Function.mem_support, huSupp]
    exact hOV (subset_closure hy)
  simp [χ, hvY, huY]

theorem exists_compact_smooth_extension [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨χ, hχ, hχc, hχU, hχK⟩ := exists_contDiff_compact_cutoff hK hU hKU
  exact ⟨fun x => χ x • f x, contDiff_smul_cutoff hU hf hχ hχU,
    hasCompactSupport_smul_cutoff hχc f, fun x hx => smul_cutoff_eventuallyEq (hχK x hx) f⟩

theorem timeDerivative_eq_of_eventuallyEq {f g : E × ℝ → F} {p : E × ℝ}
    (h : f =ᶠ[𝓝 p] g) : timeDerivative f p = timeDerivative g p := by
  exact congrArg (fun L : E × ℝ →L[ℝ] F => L (0, 1)) (h.fderiv_eq (𝕜 := ℝ))

theorem spatialDerivative_eventuallyEq_of_eventuallyEq
    {f g : E × ℝ → F} {p : E × ℝ} (h : f =ᶠ[𝓝 p] g) :
    spatialDerivative f =ᶠ[𝓝 p] spatialDerivative g := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with q hq
  exact congrArg (fun L : E × ℝ →L[ℝ] F => L.comp (ContinuousLinearMap.inl ℝ E ℝ)) hq

theorem spatialDerivative_eq_of_eventuallyEq {f g : E × ℝ → F} {p : E × ℝ}
    (h : f =ᶠ[𝓝 p] g) : spatialDerivative f p = spatialDerivative g p :=
  (spatialDerivative_eventuallyEq_of_eventuallyEq h).eq_of_nhds

theorem spatialDerivative_spatialDerivative_eq_of_eventuallyEq
    {f g : E × ℝ → F} {p : E × ℝ} (h : f =ᶠ[𝓝 p] g) :
    spatialDerivative (spatialDerivative f) p = spatialDerivative (spatialDerivative g) p :=
  spatialDerivative_eq_of_eventuallyEq (spatialDerivative_eventuallyEq_of_eventuallyEq h)

theorem exists_compact_smooth_extension_with_jets [FiniteDimensional ℝ E]
    {K U : Set (E × ℝ)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : E × ℝ → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : E × ℝ → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∀ p ∈ K, g =ᶠ[𝓝 p] f ∧ g p = f p ∧
        timeDerivative g p = timeDerivative f p ∧
        spatialDerivative g p = spatialDerivative f p ∧
        spatialDerivative (spatialDerivative g) p =
          spatialDerivative (spatialDerivative f) p := by
  obtain ⟨g, hg, hgc, hgf⟩ := exists_compact_smooth_extension hK hU hKU hf
  refine ⟨g, hg, hgc, fun p hp => ?_⟩
  have h := hgf p hp
  exact ⟨h, h.eq_of_nhds, timeDerivative_eq_of_eventuallyEq h,
    spatialDerivative_eq_of_eventuallyEq h,
    spatialDerivative_spatialDerivative_eq_of_eventuallyEq h⟩

end Poincare.Parabolic.Interior
