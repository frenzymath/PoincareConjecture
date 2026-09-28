import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Topology.UniformSpace.UniformConvergence











set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology Pointwise

variable {𝕜 T E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup T] [NormedSpace 𝕜 T]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]



theorem iteratedFDeriv_spatial_slice_eq_within
    {J : Set T} {U : Set E} {f : T × E → F} {n : ℕ∞ω}
    (hJ : UniqueDiffOn 𝕜 J) (hU : IsOpen U)
    (hf : ContDiffOn 𝕜 n f (J ×ˢ U))
    {t : T} (ht : t ∈ J) {x : E} (hx : x ∈ U)
    {r : ℕ} (hr : r ≤ n) :
    iteratedFDeriv 𝕜 r (fun y => f (t, y)) x =
      (iteratedFDerivWithin 𝕜 r f (J ×ˢ U) (t, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr 𝕜 T E) := by
  let a : T × E := (t, 0)
  let ι : E →L[𝕜] T × E := ContinuousLinearMap.inr 𝕜 T E
  let S : Set (T × E) := (fun z => a + z) ⁻¹' (J ×ˢ U)
  have hSimage : S = (fun z => -a + z) '' (J ×ˢ U) := by
    ext z
    constructor
    · intro hz
      exact ⟨a + z, hz, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [S] using hy
  have hS : UniqueDiffOn 𝕜 S := by
    rw [hSimage]
    exact (hJ.prod hU.uniqueDiffOn).image
      (fun z _ => ((hasFDerivAt_id (𝕜 := 𝕜) z).const_add (-a)).hasFDerivWithinAt)
      (fun _ _ => Function.surjective_id.denseRange)
  have hshift : ContDiffOn 𝕜 n (fun z : T × E => f (a + z)) S :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hz => hz)
  have hpre : ι ⁻¹' S = U := by
    ext y
    simp [S, a, ι, ht]
  have hmem : ι x ∈ S := by
    simpa [S, a, ι, ht] using hx
  have htranslate : a +ᵥ S = J ×ˢ U := by
    ext y
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp [S]
  have hcomp := ι.iteratedFDerivWithin_comp_right hshift hS
    (hpre.symm ▸ hU.uniqueDiffOn) hmem hr
  rw [hpre, iteratedFDerivWithin_of_isOpen _ hU hx,
    iteratedFDerivWithin_comp_add_left, htranslate] at hcomp
  simpa [a, ι, Function.comp_def] using hcomp



theorem TendstoUniformlyOn.iteratedFDeriv_spatial_slice
    {α : Type*} {l : Filter α} {J : Set T} {U : Set E} {K : Set (T × E)}
    {f : α → T × E → F} {g : T × E → F} {n : ℕ∞ω} {r : ℕ}
    (hjet : TendstoUniformlyOn
      (fun k => iteratedFDerivWithin 𝕜 r (f k) (J ×ˢ U))
      (iteratedFDerivWithin 𝕜 r g (J ×ˢ U)) l K)
    (hJ : UniqueDiffOn 𝕜 J) (hU : IsOpen U) (hK : K ⊆ J ×ˢ U)
    (hf : ∀ᶠ k in l, ContDiffOn 𝕜 n (f k) (J ×ˢ U))
    (hg : ContDiffOn 𝕜 n g (J ×ˢ U)) (hr : r ≤ n) :
    TendstoUniformlyOn
      (fun k p => iteratedFDeriv 𝕜 r (fun y => f k (p.1, y)) p.2)
      (fun p => iteratedFDeriv 𝕜 r (fun y => g (p.1, y)) p.2) l K := by
  let R := ContinuousMultilinearMap.compContinuousLinearMapL
    (F := F) (fun _ : Fin r => ContinuousLinearMap.inr 𝕜 T E)
  have h := R.uniformContinuous.comp_tendstoUniformlyOn hjet
  apply (h.congr ?_).congr_right ?_
  · filter_upwards [hf] with k hk p hp
    exact (iteratedFDeriv_spatial_slice_eq_within hJ hU hk
      (hK hp).1 (hK hp).2 hr).symm
  · intro p hp
    exact (iteratedFDeriv_spatial_slice_eq_within hJ hU hg
      (hK hp).1 (hK hp).2 hr).symm
