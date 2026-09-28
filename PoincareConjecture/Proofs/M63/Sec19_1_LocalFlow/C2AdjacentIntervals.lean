import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2Locality
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessEmbeddedCurve
import PoincareConjecture.Proofs.M63.Mathlib.SmoothRetractionDifferentials
import PoincareConjecture.Proofs.M63.Mathlib.ClassicalPrimitive
import PoincareConjecture.Proofs.M63.Mathlib.ContinuousPartialDerivatives

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem c2_of_adjacent_closed_intervals
    (F : RicciFlow n M (Icc a b))
    {s T U : ℝ} (hsT : s < T) (hTU : T < U)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {O : Set W} (hO : IsOpen O) (heO : range e ⊆ O)
    {ρ : W → M} (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ O)
    (hρe : ∀ p, ρ (e p) = p)
    {c : ℝ → ℝ → M}
    (hleft : M63C2ShrinkingCurveOn F c (Icc s T))
    (hright : M63C2ShrinkingCurveOn F c (Icc T U)) :
    M63C2ShrinkingCurveOn F c (Icc s U) := by
  have hcover : (univ ×ˢ Icc s U : Set (ℝ × ℝ)) ⊆
      (univ ×ˢ Icc s T) ∪ (univ ×ˢ Icc T U) := by
    intro z hz
    by_cases ht : z.2 ≤ T
    · exact Or.inl ⟨mem_univ _, hz.2.1, ht⟩
    · exact Or.inr ⟨mem_univ _, (lt_of_not_ge ht).le, hz.2.2⟩
  have hvalue := (hleft.continuous.union_of_isClosed hright.continuous
    (isClosed_univ.prod isClosed_Icc) (isClosed_univ.prod isClosed_Icc)).mono hcover
  have hvelocity := (hleft.velocity_continuous.union_of_isClosed hright.velocity_continuous
    (isClosed_univ.prod isClosed_Icc) (isClosed_univ.prod isClosed_Icc)).mono hcover
  have hcurvature := (hleft.curvature_continuous.union_of_isClosed hright.curvature_continuous
    (isClosed_univ.prod isClosed_Icc) (isClosed_univ.prod isClosed_Icc)).mono hcover
  have hspatial (t : ℝ) (ht : t ∈ Icc s U) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun x => c x t) := by
    by_cases h : t ≤ T
    · exact hleft.spatial_regular t ⟨ht.1, h⟩
    · exact hright.spatial_regular t ⟨(lt_of_not_ge h).le, ht.2⟩
  let q : ℝ → ℝ → W := fun x t => e (c x t)
  let P : ℝ → ℝ → W := fun x t => deriv (fun y => q y t) x
  let H : ℝ → ℝ → W := fun x t =>
    mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x)
  have hdataL := c2ShrinkingCurve_embedded_closed_data hleft he
  have hdataR := c2ShrinkingCurve_embedded_closed_data hright he
  have hq : ContinuousOn (Function.uncurry q) (univ ×ˢ Icc s U) :=
    (hdataL.2.2.1.union_of_isClosed hdataR.2.2.1
      (isClosed_univ.prod isClosed_Icc) (isClosed_univ.prod isClosed_Icc)).mono hcover
  have hP : ContinuousOn (Function.uncurry P) (univ ×ˢ Icc s U) :=
    (hdataL.2.2.2.1.union_of_isClosed hdataR.2.2.2.1
      (isClosed_univ.prod isClosed_Icc) (isClosed_univ.prod isClosed_Icc)).mono hcover
  have hH : ContinuousOn (Function.uncurry H) (univ ×ˢ Icc s U) :=
    (hdataL.2.2.2.2.union_of_isClosed hdataR.2.2.2.2
      (isClosed_univ.prod isClosed_Icc) (isClosed_univ.prod isClosed_Icc)).mono hcover
  have hspace (x t : ℝ) (ht : t ∈ Icc s U) :
      HasDerivAt (fun y => q y t) (P x t) x := by
    have hq2 : ContDiff ℝ 2 (fun y => q y t) := by
      by_cases htT : t ≤ T
      · exact hdataL.1 t ⟨ht.1, htT⟩
      · exact hdataR.1 t ⟨(lt_of_not_ge htT).le, ht.2⟩
    exact (hq2.differentiable (by norm_num) x).hasDerivAt
  have htimeL := (c2ShrinkingCurve_embedded_interior_equation hleft he).2
  have htimeR := (c2ShrinkingCurve_embedded_interior_equation hright he).2
  have hqtime (x : ℝ) : ContinuousOn (q x) (Icc s U) :=
    hq.comp (s := Icc s U) (f := fun t : ℝ => (x, t))
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => ⟨mem_univ _, ht⟩)
  have hHtime (x : ℝ) : ContinuousOn (H x) (Icc s U) :=
    hH.comp (s := Icc s U) (f := fun t : ℝ => (x, t))
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => ⟨mem_univ _, ht⟩)
  have hprimitiveL (x t : ℝ) (ht : t ∈ Icc s T) :
      (∫ r in s..t, H x r) = q x t - q x s := by
    have hsub : Icc s t ⊆ Icc s U := Icc_subset_Icc_right (ht.2.trans hTU.le)
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      ((hqtime x).mono hsub) _
      (ContinuousOn.intervalIntegrable_of_Icc ht.1 ((hHtime x).mono hsub))
    intro r hr
    exact htimeL r (by rw [interior_Icc]; exact ⟨hr.1, hr.2.trans_le ht.2⟩) x
  have hprimitiveR (x t : ℝ) (ht : t ∈ Icc T U) :
      (∫ r in T..t, H x r) = q x t - q x T := by
    have hsub : Icc T t ⊆ Icc s U := Icc_subset_Icc hsT.le ht.2
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      ((hqtime x).mono hsub) _
      (ContinuousOn.intervalIntegrable_of_Icc ht.1 ((hHtime x).mono hsub))
    intro r hr
    exact htimeR r (by rw [interior_Icc]; exact ⟨hr.1, hr.2.trans_le ht.2⟩) x
  have hprimitive (x t : ℝ) (ht : t ∈ Icc s U) :
      q x t = q x s + ∫ r in s..t, H x r := by
    by_cases htT : t ≤ T
    · rw [hprimitiveL x t ⟨ht.1, htT⟩]
      abel
    have hTt : T ≤ t := (lt_of_not_ge htT).le
    have hl : IntervalIntegrable (H x) volume s T :=
      ContinuousOn.intervalIntegrable_of_Icc hsT.le
        ((hHtime x).mono (Icc_subset_Icc_right hTU.le))
    have hr : IntervalIntegrable (H x) volume T t :=
      ContinuousOn.intervalIntegrable_of_Icc hTt
        ((hHtime x).mono (Icc_subset_Icc hsT.le ht.2))
    rw [← intervalIntegral.integral_add_adjacent_intervals hl hr,
      hprimitiveL x T ⟨hsT.le, le_rfl⟩, hprimitiveR x t ⟨hTt, ht.2⟩]
    abel
  have htime (x t : ℝ) (ht : t ∈ Ioo s U) : HasDerivAt (q x) (H x t) t :=
    hasDerivAt_of_ae_continuous_primitive (hsT.trans hTU).le
      (ContinuousOn.intervalIntegrable_of_Icc (hsT.trans hTU).le (hHtime x))
      (hHtime x) (Filter.EventuallyEq.rfl) (hprimitive x) ht
  let D : Set (ℝ × ℝ) := univ ×ˢ Ioo s U
  have hD : IsOpen D := isOpen_univ.prod isOpen_Ioo
  let L : W →L[ℝ] (ℝ →L[ℝ] W) := ContinuousLinearMap.smulRightL ℝ ℝ W 1
  have hqjoint : ContDiffOn ℝ 1 (Function.uncurry q) D := by
    apply contDiffOn_one_uncurry_of_partials hD
      (f₁ := fun x t => L (P x t)) (f₂ := fun x t => L (H x t))
    · exact (L.continuous.comp_continuousOn hP).mono
        (prod_mono Subset.rfl Ioo_subset_Icc_self)
    · exact (L.continuous.comp_continuousOn hH).mono
        (prod_mono Subset.rfl Ioo_subset_Icc_self)
    · exact fun z hz => (hspace z.1 z.2 (Ioo_subset_Icc_self hz.2)).hasFDerivAt
    · exact fun z hz => (htime z.1 z.2 hz.2).hasFDerivAt
  have hcjoint : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) 1
      (fun z : ℝ × ℝ => c z.1 z.2) D :=
    ((hρ.of_le (by norm_num)).comp hqjoint.contMDiffOn
      (fun z _ => heO (mem_range_self (c z.1 z.2)))).congr
        (fun z _ => (hρe (c z.1 z.2)).symm)
  have hretract := (smooth_retraction_differentials he hO heO hρ hρe).2.2
  refine
    { domain_subset := ?_
      periodic := ?_
      spatial_regular := hspatial
      joint_c1 := by simpa only [interior_Icc] using hcjoint
      immersed := ?_
      continuous := hvalue
      velocity_continuous := hvelocity
      curvature_continuous := hcurvature
      equation := ?_ }
  · intro t ht
    by_cases h : t ≤ T
    · exact hleft.domain_subset ⟨ht.1, h⟩
    · exact hright.domain_subset ⟨(lt_of_not_ge h).le, ht.2⟩
  · intro t ht
    by_cases h : t ≤ T
    · exact hleft.periodic t ⟨ht.1, h⟩
    · exact hright.periodic t ⟨(lt_of_not_ge h).le, ht.2⟩
  · intro t ht
    by_cases h : t ≤ T
    · exact hleft.immersed t ⟨ht.1, h⟩
    · exact hright.immersed t ⟨(lt_of_not_ge h).le, ht.2⟩
  · intro t ht x
    have ht' : t ∈ Ioo s U := by simpa only [interior_Icc] using ht
    have hd := htime x t ht'
    have hchain := mfderiv_comp t
      ((hρ.contMDiffAt (hO.mem_nhds (heO (mem_range_self (c x t))))).mdifferentiableAt
        (by simp)) hd.differentiableAt.mdifferentiableAt
    have hv := congrArg (fun A : ℝ →L[ℝ] TangentSpace (𝓡 n) (ρ (q x t)) => A 1) hchain
    rw [mfderiv_eq_fderiv, hd.hasFDerivAt.fderiv] at hv
    have heq : (fun r => ρ (q x r)) = (fun r => c x r) :=
      funext (fun r => hρe (c x r))
    change curveVelocity (fun r => ρ (q x r)) t =
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q x t) ((1 : ℝ) • H x t) at hv
    have hv' : curveVelocity (fun r => ρ (q x r)) t =
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q x t) (H x t) := by
      simpa only [one_smul] using! hv
    rw [heq] at hv'
    exact hv'.trans (hretract (c x t) (m62CurvatureVector F c t x))

end PoincareConjecture.M63
