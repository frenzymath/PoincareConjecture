import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.ImplicitFunction.Quadrants
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace Poincare.Topology.Plane.Curves

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem exists_two_height_tube {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    {W : Set ((ℝ × ℝ) × (ℝ × ℝ))} (hW : IsOpen W)
    (haxis : ∀ q ∈ K, (q, (0 : ℝ × ℝ)) ∈ W) :
    ∃ δ > 0, ∀ q ∈ K, ∀ z w : ℝ, |z| < δ → |w| < δ → (q, (z, w)) ∈ W := by
  have hsub : K ×ˢ {(0 : ℝ × ℝ)} ⊆ W := by
    rintro ⟨q, v⟩ ⟨hq, hv⟩
    have hv0 : v = 0 := hv
    subst v
    exact haxis q hq
  obtain ⟨U, V, _, hV, hKU, h0V, hUV⟩ :=
    generalized_tube_lemma hK isCompact_singleton hW hsub
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hV.mem_nhds (h0V (mem_singleton (0 : ℝ × ℝ))))
  refine ⟨δ, hδ, fun q hq z w hz hw => hUV ⟨hKU hq, hball ?_⟩⟩
  simpa only [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_lt_iff]
    using And.intro hz hw

private theorem scalar_first_derivative
    {K : ℝ × ℝ → E} {p : E} (hK : DifferentiableAt ℝ K 0)
    (ℓ : E →L[ℝ] ℝ) :
    fderiv ℝ (fun q => ℓ (K q - p)) 0 (1, 0) = ℓ (fderiv ℝ K 0 (1, 0)) := by
  have hd := ℓ.hasFDerivAt.comp 0 (hK.hasFDerivAt.sub_const p)
  change fderiv ℝ (ℓ ∘ fun q => K q - p) 0 (1, 0) = _
  rw [hd.fderiv]
  rfl

theorem exists_adjacent_strip_separation
    (F G : OpenPartialHomeomorph (ℝ × ℝ) E)
    (hF : ContDiffOn ℝ 1 F F.source) (hG : ContDiffOn ℝ 1 G G.source)
    (hFs : ∀ t ∈ Icc (0 : ℝ) 1, (t, (0 : ℝ)) ∈ F.source)
    (hGs : ∀ t ∈ Icc (0 : ℝ) 1, (t, (0 : ℝ)) ∈ G.source)
    (hcommon : F (1, 0) = G (0, 0))
    (hbase : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      F (t, 0) = G (s, 0) → t = 1 ∧ s = 0)
    (ℓ : E →L[ℝ] ℝ)
    (hFt : 0 < ℓ (fderiv ℝ F (1, 0) (1, 0)))
    (hGt : 0 < ℓ (fderiv ℝ G (0, 0) (1, 0)))
    (hFline : ∀ᶠ z in 𝓝 (0 : ℝ), ℓ (F (1, z) - F (1, 0)) = 0)
    (hGline : ∀ᶠ z in 𝓝 (0 : ℝ), ℓ (G (0, z) - G (0, 0)) = 0) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ z w : ℝ, |z| < δ → |w| < δ →
        (t, z) ∈ F.source ∧ (s, w) ∈ G.source ∧
          (F (t, z) = G (s, w) → t = 1 ∧ s = 0) := by
  have hF1 := hFs 1 (by simp)
  have hG0 := hGs 0 (by simp)
  have hFat : ContDiffAt ℝ 1 F (1, 0) :=
    (hF _ hF1).contDiffAt (F.open_source.mem_nhds hF1)
  have hGat : ContDiffAt ℝ 1 G (0, 0) :=
    (hG _ hG0).contDiffAt (G.open_source.mem_nhds hG0)
  let R : ℝ × ℝ → ℝ × ℝ := fun q => (1 - q.1, q.2)
  let f : ℝ × ℝ → ℝ := fun q => -ℓ (F (R q) - F (1, 0))
  let g : ℝ × ℝ → ℝ := fun q => ℓ (G q - G (0, 0))
  have hR : ContDiffAt ℝ 1 R 0 :=
    (contDiffAt_const.sub contDiffAt_fst).prodMk contDiffAt_snd
  have hFat' : ContDiffAt ℝ 1 F (R 0) := by
    simpa only [R, Prod.fst_zero, Prod.snd_zero, sub_zero] using hFat
  have hf : ContDiffAt ℝ 1 f 0 :=
    (ℓ.contDiff.contDiffAt.comp 0 ((hFat'.comp (f := R) 0 hR).sub contDiffAt_const)).neg
  have hg : ContDiffAt ℝ 1 g 0 := ℓ.contDiff.contDiffAt.comp 0
    (hGat.sub contDiffAt_const)
  have hRpath : HasDerivAt (fun r : ℝ => (1 - r, (0 : ℝ))) ((-1 : ℝ), (0 : ℝ)) 0 := by
    simpa only [zero_sub, Pi.sub_apply, id_eq] using
      ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ))).prodMk
        (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have hdF : HasFDerivAt F (fderiv ℝ F (1, 0)) (1 - (0 : ℝ), (0 : ℝ)) := by
    simpa only [sub_zero] using hFat.differentiableAt_one.hasFDerivAt
  have hFtrace := hdF.comp_hasDerivAt
    (f := fun r : ℝ => (1 - r, (0 : ℝ))) 0 hRpath
  have hscalar := (ℓ.hasFDerivAt.comp_hasDerivAt 0 (hFtrace.sub_const (F (1, 0)))).neg
  have hfd : HasDerivAt (fun r : ℝ => f (r, 0)) (ℓ (fderiv ℝ F (1, 0) (1, 0))) 0 := by
    convert! hscalar using 1
    have he : ((-1 : ℝ), (0 : ℝ)) = -((1 : ℝ), (0 : ℝ)) := by simp
    rw [he, map_neg, map_neg, neg_neg]
  have hpath : HasDerivAt (fun r : ℝ => (r, (0 : ℝ))) ((1 : ℝ), (0 : ℝ)) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have hfp : HasDerivAt (fun r : ℝ => f (r, 0)) (fderiv ℝ f 0 (1, 0)) 0 :=
    hf.differentiableAt_one.hasFDerivAt.comp_hasDerivAt
      (f := fun r : ℝ => (r, (0 : ℝ))) 0 hpath
  have hdf : 0 < fderiv ℝ f 0 (1, 0) := by
    rw [← hfd.unique hfp]
    exact hFt
  have hdg : 0 < fderiv ℝ g 0 (1, 0) := by
    rw [scalar_first_derivative hGat.differentiableAt_one ℓ]
    exact hGt
  have hfzero : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), q.1 = 0 → f q = 0 := by
    filter_upwards [continuousAt_snd.tendsto.eventually hFline] with q hq hq0
    simp only [f, R, hq0, sub_zero, hq, neg_zero]
  have hgzero : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), q.1 = 0 → g q = 0 := by
    filter_upwards [continuousAt_snd.tendsto.eventually hGline] with q hq hq0
    simpa only [g, ← hq0, Prod.eta] using hq
  obtain ⟨α, hα, hsignF⟩ := Poincare.Analysis.exists_first_coordinate_sign_radius hf hdf hfzero
  obtain ⟨β, hβ, hsignG⟩ := Poincare.Analysis.exists_first_coordinate_sign_radius hg hdg hgzero
  let η := min α β / 2
  have hη : 0 < η := half_pos (lt_min hα hβ)
  have hηα : η < α := (half_lt_self (lt_min hα hβ)).trans_le (min_le_left _ _)
  have hηβ : η < β := (half_lt_self (lt_min hα hβ)).trans_le (min_le_right _ _)
  let D : Set (ℝ × ℝ) :=
    (Icc (0 : ℝ) (1 - η) ×ˢ Icc (0 : ℝ) 1) ∪ (Icc (0 : ℝ) 1 ×ˢ Icc η 1)
  have hD : IsCompact D := (isCompact_Icc.prod isCompact_Icc).union
    (isCompact_Icc.prod isCompact_Icc)
  let U : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
    {q | (q.1.1, q.2.1) ∈ F.source ∧ (q.1.2, q.2.2) ∈ G.source}
  have hU : IsOpen U :=
    (F.open_source.preimage (by fun_prop)).inter (G.open_source.preimage (by fun_prop))
  have hFc : ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) => F (q.1.1, q.2.1)) U :=
    F.continuousOn.comp (by fun_prop) (fun _ hq => hq.1)
  have hGc : ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) => G (q.1.2, q.2.2)) U :=
    G.continuousOn.comp (by fun_prop) (fun _ hq => hq.2)
  let W : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
    U ∩ (fun q => F (q.1.1, q.2.1) - G (q.1.2, q.2.2)) ⁻¹' ({0} : Set E)ᶜ
  have hW : IsOpen W := (hFc.sub hGc).isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hDaxis : ∀ q ∈ D, (q, (0 : ℝ × ℝ)) ∈ W := by
    intro q hq
    have hq01 : q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ Icc (0 : ℝ) 1 := by
      rcases hq with hq | hq
      · exact ⟨⟨hq.1.1, by linarith [hq.1.2]⟩, hq.2⟩
      · exact ⟨hq.1, ⟨hη.le.trans hq.2.1, hq.2.2⟩⟩
    refine ⟨⟨hFs _ hq01.1, hGs _ hq01.2⟩, ?_⟩
    change F (q.1, 0) - G (q.2, 0) ≠ 0
    intro heq
    obtain ⟨ht, hs⟩ := hbase _ hq01.1 _ hq01.2 (sub_eq_zero.mp heq)
    rcases hq with hq | hq
    · linarith [hq.1.2]
    · linarith [hq.2.1]
  obtain ⟨δd, hδd, hdistant⟩ := exists_two_height_tube hD hW hDaxis
  obtain ⟨δs, hδs, hsource⟩ := exists_two_height_tube
    (isCompact_Icc.prod isCompact_Icc) hU (fun q hq => ⟨hFs _ hq.1, hGs _ hq.2⟩)
  let δ := min δs (min δd (min α β))
  have hδ : 0 < δ := lt_min hδs (lt_min hδd (lt_min hα hβ))
  have hδs' : δ ≤ δs := min_le_left _ _
  have hδd' : δ ≤ δd := (min_le_right _ _).trans (min_le_left _ _)
  have hδα : δ ≤ α := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδβ : δ ≤ β := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ, hδ, fun t ht s hs z w hz hw => ?_⟩
  have hsrc := hsource (t, s) ⟨ht, hs⟩ z w (hz.trans_le hδs') (hw.trans_le hδs')
  refine ⟨hsrc.1, hsrc.2, fun heq => ?_⟩
  by_cases hfar : (t, s) ∈ D
  · have hne := (hdistant (t, s) hfar z w (hz.trans_le hδd') (hw.trans_le hδd')).2
    exact False.elim (hne (by simpa only [mem_singleton_iff, sub_eq_zero] using heq))
  have hnearF : 1 - t < η := by
    by_contra hn
    apply hfar
    exact Or.inl ⟨⟨ht.1, by linarith⟩, hs⟩
  have hnearG : s < η := by
    by_contra hn
    apply hfar
    exact Or.inr ⟨ht, ⟨le_of_not_gt hn, hs.2⟩⟩
  have hFsign := hsignF (1 - t) z
    (by rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]; exact hnearF.trans hηα) (hz.trans_le hδα)
  have hGsign := hsignG s w (by rw [abs_of_nonneg hs.1]; exact hnearG.trans hηβ)
    (hw.trans_le hδβ)
  have hFnonneg := hFsign.2.2.mpr (sub_nonneg.mpr ht.2)
  have hGnonneg := hGsign.2.2.mpr hs.1
  have hsum : f (1 - t, z) = -g (s, w) := by
    dsimp [f, g, R]
    rw [sub_sub_cancel, heq, hcommon]
  have hfzero' : f (1 - t, z) = 0 := by linarith
  have hgzero' : g (s, w) = 0 := by linarith
  exact ⟨by linarith [hFsign.2.1.mp hfzero'], hGsign.2.1.mp hgzero'⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in

theorem image_inter_eq_of_endpoint_separation
    {F G : ℝ × ℝ → E} {A B : Set (ℝ × ℝ)} {S : Set E}
    (hsep : ∀ q ∈ A, ∀ r ∈ B, F q = G r → q.1 = 1 ∧ r.1 = 0)
    (hFend : F '' (A ∩ {q | q.1 = 1}) = S)
    (hGend : G '' (B ∩ {q | q.1 = 0}) = S) : F '' A ∩ G '' B = S := by
  apply Subset.antisymm
  · rintro y ⟨⟨q, hq, hqy⟩, ⟨r, hr, hry⟩⟩
    have hend := hsep q hq r hr (hqy.trans hry.symm)
    rw [← hFend]
    exact ⟨q, ⟨hq, hend.1⟩, hqy⟩
  · intro y hy
    exact ⟨image_mono inter_subset_left (hFend.symm ▸ hy),
      image_mono inter_subset_left (hGend.symm ▸ hy)⟩

theorem exists_adjacent_strip_intersection
    (F G : OpenPartialHomeomorph (ℝ × ℝ) E)
    (hF : ContDiffOn ℝ 1 F F.source) (hG : ContDiffOn ℝ 1 G G.source)
    (hFs : ∀ t ∈ Icc (0 : ℝ) 1, (t, (0 : ℝ)) ∈ F.source)
    (hGs : ∀ t ∈ Icc (0 : ℝ) 1, (t, (0 : ℝ)) ∈ G.source)
    (hcommon : F (1, 0) = G (0, 0))
    (hbase : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      F (t, 0) = G (s, 0) → t = 1 ∧ s = 0)
    (ℓ : E →L[ℝ] ℝ)
    (hFt : 0 < ℓ (fderiv ℝ F (1, 0) (1, 0)))
    (hGt : 0 < ℓ (fderiv ℝ G (0, 0) (1, 0)))
    (hFline : ∀ᶠ z in 𝓝 (0 : ℝ), ℓ (F (1, z) - F (1, 0)) = 0)
    (hGline : ∀ᶠ z in 𝓝 (0 : ℝ), ℓ (G (0, z) - G (0, 0)) = 0) :
    ∃ δ > 0, ∀ A B : Set (ℝ × ℝ),
      A ⊆ Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ →
      B ⊆ Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ →
      ∀ S : Set E, F '' (A ∩ {q | q.1 = 1}) = S →
        G '' (B ∩ {q | q.1 = 0}) = S → F '' A ∩ G '' B = S := by
  obtain ⟨δ, hδ, hsep⟩ := exists_adjacent_strip_separation F G hF hG hFs hGs hcommon hbase
    ℓ hFt hGt hFline hGline
  refine ⟨δ, hδ, fun A B hA hB S hFend hGend => ?_⟩
  apply image_inter_eq_of_endpoint_separation ?_ hFend hGend
  intro q hq r hr heq
  have hqa := hA hq
  have hra := hB hr
  exact (hsep q.1 hqa.1 r.1 hra.1 q.2 r.2 (abs_lt.mpr hqa.2) (abs_lt.mpr hra.2)).2.2 heq

end Poincare.Topology.Plane.Curves
