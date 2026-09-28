import PoincareConjecture.Statements.M63LocalFlow

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {c d : ℝ → ℝ → M} {J K : Set ℝ}

theorem c2_restrict (hc : M63C2ShrinkingCurveOn F c J) (hK : K ⊆ J) :
    M63C2ShrinkingCurveOn F c K where
  domain_subset := hK.trans hc.domain_subset
  periodic t ht := hc.periodic t (hK ht)
  spatial_regular t ht := hc.spatial_regular t (hK ht)
  joint_c1 := hc.joint_c1.mono (Set.prod_mono Subset.rfl (interior_mono hK))
  immersed t ht := hc.immersed t (hK ht)
  continuous := hc.continuous.mono (Set.prod_mono Subset.rfl hK)
  velocity_continuous := hc.velocity_continuous.mono (Set.prod_mono Subset.rfl hK)
  curvature_continuous := hc.curvature_continuous.mono (Set.prod_mono Subset.rfl hK)
  equation t ht := hc.equation t (interior_mono hK ht)

theorem c2_congr (hc : M63C2ShrinkingCurveOn F c J)
    (h : ∀ t ∈ J, ∀ x, d x t = c x t) : M63C2ShrinkingCurveOn F d J := by
  have hslice (t : ℝ) (ht : t ∈ J) : (fun x => d x t) = (fun x => c x t) :=
    funext (h t ht)
  refine
    { domain_subset := hc.domain_subset
      periodic := fun t ht => ?_
      spatial_regular := fun t ht => ?_
      joint_c1 := hc.joint_c1.congr (fun z hz => h z.2 (interior_subset hz.2) z.1)
      immersed := fun t ht x => ?_
      continuous := hc.continuous.congr (fun z hz => h z.2 hz.2 z.1)
      velocity_continuous := hc.velocity_continuous.congr (fun z hz => ?_)
      curvature_continuous := hc.curvature_continuous.congr (fun z hz => ?_)
      equation := fun t ht x => ?_ }
  · rw [hslice t ht]
    exact hc.periodic t ht
  · rw [hslice t ht]
    exact hc.spatial_regular t ht
  · rw [hslice t ht]
    exact hc.immersed t ht x
  · exact congrArg (fun gamma : ℝ → M =>
      (⟨gamma z.1, curveVelocity (n := n) gamma z.1⟩ : TangentBundle (𝓡 n) M))
      (hslice z.2 hz.2)
  · exact congrArg (fun gamma : ℝ → M =>
      (⟨gamma z.1, m62CurvatureVector F (fun x _ => gamma x) z.2 z.1⟩ :
        TangentBundle (𝓡 n) M)) (hslice z.2 hz.2)
  · have heq : (fun s => d x s) =ᶠ[𝓝 t] (fun s => c x s) := by
      filter_upwards [isOpen_interior.mem_nhds ht] with s hs
      exact h s (interior_subset hs) x
    have hv : curveVelocity (n := n) (fun s => d x s) t =
        curveVelocity (n := n) (fun s => c x s) t := by
      unfold curveVelocity
      rw [heq.mfderiv_eq]
      rfl
    have hH : m62CurvatureVector F d t x = m62CurvatureVector F c t x :=
      congrArg (fun gamma : ℝ → M => m62CurvatureVector F (fun y _ => gamma y) t x)
        (hslice t (interior_subset ht))
    rw [hv, hH]
    exact hc.equation t ht x

theorem c2_of_closed_prefixes {T : ℝ}
    (hprefix : ∀ t ∈ Ico a T, ∃ s, t < s ∧ s < T ∧
      M63C2ShrinkingCurveOn F c (Icc a s)) :
    M63C2ShrinkingCurveOn F c (Ico a T) := by
  have hcont {Z : Type u} [TopologicalSpace Z] (f : ℝ × ℝ → Z)
      (hf : ∀ s, M63C2ShrinkingCurveOn F c (Icc a s) →
        ContinuousOn f (univ ×ˢ Icc a s)) : ContinuousOn f (univ ×ˢ Ico a T) := by
    apply continuousOn_of_locally_continuousOn
    intro z hz
    obtain ⟨s, hts, _, hs⟩ := hprefix z.2 hz.2
    refine ⟨univ ×ˢ Iio s, isOpen_univ.prod isOpen_Iio, ⟨mem_univ _, hts⟩, ?_⟩
    exact (hf s hs).mono (fun y hy => ⟨mem_univ _, hy.1.2.1, hy.2.2.le⟩)
  refine
    { domain_subset := fun t ht => ?_
      periodic := fun t ht => ?_
      spatial_regular := fun t ht => ?_
      joint_c1 := ?_
      immersed := fun t ht => ?_
      continuous := hcont _ (fun _ hs => hs.continuous)
      velocity_continuous := hcont _ (fun _ hs => hs.velocity_continuous)
      curvature_continuous := hcont _ (fun _ hs => hs.curvature_continuous)
      equation := fun t ht => ?_ }
  · obtain ⟨s, hts, _, hs⟩ := hprefix t ht
    exact hs.domain_subset ⟨ht.1, hts.le⟩
  · obtain ⟨s, hts, _, hs⟩ := hprefix t ht
    exact hs.periodic t ⟨ht.1, hts.le⟩
  · obtain ⟨s, hts, _, hs⟩ := hprefix t ht
    exact hs.spatial_regular t ⟨ht.1, hts.le⟩
  · rw [interior_Ico]
    apply contMDiffOn_of_locally_contMDiffOn
    intro z hz
    obtain ⟨s, hts, _, hs⟩ := hprefix z.2 (Ioo_subset_Ico_self hz.2)
    refine ⟨univ ×ˢ Iio s, isOpen_univ.prod isOpen_Iio, ⟨mem_univ _, hts⟩, ?_⟩
    apply hs.joint_c1.mono
    rw [interior_Icc]
    exact fun y hy => ⟨mem_univ _, hy.1.2.1, hy.2.2⟩
  · obtain ⟨s, hts, _, hs⟩ := hprefix t ht
    exact hs.immersed t ⟨ht.1, hts.le⟩
  · rw [interior_Ico] at ht
    obtain ⟨s, hts, _, hs⟩ := hprefix t (Ioo_subset_Ico_self ht)
    exact hs.equation t (by rw [interior_Icc]; exact ⟨ht.1, hts⟩)

end PoincareConjecture.M63
