import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Extension.Euclidean
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem chart_curve_contDiffOn {I : Set ℝ} (x : M) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α I)
    (hsrc : MapsTo α I (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ContDiffOn ℝ ∞ ((extChartAt (𝓡 n) x) ∘ α) I := by
  apply ContMDiffOn.contDiffOn
  apply (contMDiffOn_extChartAt (I := 𝓡 n) (x := x)).comp hα
  intro r hr
  simpa only [mem_preimage, extChartAt_source] using hsrc hr

theorem exists_smooth_chart_extension_Icc {a b : ℝ} (hab : a < b)
    (x : M) (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α (Icc a b))
    (hsrc : MapsTo α (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ∃ (β : ℝ → M) (U : Set ℝ), IsOpen U ∧ Icc a b ⊆ U ∧
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ β U ∧ EqOn β α (Icc a b) := by
  let e := extChartAt (𝓡 n) x
  have hu : ContDiffOn ℝ ∞ (e ∘ α) (Icc a b) := chart_curve_contDiffOn x α hα hsrc
  obtain ⟨v, hv, hvα⟩ := exists_smooth_extension_Icc hab (e ∘ α) hu
  let U := v ⁻¹' e.target
  have hU : IsOpen U := (isOpen_extChartAt_target (I := 𝓡 n) x).preimage hv.continuous
  have hsrc' : MapsTo α (Icc a b) e.source := by simpa only [e, extChartAt_source] using hsrc
  have hsub : Icc a b ⊆ U := by
    intro s hs
    change v s ∈ e.target
    rw [hvα hs]
    exact e.map_source (hsrc' hs)
  refine ⟨e.symm ∘ v, U, hU, hsub, ?_, ?_⟩
  · exact (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).comp hv.contMDiff.contMDiffOn
      (fun s hs ↦ hs)
  · intro s hs
    change e.symm (v s) = α s
    rw [hvα hs]
    exact e.left_inv (hsrc' hs)

theorem endpoint_chart_intervals {a b : ℝ} (hab : a < b) (α : ℝ → M)
    (hα : ContinuousOn α (Icc a b)) :
    ∃ c d : ℝ, a < c ∧ c < b ∧ a < d ∧ d < b ∧
      MapsTo α (Icc a c) (chartAt (EuclideanSpace ℝ (Fin n)) (α a)).source ∧
      MapsTo α (Icc d b) (chartAt (EuclideanSpace ℝ (Fin n)) (α b)).source := by
  let f : Icc a b → M := fun s ↦ α s
  have hf : Continuous f := continuousOn_iff_continuous_domRestrict.mp hα
  let γ := f ∘ projIcc a b hab.le
  have hγ : Continuous γ := hf.comp continuous_projIcc
  have hγα : EqOn γ α (Icc a b) := by
    intro s hs
    simp only [γ, Function.comp_apply, projIcc_of_mem hab.le hs, f]
  have hleft : γ ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) (α a)).source ∈ 𝓝 a := by
    apply hγ.continuousAt.preimage_mem_nhds
    apply (chartAt (EuclideanSpace ℝ (Fin n)) (α a)).open_source.mem_nhds
    rw [hγα ⟨le_rfl, hab.le⟩]
    exact mem_chart_source _ _
  have hright : γ ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) (α b)).source ∈ 𝓝 b := by
    apply hγ.continuousAt.preimage_mem_nhds
    apply (chartAt (EuclideanSpace ℝ (Fin n)) (α b)).open_source.mem_nhds
    rw [hγα ⟨hab.le, le_rfl⟩]
    exact mem_chart_source _ _
  obtain ⟨l, r, ⟨hla, har⟩, hL⟩ := mem_nhds_iff_exists_Ioo_subset.mp hleft
  obtain ⟨l', r', ⟨hlb, hbr⟩, hR⟩ := mem_nhds_iff_exists_Ioo_subset.mp hright
  obtain ⟨c, hac, hcm⟩ := exists_between (lt_min hab har)
  obtain ⟨d, hmd, hdb⟩ := exists_between (max_lt hab hlb)
  have hcb := hcm.trans_le (min_le_left b r)
  have had := (le_max_left a l').trans_lt hmd
  refine ⟨c, d, hac, hcb, had, hdb, ?_, ?_⟩
  · intro s hs
    have h := hL ⟨hla.trans_le hs.1, hs.2.trans_lt (hcm.trans_le (min_le_right b r))⟩
    change γ s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (α a)).source at h
    rwa [hγα ⟨hs.1, hs.2.trans hcb.le⟩] at h
  · intro s hs
    have h := hR ⟨((le_max_right a l').trans_lt hmd).trans_le hs.1, hs.2.trans_lt hbr⟩
    change γ s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (α b)).source at h
    rwa [hγα ⟨had.le.trans hs.1, hs.2⟩] at h

set_option maxHeartbeats 800000 in
theorem exists_smooth_manifold_extension_Icc {a b : ℝ} (hab : a < b)
    (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α (Icc a b)) :
    ∃ (β : ℝ → M) (U : Set ℝ), IsOpen U ∧ Icc a b ⊆ U ∧
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ β U ∧ EqOn β α (Icc a b) := by
  classical
  obtain ⟨c, d, hac, hcb, had, hdb, hsrcL, hsrcR⟩ :=
    endpoint_chart_intervals (n := n) hab α hα.continuousOn
  obtain ⟨L, UL, hUL, hsubL, hL, hagL⟩ := exists_smooth_chart_extension_Icc hac (α a) α
    (hα.mono (Icc_subset_Icc le_rfl hcb.le)) hsrcL
  obtain ⟨R, UR, hUR, hsubR, hR, hagR⟩ := exists_smooth_chart_extension_Icc hdb (α b) α
    (hα.mono (Icc_subset_Icc had.le le_rfl)) hsrcR
  let β : ℝ → M := fun s ↦ if s ≤ a then L s else if b ≤ s then R s else α s
  let U := ((Iio c ∩ UL) ∪ Ioo a b) ∪ (Ioi d ∩ UR)
  have hβL : EqOn β L (Iio c) := by
    intro s hs
    dsimp only [β]
    split_ifs with hsa hbs
    · rfl
    · exact False.elim ((lt_of_lt_of_le hs hcb.le).not_ge hbs)
    · exact (hagL ⟨(lt_of_not_ge hsa).le, hs.le⟩).symm
  have hβR : EqOn β R (Ioi d) := by
    intro s hs
    have has : a < s := had.trans hs
    dsimp only [β]
    rw [if_neg has.not_ge]
    split_ifs with hbs
    · rfl
    · exact (hagR ⟨hs.le, (lt_of_not_ge hbs).le⟩).symm
  have hβα : EqOn β α (Ioo a b) := by
    intro s hs
    simp only [β, if_neg hs.1.not_ge, if_neg hs.2.not_ge]
  refine ⟨β, U, ((isOpen_Iio.inter hUL).union isOpen_Ioo).union
    (isOpen_Ioi.inter hUR), ?_, ?_, ?_⟩
  · intro s hs
    rcases eq_or_lt_of_le hs.1 with hsa | has
    · subst s
      exact Or.inl (Or.inl ⟨hac, hsubL ⟨le_rfl, hac.le⟩⟩)
    · rcases eq_or_lt_of_le hs.2 with hsb | hsb
      · subst s
        exact Or.inr ⟨hdb, hsubR ⟨hdb.le, le_rfl⟩⟩
      · exact Or.inl (Or.inr ⟨has, hsb⟩)
  · intro s hs
    rcases hs with (hs | hs) | hs
    · exact (((hL s hs.2).contMDiffAt (hUL.mem_nhds hs.2)).congr_of_eventuallyEq
        (eventuallyEq_of_mem (isOpen_Iio.mem_nhds hs.1) hβL)).contMDiffWithinAt
    · exact (((hα s (Ioo_subset_Icc_self hs)).contMDiffAt (Icc_mem_nhds hs.1 hs.2)).congr_of_eventuallyEq
        (eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs) hβα)).contMDiffWithinAt
    · exact (((hR s hs.2).contMDiffAt (hUR.mem_nhds hs.2)).congr_of_eventuallyEq
        (eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hs.1) hβR)).contMDiffWithinAt
  · intro s hs
    rcases eq_or_lt_of_le hs.1 with hsa | has
    · subst s
      exact (hβL hac).trans (hagL ⟨le_rfl, hac.le⟩)
    · rcases eq_or_lt_of_le hs.2 with hsb | hsb
      · subst s
        exact (hβR hdb).trans (hagR ⟨hdb.le, le_rfl⟩)
      · exact hβα ⟨has, hsb⟩

end PoincareConjecture.ReducedLengthMinimum.Variational
