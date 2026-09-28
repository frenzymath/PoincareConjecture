import PoincareConjecture.Proofs.M08.JacobiAlongPair
import PoincareConjecture.Proofs.M08.ClosedSectionExtension
import PoincareConjecture.Proofs.M08.IntervalSolutionGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem sectionPaste_contMDiffOn (α : ℝ → M) {a l c r : ℝ}
    (hlc : l < c) (hcr : c < r)
    (Y Z : ∀ s, TangentSpace (𝓡 n) (α s))
    (hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (Y s)) (Icc a c))
    (hZ : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (Z s)) (Icc l r))
    (heq : ∀ s ∈ Icc l c, Y s = Z s) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s)
        (if s ≤ c then Y s else Z s)) (Icc a r) := by
  have hleft : ∀ s ∈ Icc a c,
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s)
          (if s ≤ c then Y s else Z s) =
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (Y s) := by
    intro s hs
    rw [if_pos hs.2]
  have hright : ∀ s ∈ Icc l r,
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s)
          (if s ≤ c then Y s else Z s) =
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (Z s) := by
    intro s hs
    by_cases hsc : s ≤ c
    · rw [if_pos hsc, heq s ⟨hs.1, hsc⟩]
    · rw [if_neg hsc]
  intro s hs
  by_cases hsc : s < c
  · have hsold : s ∈ Icc a c := ⟨hs.1, hsc.le⟩
    apply ((hY s hsold).congr_of_mem hleft hsold).mono_of_mem_nhdsWithin
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨Iio c, Iio_mem_nhds hsc, ?_⟩
    intro t ht
    exact ⟨ht.2.1, ht.1.le⟩
  · have hcs : c ≤ s := le_of_not_gt hsc
    have hsnew : s ∈ Icc l r := ⟨hlc.le.trans hcs, hs.2⟩
    apply ((hZ s hsnew).congr_of_mem hright hsnew).mono_of_mem_nhdsWithin
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨Ioi l, Ioi_mem_nhds (hlc.trans_le hcs), ?_⟩
    intro t ht
    exact ⟨ht.1.le, ht.2.2⟩

set_option maxHeartbeats 1500000 in
theorem jacobiPairOn_paste {J S U : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (α : ℝ → M) (hU : IsOpen U) (hSU : S ⊆ U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    {a l c r : ℝ} (hal : a ≤ l) (hlc : l < c) (hcr : c < r)
    {f g : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (hf : IsJacobiPairOn F T α S a c f) (hg : IsJacobiPairOn F T α S l r g)
    (heq : EqOn f g (Icc l c)) :
    IsJacobiPairOn F T α S a r (fun s ↦ if s ≤ c then f s else g s) := by
  let q := fun s ↦ if s ≤ c then f s else g s
  have har : a < r := (hal.trans_lt hlc).trans hcr
  have hqS : Icc a r ⊆ S := by
    intro s hs
    by_cases hsc : s ≤ c
    · exact hf.interval_subset ⟨hs.1, hsc⟩
    · exact hg.interval_subset ⟨hlc.le.trans (le_of_not_ge hsc), hs.2⟩
  have hqY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (E := TangentSpace (𝓡 n))
        (EuclideanSpace ℝ (Fin n)) (α s) (q s).1) (Icc a r) := by
    have h := sectionPaste_contMDiffOn α hlc hcr (fun s ↦ (f s).1) (fun s ↦ (g s).1)
      hf.first_smooth hg.first_smooth (fun s hs ↦ congrArg Prod.fst (heq hs))
    convert h using 1
    funext s
    dsimp only [q]
    split_ifs <;> rfl
  have hqP : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (E := TangentSpace (𝓡 n))
        (EuclideanSpace ℝ (Fin n)) (α s) (q s).2) (Icc a r) := by
    have h := sectionPaste_contMDiffOn α hlc hcr (fun s ↦ (f s).2) (fun s ↦ (g s).2)
      hf.second_smooth hg.second_smooth (fun s hs ↦ congrArg Prod.snd (heq hs))
    convert h using 1
    funext s
    dsimp only [q]
    split_ifs <;> rfl
  obtain ⟨EY⟩ := exists_closedSectionExtension har hU (hqS.trans hSU) α hα
    (fun s ↦ (q s).1) hqY
  obtain ⟨EP⟩ := exists_closedSectionExtension har hU (hqS.trans hSU) α hα
    (fun s ↦ (q s).2) hqP
  have hαs (s : ℝ) (hs : s ∈ S) : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s :=
    ((hα s (hSU hs)).contMDiffAt (hU.mem_nhds (hSU hs))).mdifferentiableAt (by simp)
  have hlocal {d e : ℝ} (hde : IsJacobiPairOn F T α S d e q)
      (hsub : Icc d e ⊆ Icc a r) :
      ∀ s ∈ Icc d e,
        pullbackCovariantDerivative F (fun v ↦ T - v ^ 2) α
          (fun v ↦ (q v).1) (Icc a r) EY s = (q s).2 ∧
        ∀ W : TangentSpace (𝓡 n) (α s),
          jacobiPairResidual F T α S s (q s).1 (q s).2
            (pullbackCovariantDerivative F (fun v ↦ T - v ^ 2) α
              (fun v ↦ (q v).2) (Icc a r) EP s) W = 0 := by
    have hlocalEq := hde.equations_for_extensions
      (fun s hs ↦ hαs s (hde.interval_subset hs))
      (restrictParametricSectionExtension hsub EY) (restrictParametricSectionExtension hsub EP)
    intro s hs
    have hDY := pullbackCovariantDerivative_restrict F (fun v ↦ T - v ^ 2) hsub EY
      (uniqueDiffOn_Icc har s (hsub hs)) (uniqueDiffOn_Icc hde.ordered s hs)
      (hαs s (hde.interval_subset hs))
    have hDP := pullbackCovariantDerivative_restrict F (fun v ↦ T - v ^ 2) hsub EP
      (uniqueDiffOn_Icc har s (hsub hs)) (uniqueDiffOn_Icc hde.ordered s hs)
      (hαs s (hde.interval_subset hs))
    refine ⟨hDY.trans (hlocalEq.1 s hs), ?_⟩
    intro W
    rw [hDP]
    exact hlocalEq.2 s hs W
  have hleft : IsJacobiPairOn F T α S a c q := hf.congr (by
    intro s hs
    simp only [q, if_pos hs.2])
  have hright : IsJacobiPairOn F T α S l r q := hg.congr (by
    intro s hs
    dsimp only [q]
    split_ifs with hsc
    · exact (heq ⟨hs.1, hsc⟩).symm
    · rfl)
  have hpoint : ∀ s ∈ Icc a r,
      pullbackCovariantDerivative F (fun v ↦ T - v ^ 2) α
        (fun v ↦ (q v).1) (Icc a r) EY s = (q s).2 ∧
      ∀ W : TangentSpace (𝓡 n) (α s),
        jacobiPairResidual F T α S s (q s).1 (q s).2
          (pullbackCovariantDerivative F (fun v ↦ T - v ^ 2) α
            (fun v ↦ (q v).2) (Icc a r) EP s) W = 0 := by
    intro s hs
    by_cases hsc : s ≤ c
    · exact hlocal hleft (Icc_subset_Icc le_rfl hcr.le) s ⟨hs.1, hsc⟩
    · exact hlocal hright (Icc_subset_Icc hal le_rfl) s
        ⟨hlc.le.trans (le_of_not_ge hsc), hs.2⟩
  exact ⟨har, hqS, hqY, hqP, EY, EP,
    fun s hs ↦ (hpoint s hs).1, fun s hs ↦ (hpoint s hs).2⟩

theorem jacobiPairOn_locality {J S U : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (α : ℝ → M) (hU : IsOpen U) (hSU : S ⊆ U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U) :
    IntervalSolutionLocality (IsJacobiPairOn F T α S) where
  restrict hac hcd hdb h := h.restrict (fun s hs ↦
    ((hα s (hSU (h.interval_subset hs))).contMDiffAt
      (hU.mem_nhds (hSU (h.interval_subset hs)))).mdifferentiableAt (by simp)) hac hcd hdb
  paste hal hlc hcr hf hg heq := jacobiPairOn_paste F T α hU hSU hα hal hlc hcr hf hg heq

end PoincareConjecture.M08
