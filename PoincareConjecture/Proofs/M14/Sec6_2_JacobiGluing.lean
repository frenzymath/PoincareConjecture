import PoincareConjecture.Proofs.M14.Sec6_2_JacobiPair
import PoincareConjecture.Proofs.M14.Sec6_2_ClosedFieldExtension
import PoincareConjecture.Proofs.M14.Mathlib.DependentIntervalSolution

set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem horizontalField_paste_contMDiffOn (γ : ℝ → G.Point) {a l c r : ℝ}
    (hlc : l < c) (Y Z : ∀ s, G.Horizontal (γ s))
    (hY : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (γ s) (Y s)) (Icc a c))
    (hZ : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (γ s) (Z s)) (Icc l r))
    (heq : ∀ s ∈ Icc l c, Y s = Z s) :
    ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (γ s)
        (if s ≤ c then Y s else Z s)) (Icc a r) := by
  have hleft : ∀ s ∈ Icc a c,
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (γ s)
          (if s ≤ c then Y s else Z s) =
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (γ s) (Y s) := by
    intro s hs
    rw [if_pos hs.2]
  have hright : ∀ s ∈ Icc l r,
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (γ s)
          (if s ≤ c then Y s else Z s) =
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (γ s) (Z s) := by
    intro s hs
    by_cases hsc : s ≤ c
    · rw [if_pos hsc, heq s ⟨hs.1, hsc⟩]
    · rw [if_neg hsc]
  intro s hs
  by_cases hsc : s < c
  · have hsold : s ∈ Icc a c := ⟨hs.1, hsc.le⟩
    apply ((hY s hsold).congr_of_mem hleft hsold).mono_of_mem_nhdsWithin
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    exact ⟨Iio c, Iio_mem_nhds hsc, fun _ ht => ⟨ht.2.1, ht.1.le⟩⟩
  · have hcs : c ≤ s := le_of_not_gt hsc
    have hsnew : s ∈ Icc l r := ⟨hlc.le.trans hcs, hs.2⟩
    apply ((hZ s hsnew).congr_of_mem hright hsnew).mono_of_mem_nhdsWithin
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    exact ⟨Ioi l, Ioi_mem_nhds (hlc.trans_le hcs), fun _ ht => ⟨ht.1.le, ht.2.2⟩⟩

variable {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

theorem horizontalJacobiPairOn_paste {a l c r : ℝ}
    (hal : a ≤ l) (hlc : l < c) (hcr : c < r)
    {f g : ∀ s, G.Horizontal (R.curve s) × G.Horizontal (R.curve s)}
    (hf : IsHorizontalJacobiPairOn R a c f) (hg : IsHorizontalJacobiPairOn R l r g)
    (heq : ∀ s ∈ Icc l c, f s = g s) :
    IsHorizontalJacobiPairOn R a r (fun s => if s ≤ c then f s else g s) := by
  let q := fun s => if s ≤ c then f s else g s
  have har : a < r := (hal.trans_lt hlc).trans hcr
  have hqC : Icc a r ⊆ M14SqrtParameterInterval τ₁ τ₂ := by
    intro s hs
    by_cases hsc : s ≤ c
    · exact hf.interval_subset ⟨hs.1, hsc⟩
    · exact hg.interval_subset ⟨hlc.le.trans (le_of_not_ge hsc), hs.2⟩
  have hqY : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (q s).1)
      (Icc a r) := by
    have h := horizontalField_paste_contMDiffOn R.curve hlc (fun s => (f s).1)
      (fun s => (g s).1) hf.first_smooth hg.first_smooth
      (fun s hs => congrArg Prod.fst (heq s hs))
    convert h using 1
    funext s
    dsimp only [q]
    split_ifs <;> rfl
  have hqP : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (q s).2)
      (Icc a r) := by
    have h := horizontalField_paste_contMDiffOn R.curve hlc (fun s => (f s).2)
      (fun s => (g s).2) hf.second_smooth hg.second_smooth
      (fun s hs => congrArg Prod.snd (heq s hs))
    convert h using 1
    funext s
    dsimp only [q]
    split_ifs <;> rfl
  obtain ⟨EY⟩ := exists_pullbackExtension_Icc har hqY
  obtain ⟨EP⟩ := exists_pullbackExtension_Icc har hqP
  have hR := R.smooth.mono (hqC.trans R.interval_subset)
  have hlocal {d e : ℝ} (hde : IsHorizontalJacobiPairOn R d e q)
      (hsub : Icc d e ⊆ Icc a r) :
      ∀ s ∈ Icc d e,
        M14HorizontalCovariantDerivative G R.curve (Icc a r)
          (fun v => (q v).1) EY s = (q s).2 ∧
        ∀ W : G.Horizontal (R.curve s),
          horizontalJacobiPairResidual R s (q s).1 (q s).2
            (M14HorizontalCovariantDerivative G R.curve (Icc a r)
              (fun v => (q v).2) EP s) W = 0 := by
    have hEq := hde.equations_for_extensions
      (pullbackExtensionRestrict EY hsub) (pullbackExtensionRestrict EP hsub)
    intro s hs
    have hDY := horizontalCovariantDerivative_restrict_subset EY hsub
      (uniqueDiffOn_Icc hde.ordered s hs) ((hR s (hsub hs)).mdifferentiableWithinAt (by simp))
    have hDP := horizontalCovariantDerivative_restrict_subset EP hsub
      (uniqueDiffOn_Icc hde.ordered s hs) ((hR s (hsub hs)).mdifferentiableWithinAt (by simp))
    exact ⟨hDY.trans (hEq.1 s hs), fun W => hDP ▸ hEq.2 s hs W⟩
  have hleft : IsHorizontalJacobiPairOn R a c q := hf.congr (by
    intro s hs
    simp only [q, if_pos hs.2])
  have hright : IsHorizontalJacobiPairOn R l r q := hg.congr (by
    intro s hs
    dsimp only [q]
    split_ifs with hsc
    · exact (heq s ⟨hs.1, hsc⟩).symm
    · rfl)
  have hpoint (s : ℝ) (hs : s ∈ Icc a r) := by
    by_cases hsc : s ≤ c
    · exact hlocal hleft (Icc_subset_Icc le_rfl hcr.le) s ⟨hs.1, hsc⟩
    · exact hlocal hright (Icc_subset_Icc hal le_rfl) s
        ⟨hlc.le.trans (le_of_not_ge hsc), hs.2⟩
  exact ⟨har, hqC, hqY, hqP, EY, EP,
    fun s hs => (hpoint s hs).1, fun s hs => (hpoint s hs).2⟩

theorem horizontalJacobiPairOn_locality (R : M14SquareRootPath G p) :
    DependentIntervalSolutionLocality (IsHorizontalJacobiPairOn R) where
  restrict hac hcd hdb h := h.restrict hac hcd hdb
  paste hal hlc hcr hf hg heq := horizontalJacobiPairOn_paste hal hlc hcr hf hg heq

end PoincareConjecture.M14
