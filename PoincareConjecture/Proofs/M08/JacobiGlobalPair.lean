import PoincareConjecture.Proofs.M08.JacobiLocalUniqueness
import PoincareConjecture.Proofs.M08.JacobiPairGluing
import PoincareConjecture.Proofs.M08.IntervalSolutionUnique

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_overlapping_curve_charts {U : Set ℝ} {a b : ℝ} (hab : a < b)
    (α : ℝ → M) (hU : IsOpen U) (hCU : Icc a b ⊆ U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U) :
    ∃ (m : ℕ) (t : Fin (m + 1) → ℝ) (x : Fin m → M) (l r : Fin m → ℝ),
      0 < m ∧ Monotone t ∧ t 0 = a ∧ t (Fin.last m) = b ∧
      ∀ i, a ≤ l i ∧ l i < r i ∧ r i ≤ b ∧ l i ≤ t i.castSucc ∧
        t i.succ ≤ r i ∧
          MapsTo α (Icc (l i) (r i)) (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source ∧
            ∀ s ∈ Icc (t i.castSucc) (t i.succ),
              Icc (l i) (r i) ∈ 𝓝[Icc a b] s := by
  let V : M → Set ℝ := fun x ↦ U ∩ α ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source
  have hV : ∀ x, IsOpen (V x) := fun x ↦
    hα.continuousOn.isOpen_inter_preimage hU (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
  have hcover : Icc a b ⊆ ⋃ x, V x := by
    intro s hs
    exact mem_iUnion.mpr ⟨α s, hCU hs, mem_chart_source (EuclideanSpace ℝ (Fin n)) (α s)⟩
  obtain ⟨m, t, x, l, r, hm, ht, hta, htb, hp⟩ :=
    exists_overlapping_Icc_partition V hV hab hcover
  refine ⟨m, t, x, l, r, hm, ht, hta, htb, ?_⟩
  intro i
  obtain ⟨hal, hlr, hrb, hlt, htr, hsub, hnear⟩ := hp i
  exact ⟨hal, hlr, hrb, hlt, htr, fun s hs ↦ (hsub hs).2, hnear⟩

theorem exists_jacobiPairOn {J U : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    (α : ℝ → M) (hU : IsOpen U) (hCU : Icc a b ⊆ U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (z₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    ∃ z : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      IsJacobiPairOn F T α (Icc a b) a b z ∧ z a = z₀ := by
  obtain ⟨m, t, x, l, r, hm, ht, hta, htb, hp⟩ :=
    exists_overlapping_curve_charts hab α hU hCU hα
  apply exists_interval_solution_of_overlapping_cover (IsJacobiPairOn F T α (Icc a b))
    (jacobiPairOn_locality F T α hU hCU hα) hab hm t l r ht hta htb
      (fun i ↦ ⟨(hp i).1, (hp i).2.1, (hp i).2.2.1, (hp i).2.2.2.1,
        (hp i).2.2.2.2.1, (hp i).2.2.2.2.2.2⟩) ?_ ?_ z₀
  · intro i s hs z
    obtain ⟨hal, hlr, hrb, hlt, htr, hsrc, hnear⟩ := hp i
    exact exists_chartJacobiPairOn F hM04 T hab hlr (Icc_subset_Icc hal hrb) htime
      (x i) α hU ((Icc_subset_Icc hal hrb).trans hCU) hα hsrc hs z
  · intro i c d hlc hcd hdr f g hf hg s hs hinit
    obtain ⟨hal, hlr, hrb, hlt, htr, hsrc, hnear⟩ := hp i
    exact chartJacobiPairOn_unique hM04 hf hg hab htime (x i) hU
      (hf.interval_subset.trans hCU) hα
      (hsrc.mono (Icc_subset_Icc hlc hdr) Subset.rfl) hs hinit

theorem jacobiPairOn_unique {J U : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T a b : ℝ} {α : ℝ → M}
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    (hU : IsOpen U) (hCU : Icc a b ⊆ U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    {f g : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (hf : IsJacobiPairOn F T α (Icc a b) a b f)
    (hg : IsJacobiPairOn F T α (Icc a b) a b g) (hinit : f a = g a) :
    EqOn f g (Icc a b) := by
  obtain ⟨m, t, x, l, r, hm, ht, hta, htb, hp⟩ :=
    exists_overlapping_curve_charts hf.ordered α hU hCU hα
  apply interval_solution_unique_of_cover (IsJacobiPairOn F T α (Icc a b))
    (jacobiPairOn_locality F T α hU hCU hα) hm t l r ht hta htb
      (fun i ↦ ⟨(hp i).1, (hp i).2.1, (hp i).2.2.1,
        (hp i).2.2.2.1, (hp i).2.2.2.2.1⟩) ?_ hf hg hinit
  intro i f' g' hf' hg' s hs hinit'
  obtain ⟨hal, hlr, hrb, hlt, htr, hsrc, hnear⟩ := hp i
  exact chartJacobiPairOn_unique hM04 hf' hg' hf.ordered htime (x i) hU
    (hf'.interval_subset.trans hCU) hα hsrc hs hinit'

end PoincareConjecture.M08
