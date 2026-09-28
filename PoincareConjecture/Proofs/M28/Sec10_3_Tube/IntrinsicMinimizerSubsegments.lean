import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicSplicing










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]




theorem pathELength_eq_intrinsicEDist_subsegment (g : RiemannianMetric 3 M)
    {U : Set M} {γ : ℝ → M} {a b c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hfinite : g.pathELength γ a b ≠ ⊤)
    (hmin : g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b)) :
    g.pathELength γ c d = intrinsicEDist g U (γ c) (γ d) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hac hdb
  apply le_antisymm ?_
    (intrinsicEDist_le_pathELength g hcd (hγ.mono hsub)
      (fun _ ht => hγU (hsub ht)))
  by_contra hnot
  have hshort : intrinsicEDist g U (γ c) (γ d) < g.pathELength γ c d :=
    lt_of_not_ge hnot
  obtain ⟨α, hα0, hα1, hα, hαU, hαlen⟩ :=
    exists_intrinsic_competitor g hshort
  obtain ⟨σ, hσ0, hσ1, hσ, hσU, hσlen⟩ :=
    exists_intrinsic_subarc_replacement g hac hcd hdb hγ hγU
      hα hαU hα0 hα1
  have hleft : g.pathELength γ a c ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite
      (Manifold.pathELength_mono le_rfl (hcd.trans hdb))
  have hright : g.pathELength γ d b ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite
      (Manifold.pathELength_mono (hac.trans hcd) le_rfl)
  have hsplit : g.pathELength γ a c + g.pathELength γ c d +
      g.pathELength γ d b = g.pathELength γ a b := by
    change Manifold.pathELength (𝓡 3) γ a c +
      Manifold.pathELength (𝓡 3) γ c d +
      Manifold.pathELength (𝓡 3) γ d b = Manifold.pathELength (𝓡 3) γ a b
    rw [Manifold.pathELength_add hac hcd,
      Manifold.pathELength_add (hac.trans hcd) hdb]
  have hshorter : g.pathELength σ 0 1 < g.pathELength γ a b := by
    rw [hσlen, ← hsplit]
    exact ENNReal.add_lt_add_right hright (ENNReal.add_lt_add_left hleft hαlen)
  have hbound := intrinsicEDist_le_pathELength g zero_le_one hσ hσU
  rw [hσ0, hσ1, ← hmin] at hbound
  exact (not_lt_of_ge hbound) hshorter

end PoincareConjecture.M28
