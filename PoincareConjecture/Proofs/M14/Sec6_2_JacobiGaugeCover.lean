import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift
import PoincareConjecture.Definitions.M14PathCalculus
import PoincareConjecture.Proofs.M08.OverlappingIntervals










set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p)




theorem exists_squareRoot_gauge_neighborhood {s : ℝ}
    (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    ∃ (b : G.gaugeCover.index) (N : Set ℝ)
      (β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
        G.gaugeCover.spatial b), IsOpen N ∧ s ∈ N ∧
      ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β (M14SqrtParameterInterval τ₁ τ₂ ∩ N) ∧
      (∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N,
        (G.gaugeCover.cylinder b).toSpacetime (β r) = R.curve r) ∧
      (∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N, (β r).1.val = T - r ^ 2) := by
  obtain ⟨b, U, lift, hU, hsU, hlift, hright, hclock⟩ := exists_smooth_gauge_lift G (R.curve s)
  have hR := R.smooth.mono R.interval_subset
  have hpre : R.curve ⁻¹' U ∈ 𝓝[M14SqrtParameterInterval τ₁ τ₂] s :=
    (hR.continuousOn s hs).preimage_mem_nhdsWithin (hU.mem_nhds hsU)
  obtain ⟨N, hN, hsN, hsub⟩ := mem_nhdsWithin.mp hpre
  have hmap : MapsTo R.curve (M14SqrtParameterInterval τ₁ τ₂ ∩ N) U :=
    fun _ hr => hsub ⟨hr.2, hr.1⟩
  refine ⟨b, N, fun r => lift (R.curve r), hN, hsN,
    hlift.comp (hR.mono inter_subset_left) hmap, ?_, ?_⟩
  · intro r hr
    exact hright _ (hmap hr)
  · intro r hr
    exact (hclock _ (hmap hr)).trans (R.curve_time r hr.1)




theorem exists_overlapping_squareRoot_gauges :
    ∃ (m : ℕ) (t : Fin (m + 1) → ℝ) (b : Fin m → G.gaugeCover.index)
      (l r : Fin m → ℝ)
      (β : ∀ i, ℝ → (G.timeIntervals.interval (G.gaugeCover.interval (b i))).Point ×
        G.gaugeCover.spatial (b i)),
      0 < m ∧ Monotone t ∧ t 0 = Real.sqrt τ₁ ∧ t (Fin.last m) = Real.sqrt τ₂ ∧
      ∀ i, Real.sqrt τ₁ ≤ l i ∧ l i < r i ∧ r i ≤ Real.sqrt τ₂ ∧
        l i ≤ t i.castSucc ∧ t i.succ ≤ r i ∧
        ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (β i) (Icc (l i) (r i)) ∧
        (∀ s ∈ Icc (l i) (r i),
          (G.gaugeCover.cylinder (b i)).toSpacetime (β i s) = R.curve s) ∧
        (∀ s ∈ Icc (l i) (r i), (β i s).1.val = T - s ^ 2) ∧
        ∀ s ∈ Icc (t i.castSucc) (t i.succ),
          Icc (l i) (r i) ∈ 𝓝[M14SqrtParameterInterval τ₁ τ₂] s := by
  classical
  let C := M14SqrtParameterInterval τ₁ τ₂
  choose b N β hN hsN hβ hrec hclock using
    (fun s : C => exists_squareRoot_gauge_neighborhood R s.property)
  have hcover : C ⊆ ⋃ i, N i := by
    intro s hs
    exact mem_iUnion.mpr ⟨⟨s, hs⟩, hsN ⟨s, hs⟩⟩
  obtain ⟨m, t, k, l, r, hm, ht, hta, htb, hp⟩ :=
    M08.exists_overlapping_Icc_partition N hN
      (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt) hcover
  refine ⟨m, t, fun i => b (k i), l, r, fun i => β (k i), hm, ht, hta, htb, ?_⟩
  intro i
  obtain ⟨hal, hlr, hrb, hlt, htr, hsub, hnear⟩ := hp i
  have hmap : Icc (l i) (r i) ⊆ C ∩ N (k i) :=
    fun _ hs => ⟨Icc_subset_Icc hal hrb hs, hsub hs⟩
  exact ⟨hal, hlr, hrb, hlt, htr, (hβ (k i)).mono hmap,
    fun s hs => hrec (k i) s (hmap hs), fun s hs => hclock (k i) s (hmap hs), hnear⟩

end PoincareConjecture.M14
