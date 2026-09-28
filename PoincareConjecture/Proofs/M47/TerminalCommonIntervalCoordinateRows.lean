import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCoordinateMetric
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCompactCapture
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalSmoothLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCommonInterval_actual_coordinate_rows
    {M : Type u} {N : Type v} {X : ℕ → Type w}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    [MetricSpace N] [LocallyCompactSpace N]
    [ChartedSpace E N] [IsManifold (𝓡 3) ∞ N]
    [∀ n, TopologicalSpace (X n)] [∀ n, ChartedSpace E (X n)]
    [∀ n, IsManifold (𝓡 3) ∞ (X n)]
    (h : ∀ n, RiemannianMetric 3 (X n))
    (e : ∀ n, PartialDiffeomorph (𝓡 3) (𝓡 3) M (X n) ∞)
    (f : ∀ n, PartialDiffeomorph (𝓡 3) (𝓡 3) N (X n) ∞)
    (d : M → N) (hd : Continuous d)
    (hsource : ∀ K : Set M, IsCompact K →
      ∀ᶠ n in atTop, K ⊆ ((e n).trans (f n).symm).source)
    (hconv : ∀ K : Set M, IsCompact K → TendstoUniformlyOn
      (fun n => (e n).trans (f n).symm) d atTop K)
    (a : PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞)
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) N E ∞)
    {U : Set E} (hUa : U ⊆ a.target)
    (hUb : MapsTo (fun x => d (a.symm x)) U b.source) :
    let A := fun n => ((a.symm.trans (e n)).trans (f n).symm).trans b
    (∀ x ∈ U, Tendsto (fun n => A n x) atTop (𝓝 (b (d (a.symm x))))) ∧
      LocallyEventuallyContDiff U (fun n => A n) ∧
      (∀ K : Set E, IsCompact K → K ⊆ U → ∃ L : Set E,
        IsCompact L ∧ L ⊆ b.target ∧ ∀ᶠ n in atTop, MapsTo (A n) K L) ∧
      ∀ K : Set E, IsCompact K → K ⊆ U → ∀ᶠ n in atTop,
        ∀ x ∈ K, ∀ v w : E,
          (h n).pullbackCoefficients (f n ∘ b.symm) (A n x)
              (fderiv ℝ (A n) x v) (fderiv ℝ (A n) x w) =
            (h n).pullbackCoefficients (e n ∘ a.symm) x v w := by
  let T := fun n => (e n).trans (f n).symm
  let A := fun n => ((a.symm.trans (e n)).trans (f n).symm).trans b
  have htail (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U) :
      ∃ L : Set N, IsCompact L ∧ L ⊆ b.source ∧
        ∀ᶠ n in atTop, K ⊆ (A n).source ∧ MapsTo (T n) (a.symm '' K) L := by
    have hKa : K ⊆ a.target := hKU.trans hUa
    have himage : IsCompact (a.symm '' K) := hK.image_of_continuousOn
      (a.toOpenPartialHomeomorph.continuousOn_invFun.mono hKa)
    have hdmap : MapsTo d (a.symm '' K) b.source := by
      rintro _ ⟨x, hx, rfl⟩
      exact hUb (hKU hx)
    obtain ⟨L, hL, hLb, hmap⟩ := terminalCommonInterval_compact_image_capture
      himage b.open_source hd.continuousOn hdmap (hconv _ himage)
    refine ⟨L, hL, hLb, ?_⟩
    filter_upwards [hsource _ himage, hmap] with n hn hm
    refine ⟨?_, hm⟩
    intro x hx
    have he := hn (mem_image_of_mem a.symm hx)
    exact ⟨⟨⟨hKa hx, he.1⟩, he.2⟩, hLb (hm (mem_image_of_mem a.symm hx))⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    have ht := (hconv {a.symm x} isCompact_singleton).tendsto_at
      (mem_singleton (a.symm x))
    have hb := b.toOpenPartialHomeomorph.continuousOn_toFun.continuousAt
      (b.open_source.mem_nhds (hUb hx))
    exact hb.tendsto.comp ht
  · intro K hK hKU
    obtain ⟨L, _hL, _hLb, hmap⟩ := htail K hK hKU
    filter_upwards [hmap] with n hn
    exact ⟨(A n).source, (A n).open_source, hn.1,
      contMDiffOn_iff_contDiffOn.mp (A n).contMDiffOn_toFun⟩
  · intro K hK hKU
    obtain ⟨L, hL, hLb, hmap⟩ := htail K hK hKU
    refine ⟨b '' L, hL.image_of_continuousOn
      (b.toOpenPartialHomeomorph.continuousOn_toFun.mono hLb), ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact b.map_source (hLb hx)
    · filter_upwards [hmap] with n hn x hx
      exact mem_image_of_mem b (hn.2 (mem_image_of_mem a.symm hx))
  · intro K hK hKU
    obtain ⟨L, _hL, _hLb, hmap⟩ := htail K hK hKU
    filter_upwards [hmap] with n hn x hx v w
    exact (terminalCommonInterval_actual_coordinate_metric (h n) (e n) (f n) a b).2
      x (hn.1 hx) v w

end PoincareConjecture.M47
