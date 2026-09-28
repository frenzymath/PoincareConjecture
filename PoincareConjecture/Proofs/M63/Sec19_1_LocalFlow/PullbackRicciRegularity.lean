import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PullbackMetricHessian
import PoincareConjecture.Proofs.M08.ChartConnectionVariation

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem flow_pullback_ricci_contDiffOn {a b : ℝ} (F : RicciFlow n M (Icc a b))
    {U : Set V} (hU : IsOpen U) {ρ : V → M}
    (hρ : ContMDiffOn 𝓘(ℝ, V) (𝓡 n) ∞ ρ U) :
    ContDiffOn ℝ ∞
      (fun z : (ℝ × V) × V => (F.connection z.1.1).ricci (ρ z.1.2)
        (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.1.2 z.2)
        (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.1.2 z.2)) ((Icc a b ×ˢ U) ×ˢ univ) := by
  have hab : a < b := by
    obtain ⟨s, hs, t, ht, hne⟩ := F.nontrivial
    by_contra! h
    apply hne
    linarith [hs.1, hs.2, ht.1, ht.2]
  have hC : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  let G : ℝ × (V × V) → ℝ := fun z => (F.metric z.1).inner (ρ z.2.1)
    (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.2.1 z.2.2)
    (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.2.1 z.2.2)
  let R : ℝ × (V × V) → ℝ := fun z => (F.connection z.1).ricci (ρ z.2.1)
    (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.2.1 z.2.2)
    (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.2.1 z.2.2)
  have hzero : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M => (0 : ℝ)) :=
    contMDiff_const
  have hmetric := (flow_pullback_metric_hessian_contDiffOn F hU hρ hzero).1
  have hpair : ContDiff ℝ ∞ (fun z : ℝ × (V × V) => ((z.1, z.2.1), z.2.2)) :=
    (contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd
  have hG : ContDiffOn ℝ ∞ G (Icc a b ×ˢ (U ×ˢ univ)) :=
    hmetric.comp hpair.contDiffOn (fun z hz => ⟨⟨hz.1, hz.2.1⟩, mem_univ _⟩)
  have hD := M08.timeWithinFDeriv_contDiffOn hC (hU.prod isOpen_univ) G hG
  have hR : ContDiffOn ℝ ∞ R (Icc a b ×ˢ (U ×ˢ univ)) := by
    apply ((contDiffOn_const (c := - (1 / 2 : ℝ))).mul hD).congr
    intro z hz
    have hd := (M08.hasDerivWithinAt_timeWithin G hG hz.1 hz.2).derivWithin (hC z.1 hz.1)
    have he := (F.equation z.1 hz.1 (ρ z.2.1)
      (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.2.1 z.2.2)
      (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.2.1 z.2.2)).derivWithin (hC z.1 hz.1)
    have hval := hd.symm.trans he
    change M08.timeWithinFDeriv (Icc a b) (U ×ˢ univ) G z = -2 * R z at hval
    change R z = (- (1 / 2 : ℝ)) * M08.timeWithinFDeriv (Icc a b) (U ×ˢ univ) G z
    linarith only [hval]
  have hinv : ContDiff ℝ ∞ (fun z : (ℝ × V) × V => (z.1.1, (z.1.2, z.2))) :=
    contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)
  exact hR.comp hinv.contDiffOn (fun z hz => ⟨hz.1.1, hz.1.2, mem_univ _⟩)

end PoincareConjecture.M63
