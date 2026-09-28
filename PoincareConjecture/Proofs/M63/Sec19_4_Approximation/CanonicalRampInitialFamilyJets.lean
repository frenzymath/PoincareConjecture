import PoincareConjecture.Definitions.M63Family
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.CanonicalRampRegularity
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ContinuousDependenceEmbeddedJets
import PoincareConjecture.Proofs.M63.Mathlib.CompactEmbeddedRetraction
import PoincareConjecture.Proofs.M58.Sec18_4_LoopLength
import PoincareConjecture.Proofs.M58.Sec18_4_LoopTopology
import Mathlib.Geometry.Manifold.WhitneyEmbedding










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M63

open Proofs.M58




theorem continuous_canonicalRamp_embedded_initial_jets
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    {Gamma : C(LoopTwoSphere, C1FreeLoopSpace (M := M))} {zeta : ℝ}
    (A : M63RawApproximation F Gamma zeta) {circumference : ℝ}
    (P : M62.CircleProductData F circumference)
    {ι : Type v} [Fintype ι]
    {e : P.charts.Point → EuclideanSpace ℝ ι}
    (he : ContMDiff (𝓡 (3 + 1)) 𝓘(ℝ, EuclideanSpace ℝ ι) ∞ e) :
    let gamma : LoopTwoSphere → ℝ → P.charts.Point :=
      fun z => m63CanonicalRamp P (periodicFreeLoop (A.family z))
    Continuous (fun z : LoopTwoSphere × ℝ => e (gamma z.1 z.2)) ∧
      Continuous (fun z : LoopTwoSphere × ℝ =>
        deriv (fun y => e (gamma z.1 y)) z.2) ∧
      Continuous (fun z : LoopTwoSphere × ℝ =>
        deriv (deriv (fun y => e (gamma z.1 y))) z.2) := by
  classical
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let z0 : LoopTwoSphere := ⟨EuclideanSpace.single (0 : Fin 3) 1, by simp⟩
  let : Nonempty M := ⟨periodicFreeLoop (A.family z0) 0⟩
  have hab : a < b := by
    obtain ⟨s, hs, t, ht, hne⟩ := F.nontrivial
    by_contra! h
    apply hne
    linarith [hs.1, hs.2, ht.1, ht.2]
  obtain ⟨N, i, hi, hiClosed, hiInjective⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓡 3) (M := M)
  obtain ⟨U, rho, hU, hiU, hrho, hrhoi, _hmin, _hunique⟩ :=
    exists_smooth_compact_embedded_retraction i hiClosed hi hiInjective
  let V := EuclideanSpace ℝ (Fin N)
  let W := EuclideanSpace ℝ ι
  let f : LoopTwoSphere → ℝ → V := fun z x => i (periodicFreeLoop (A.family z) x)
  let gamma : LoopTwoSphere → ℝ → P.charts.Point :=
    fun z => m63CanonicalRamp P (periodicFreeLoop (A.family z))
  have htheta : Continuous (fun x : ℝ =>
      (⟨angularPoint x, norm_angularPoint x⟩ : LoopCircle)) :=
    contDiff_angularPoint.continuous.subtype_mk _
  have hbase : Continuous (fun z : LoopTwoSphere × ℝ =>
      periodicFreeLoop (A.family z.1) z.2) := by
    apply ((continuous_loop_eval (M := M)).comp
      ((A.family.continuous.comp continuous_fst).prodMk
        (htheta.comp continuous_snd))).congr
    intro z
    exact ((A.family z.1).boundary ⟨angularPoint z.2, norm_angularPoint z.2⟩).symm
  obtain ⟨hspace, hf0, hf1, hf2⟩ :=
    continuous_embedded_initial_jets F ⟨le_rfl, hab.le⟩
      (fun z => periodicFreeLoop (A.family z)) hbase
      A.first_jet_continuous A.second_jet_continuous
      (fun z => (A.angular_smooth z).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hi hU hiU hrho hrhoi
  let D : Set (V × ℝ) := U ×ˢ univ
  have hD : IsOpen D := hU.prod isOpen_univ
  let Phi : V × ℝ → W := fun y =>
    e (rho y.1, P.circle.quotient (circumference * y.2 / curvePeriod))
  have hPhi : ContDiffOn ℝ ∞ Phi D := by
    let := P.charts.chartedSpace
    let := P.circle.chartedSpace
    have hfst : ContMDiff 𝓘(ℝ, V × ℝ) 𝓘(ℝ, V) ∞
        (Prod.fst : V × ℝ → V) := contDiff_fst.contMDiff
    have hbaseMap : ContMDiffOn 𝓘(ℝ, V × ℝ) (𝓡 3) ∞ (fun y => rho y.1) D :=
      hrho.comp hfst.contMDiffOn (fun _ hy => hy.1)
    have hlinear : ContMDiff 𝓘(ℝ, V × ℝ) 𝓘(ℝ, ℝ) ∞
        (fun y : V × ℝ => circumference * y.2 / curvePeriod) :=
      contMDiff_iff_contDiff.mpr ((contDiff_const.mul contDiff_snd).div_const _)
    have hgraph : ContMDiffOn 𝓘(ℝ, V × ℝ) (𝓡 (3 + 1)) ∞
        (fun y : V × ℝ =>
          (rho y.1, P.circle.quotient (circumference * y.2 / curvePeriod))) D :=
      P.charts.from_product_smooth.comp_contMDiffOn
        (hbaseMap.prodMk (P.circle.quotient_smooth.comp hlinear).contMDiffOn)
    exact (he.comp_contMDiffOn hgraph).contDiffOn
  let r : LoopTwoSphere → ℝ → V × ℝ := fun z x => (f z x, x)
  let p : LoopTwoSphere → ℝ → V × ℝ := fun z x => (deriv (f z) x, 1)
  let q : LoopTwoSphere → ℝ → V × ℝ := fun z x => (deriv (deriv (f z)) x, 0)
  have hrep (z : LoopTwoSphere) (x : ℝ) : e (gamma z x) = Phi (r z x) := by
    dsimp only [Phi, r, f, gamma, m63CanonicalRamp]
    rw [hrhoi]
  have hmem (z : LoopTwoSphere × ℝ) : r z.1 z.2 ∈ D :=
    ⟨hiU (mem_range_self _), mem_univ _⟩
  have hr : Continuous (fun z : LoopTwoSphere × ℝ => r z.1 z.2) :=
    hf0.prodMk continuous_snd
  have hp : Continuous (fun z : LoopTwoSphere × ℝ => p z.1 z.2) :=
    hf1.prodMk continuous_const
  have hq : Continuous (fun z : LoopTwoSphere × ℝ => q z.1 z.2) :=
    hf2.prodMk continuous_const
  have hrd (z : LoopTwoSphere) (x : ℝ) : HasDerivAt (r z) (p z x) x :=
    (((hspace z).differentiable (by norm_num) x).hasDerivAt).prodMk (hasDerivAt_id x)
  have hpd (z : LoopTwoSphere) (x : ℝ) : HasDerivAt (p z) (q z x) x :=
    ((((hspace z).deriv' (n := 1)).differentiable (by norm_num) x).hasDerivAt).prodMk
      (hasDerivAt_const x (1 : ℝ))
  have hDPhi := hPhi.fderiv_of_isOpen hD (m := ∞) (by simp)
  have hDDPhi := hDPhi.fderiv_of_isOpen hD (m := ∞) (by simp)
  have hfirst (z : LoopTwoSphere) (x : ℝ) :
      deriv (fun y => e (gamma z y)) x = fderiv ℝ Phi (r z x) (p z x) := by
    rw [show (fun y => e (gamma z y)) = Phi ∘ r z from funext (hrep z)]
    exact (((hPhi.contDiffAt (hD.mem_nhds (hmem (z, x)))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt x (hrd z x)).deriv
  have hsecond (z : LoopTwoSphere) (x : ℝ) :
      deriv (deriv (fun y => e (gamma z y))) x =
        fderiv ℝ (fderiv ℝ Phi) (r z x) (p z x) (p z x) +
          fderiv ℝ Phi (r z x) (q z x) := by
    rw [show deriv (fun y => e (gamma z y)) =
      (fun y => fderiv ℝ Phi (r z y) (p z y)) from funext (hfirst z)]
    have hd : HasDerivAt (fun y => fderiv ℝ Phi (r z y))
        (fderiv ℝ (fderiv ℝ Phi) (r z x) (p z x)) x :=
      (((hDPhi.contDiffAt (hD.mem_nhds (hmem (z, x)))).differentiableAt
        (by simp)).hasFDerivAt.comp_hasDerivAt x (hrd z x))
    exact (hd.clm_apply (hpd z x)).deriv
  have hDcomp : Continuous (fun z : LoopTwoSphere × ℝ => fderiv ℝ Phi (r z.1 z.2)) :=
    hDPhi.continuousOn.comp_continuous hr hmem
  have hDDcomp : Continuous
      (fun z : LoopTwoSphere × ℝ => fderiv ℝ (fderiv ℝ Phi) (r z.1 z.2)) :=
    hDDPhi.continuousOn.comp_continuous hr hmem
  exact ⟨(hPhi.continuousOn.comp_continuous hr hmem).congr (fun z => (hrep z.1 z.2).symm),
    (hDcomp.clm_apply hp).congr (fun z => (hfirst z.1 z.2).symm),
    (((hDDcomp.clm_apply hp).clm_apply hp).add (hDcomp.clm_apply hq)).congr
      (fun z => (hsecond z.1 z.2).symm)⟩

end PoincareConjecture.M63
