import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.SupportedRectangleAdmission
import PoincareConjecture.Proofs.M60.Mathlib.SupportedChartVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

omit [T2Space M] in

theorem m64SupportedChartVariation_eq_of_notMem_tsupport
    (A : M64Annulus g c0 c1) (b : M) {U : Set LoopPlane}
    (hfU : MapsTo A.map U (chartAt (EuclideanSpace ℝ (Fin n)) b).source)
    (V : LoopPlane → EuclideanSpace ℝ (Fin n)) (s : ℝ) {p : LoopPlane}
    (hp : p ∉ tsupport V) :
    M60.supportedChartVariation (chartAt (EuclideanSpace ℝ (Fin n)) b)
      U A.map V (s, p) = A.map p := by
  apply M40.chartPerturb_eq_of_zero (chartAt (EuclideanSpace ℝ (Fin n)) b)
    (Prod.snd ⁻¹' U) (A.map ∘ Prod.snd)
    (fun q : ℝ × LoopPlane => q.1 • V q.2) (fun _ hq => hfU hq)
  simp only [image_eq_zero_of_notMem_tsupport hp, smul_zero]

theorem m64SupportedChartVariation_exists_admissible_interval
    (A : M64Annulus g c0 c1) (b : M) {U : Set LoopPlane}
    (hU : IsOpen U) (hUinside : U ⊆ m64AnnulusInterior)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map U)
    (hfU : MapsTo A.map U (chartAt (EuclideanSpace ℝ (Fin n)) b).source)
    (V : LoopPlane → EuclideanSpace ℝ (Fin n)) (hV : ContDiff ℝ ∞ V)
    (hcompact : HasCompactSupport V) (hsupport : tsupport V ⊆ U) :
    let c := chartAt (EuclideanSpace ℝ (Fin n)) b
    let v := M60.supportedChartVariation c U A.map V
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
        (Ioo (-epsilon) epsilon ×ˢ U) ∧
      (∀ s ∈ Ioo (-epsilon) epsilon, ∀ z ∈ U,
        v (s, z) ∈ c.source ∧ c (v (s, z)) = c (A.map z) + s • V z) ∧
      ∀ s ∈ Ioo (-epsilon) epsilon,
        ∃ B : M64Annulus g c0 c1, EqOn B.map (fun p => v (s, p)) m64AnnulusDomain := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) b
  let v := M60.supportedChartVariation c U A.map V
  obtain ⟨epsilon, hepsilon, hrange⟩ := M60.exists_supportedChartVariation_interval
    c hU hf.continuousOn hV.continuous hcompact hsupport hfU
  have hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U) := by
    intro q hq
    have hbase : ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞
        (A.map ∘ Prod.snd) q :=
      (hf.contMDiffAt (hU.mem_nhds hq.2)).comp q
        contDiff_snd.contMDiff.contMDiffAt
    have hcoord : ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane)
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (c ∘ (A.map ∘ Prod.snd)) q :=
      ((contMDiffOn_chart (A.map q.2) (hfU hq.2)).contMDiffAt
        (c.open_source.mem_nhds (hfU hq.2))).comp q hbase
    have hdelta : ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane)
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (fun p : ℝ × LoopPlane => p.1 • V p.2) q :=
      (contDiff_fst.smul (hV.comp contDiff_snd)).contMDiff.contMDiffAt
    exact (M40.contMDiffAt_chartPerturb_of_mem c
      (hU.preimage continuous_snd) hq.2 (hcoord.add hdelta)
      contMDiffOn_chart_symm (hrange q.1 hq.1 q.2 hq.2)).contMDiffWithinAt
  refine ⟨epsilon, hepsilon, hv, ?_, ?_⟩
  · intro s hs z hz
    change v (s, z) ∈ c.source ∧ c (v (s, z)) = c (A.map z) + s • V z
    rw [show v (s, z) = c.symm (c (A.map z) + s • V z) from
      M60.supportedChartVariation_of_mem c U A.map V s hz]
    exact ⟨c.map_target (hrange s hs z hz), c.right_inv (hrange s hs z hz)⟩
  · intro s hs
    apply m64Annulus_exists_eqOn_of_supported_smooth_modification
      (f := fun p => v (s, p)) A hU hcompact
      hsupport (hsupport.trans hUinside)
    · intro p hp
      have hvp := hv.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds
        (show (s, p) ∈ Ioo (-epsilon) epsilon ×ˢ U from ⟨hs, hp⟩))
      exact ((hvp.comp p (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt).of_le
        (m := 1) (by simp)).contMDiffWithinAt
    · intro p hp
      exact m64SupportedChartVariation_eq_of_notMem_tsupport A b hfU V s hp

end PoincareConjecture
