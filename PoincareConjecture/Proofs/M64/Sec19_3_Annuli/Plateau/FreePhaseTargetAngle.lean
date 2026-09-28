import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.OriginalCircleObservation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

theorem auxiliaryCircle_originalPhase_local
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (q : Q.charts.Point) :
    ∃ (U : Set Q.charts.Point) (beta : Q.charts.Point → ℝ),
      IsOpen U ∧ q ∈ U ∧ ContMDiffOn (𝓡 ((n + 1) + 1)) 𝓘(ℝ, ℝ) ∞ beta U ∧
      ∀ y ∈ U, P.circle.quotient (beta y) = y.1.2 := by
  let := Q.charts.chartedSpace
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  let pi : Q.charts.Point → P.circle.Point := fun y => y.1.2
  have hpi : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 1) ∞ pi :=
    (contMDiff_snd.comp P.charts.to_product_smooth).comp
      (contMDiff_fst.comp Q.charts.to_product_smooth)
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective (pi q)
  let hlocal := P.circle.quotient_local_diffeomorph s
  let sigma := hlocal.localInverse
  let U := pi ⁻¹' sigma.source
  let beta := sigma ∘ pi
  have hq : pi q ∈ sigma.source := by
    rw [← hs]
    exact hlocal.localInverse_mem_source
  refine ⟨U, beta, sigma.open_source.preimage hpi.continuous, hq, ?_, ?_⟩
  · intro y hy
    exact (((hlocal.contmdiffOn_localInverse (pi y) hy).contMDiffAt
      (sigma.open_source.mem_nhds hy)).comp y (hpi y)).contMDiffWithinAt
  · intro y hy
    exact hlocal.localInverse_right_inv hy

end PoincareConjecture.M64
