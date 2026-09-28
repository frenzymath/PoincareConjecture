import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreePhaseConfinement
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseMinimum









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Topology
open scoped ContDiff Manifold

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin m)




theorem weightedEnergy_attained_positive
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := n) e)
    (R : E →L[ℝ] LoopPlane) (c0 c1 : ℝ → M) (hc0 : Continuous c0) (hc1 : Continuous c1)
    (H0 H1 : ℝ ≃o ℝ) {frequency D : ℝ} (hf : frequency ≠ 0) (hD : D ≠ 0)
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D)
    (T : E →L[ℝ] ℝ) {v0 v1 : ℝ} (hne : v0 ≠ v1)
    (h0 : ∀ x, T (e (c0 x)) = v0) (h1 : ∀ x, T (e (c1 x)) = v1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) (hsymm : ∀ q v w, B q v w = B q w v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v)
    (A0 : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 frequency D) :
    ∃ r : ℝ, 0 < r ∧
      ∃ L : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 frequency D,
        ∀ s : ℝ, 0 < s →
          ∀ A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 frequency D,
            L.annulus.weightedEnergy B r ≤ A.annulus.weightedEnergy B s := by
  let cap := A0.annulus.weightedEnergy B 1 + 1
  have hcap : 0 < cap := by
    have hn := A0.annulus.weightedEnergy_nonneg B hpos zero_le_one
    dsimp only [cap]
    linarith
  obtain ⟨lo, hi, hlo, hlohi, hconfined⟩ :=
    exists_strict_modulus_interval (R := R) hf hD hH0 hH1
      (he.continuous.comp hc0) (he.continuous.comp hc1) T hne h0 h1
      B hB hei.isEmbedding hb hpos hcoercive hcap
  have hseed : A0.annulus.weightedEnergy B 1 ≤ cap := by
    dsimp only [cap]
    linarith
  have hone := hconfined A0 1 one_pos hseed
  obtain ⟨r, hr, L, hminimum⟩ := weightedEnergy_attained e he hei hread
    R c0 c1 hc0 hc1 H0 H1 hf hH0 hH1 B hB hK hb hpos hsymm hC hcoercive
    hlo hlohi.le A0
  have hrpos : 0 < r := hlo.trans_le hr.1
  have hbelow : L.annulus.weightedEnergy B r ≤ cap :=
    (hminimum 1 ⟨hone.1.le, hone.2.le⟩ A0).trans hseed
  have hinterior := hconfined L r hrpos hbelow
  refine ⟨r, hlo.trans hinterior.1, L, ?_⟩
  intro s hs A
  by_cases hA : A.annulus.weightedEnergy B s ≤ cap
  · have hsI := hconfined A s hs hA
    exact hminimum s ⟨hsI.1.le, hsI.2.le⟩ A
  · exact hbelow.trans (lt_of_not_ge hA).le

end PoincareConjecture.M64FreeWeakPhaseAnnulus
