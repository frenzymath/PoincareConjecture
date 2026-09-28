import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseGrowth
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

omit [T2Space M] in

theorem m64ObservedMetric_coercivity_of_diagonal
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (w : TangentSpace (𝓡 n) q),
      B q (mfderiv (𝓡 n) (𝓡 m) e q w) (mfderiv (𝓡 n) (𝓡 m) e q w) = g.inner q w w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨D, hD, hbound⟩ := M60.exists_uniform_mfderiv_bound g e he
  refine ⟨D ^ 2, sq_nonneg D, ?_⟩
  rintro q v ⟨w, rfl⟩
  have hnorm : ‖(show E from mfderiv (𝓡 n) (𝓡 m) e q w)‖ ≤ D * ‖w‖ := by
    rw [← norm_tangentSpace_vectorSpace (x := e q)]
    exact ((mfderiv (𝓡 n) (𝓡 m) e q).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (hbound q) (norm_nonneg w))
  have hnormsq : ‖w‖ ^ 2 = g.inner q w w := (real_inner_self_eq_norm_sq w).symm
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD (norm_nonneg w))).mpr hnorm
  simpa only [mul_pow, hnormsq, hdiag q w] using hs

namespace M64

variable {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

theorem auxiliaryCircle_free_phase_continuous_minimum
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    {e : Q.charts.Point → E}
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := (n + 1) + 1) e)
    {R : E →L[ℝ] LoopPlane} (hR : ∀ q, R (e q) = planarCircleObservation q.1.2)
    {c0 c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {D : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e R c0 c1 H0 H1 (curvePeriod / circumference) D)
    (g : RiemannianMetric ((n + 1) + 1) Q.charts.Point)
    (B : Q.charts.Point → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hpos : ∀ q v, 0 ≤ B q v v)
    (hdiag : ∀ (q : Q.charts.Point) (w : TangentSpace (𝓡 ((n + 1) + 1)) q),
      B q (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q w)
        (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q w) = g.inner q w w)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hminimum : ∀ s : ℝ, 0 < s →
      ∀ W : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
          e R c0 c1 H0 H1 (curvePeriod / circumference) D,
        A.annulus.weightedEnergy B modulus ≤ W.annulus.weightedEnergy B s) :
    ∃ W : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
        e R c0 c1 H0 H1 (curvePeriod / circumference) D,
      W.label0 = A.label0 ∧ W.label1 = A.label1 ∧ ContinuousOn W.annulus.map S ∧
      W.annulus.map =ᵐ[mu] A.annulus.map ∧ W.annulus.column = A.annulus.column ∧
      W.phase = A.phase ∧ W.phaseColumn = A.phaseColumn ∧
      (∀ (G : Q.charts.Point → E →L[ℝ] E →L[ℝ] ℝ) (s : ℝ),
        W.annulus.weightedEnergy G s = A.annulus.weightedEnergy G s) ∧
      ∀ s : ℝ, 0 < s →
        ∀ V : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
            e R c0 c1 H0 H1 (curvePeriod / circumference) D,
          W.annulus.weightedEnergy B modulus ≤ V.annulus.weightedEnergy B s := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  obtain ⟨C, hC, hcoercive⟩ := m64ObservedMetric_coercivity_of_diagonal g e he B hdiag
  have hgrowth (a : LoopPlane) (ha : a ∈ S) :=
    auxiliaryCircle_free_phase_column_power_growth P Q he hei hread hR A g B hB hpos
      hC hcoercive hmodulus (hminimum modulus hmodulus) a ha
  obtain ⟨U, hU, hUae⟩ := m64Morrey_local_representative A.annulus.observed_memLp
    (fun i => Lp.memLp (A.annulus.column i)) A.annulus.weak_partial (by
      intro a ha
      obtain ⟨rho, hrho, hsub, K, hK, beta, hbeta, hg⟩ := hgrowth a ha
      exact ⟨rho, hrho, hsub, K, hK, beta, hbeta, fun i b hb r hr => hg b hb r hr i⟩)
  obtain ⟨f, hf, hfae, -⟩ :=
    m64ClosedEmbedding_continuous_representative hei isOpen_interior A.annulus.map U hU hUae
  obtain ⟨V, hmap, hcolumn, -⟩ := A.annulus.with_map_ae f hfae
  have hVae : V.map =ᵐ[mu] A.annulus.map := hmap ▸ hfae
  have hobs : (fun p => R (e (V.map p))) =ᵐ[mu]
      fun p => angularPoint ((curvePeriod / circumference) * A.phase p) := by
    filter_upwards [hVae, A.phase_observation] with p hp hphase
    simpa only [hp] using hphase
  let W : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e R c0 c1 H0 H1 (curvePeriod / circumference) D :=
    { A with annulus := V, phase_observation := hobs }
  have henergy := A.annulus.weightedEnergy_eq_of_map_ae V hVae hcolumn
  refine ⟨W, rfl, rfl, hmap ▸ hf, hVae, hcolumn, rfl, rfl, henergy, ?_⟩
  intro s hs Z
  change V.weightedEnergy B modulus ≤ _
  rw [henergy]
  exact hminimum s hs Z

end M64
end PoincareConjecture
