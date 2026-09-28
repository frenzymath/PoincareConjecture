import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryUniformTangentialQuotients
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTangentialHessian
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryLocalEmbedding












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

local instance m64InitialGain_bilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64InitialGain_bilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance m64InitialGain_trilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64InitialGain_trilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace





theorem m64WeightedMixedMetric_conformal_initial_gain
    (dirichlet : Fin n → Prop) {a : LoopPlane} {R : ℝ} (hR : 0 < R)
    (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (w : Fin 2 → ℝ) (V : Fin 2 → LoopPlane → E) (u : LoopPlane → E)
    {kappa mu C Lambda modulus : ℝ} (hk : 0 < kappa) (hmu : 0 < mu) (hC : 0 < C)
    (hw : ∀ i, mu ≤ w i ∧ w i ≤ Lambda)
    (hG : ∀ p ∈ ball a R ∩ {p : LoopPlane | 0 < p 1},
      ‖G (u p)‖ ≤ C ∧ ‖T (u p)‖ ≤ C ∧ ∀ v : E, kappa * ‖v‖ ^ 2 ≤ G (u p) v v)
    (hLip : ∀ p ∈ ball a R ∩ {p : LoopPlane | 0 < p 1},
      ∀ q ∈ ball a R ∩ {p : LoopPlane | 0 < p 1},
      ‖G (u p) - G (u q)‖ ≤ C * ‖u p - u q‖ ∧
      ‖T (u p) - T (u q)‖ ≤ C * ‖u p - u q‖)
    (hu : Continuous u) (huc : HasCompactSupport u) (hu0 : u a = 0)
    (hz : ∀ j, dirichlet j → ∀ p : LoopPlane, p 1 < 0 → u p j = 0)
    (hV : ∀ i, MemLp (V i) 2 volume)
    (hweak : ∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => u p j) univ)
    (hflux : ∀ j : Fin n, ∀ i : Fin 2,
      MemLp (fun p => w i * G (u p) (V i p) (EuclideanSpace.single j 1))
        2 (volume.restrict (ball a R ∩ {p : LoopPlane | 0 < p 1})))
    (hsource : ∀ j : Fin n, IntegrableOn (fun p =>
      -(∑ i : Fin 2, w i * T (u p) (EuclideanSpace.single j 1) (V i p) (V i p)) / 2)
      (ball a R ∩ {p : LoopPlane | 0 < p 1}))
    (heq : ∀ j : Fin n, ∀ phi : LoopPlane → ℝ,
      ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ ball a R →
      (dirichlet j → ∀ p : LoopPlane, p 1 = 0 → phi p = 0) →
      (∫ p, ∑ i : Fin 2, (ball a R ∩ {p : LoopPlane | 0 < p 1}).indicator
        (fun q => w i * G (u q) (V i q) (EuclideanSpace.single j 1)) p *
          fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p, (ball a R ∩ {p : LoopPlane | 0 < p 1}).indicator
          (fun q => -(∑ i : Fin 2,
            w i * T (u q) (EuclideanSpace.single j 1) (V i q) (V i q)) / 2) p * phi p)
    (hconf : ∀ᵐ p ∂volume.restrict (ball a R ∩ {p : LoopPlane | 0 < p 1}),
      G (u p) (V 1 p) (V 1 p) = modulus ^ 2 * G (u p) (V 0 p) (V 0 p)) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∃ Q : Fin 2 → LoopPlane → E,
      (∀ i, MemLp (Q i) 2 (volume.restrict (ball a r ∩ {p : LoopPlane | 0 < p 1}))) ∧
      (∀ i j, HasWeakPartialDeriv 0 (fun p => Q i p j) (fun p => V i p j)
        (ball a r ∩ {p : LoopPlane | 0 < p 1})) ∧
      ∀ q : ℝ, 1 ≤ q → ∀ i : Fin 2, MemLp (V i) (ENNReal.ofReal q)
        (volume.restrict (ball a r ∩ {p : LoopPlane | 0 < p 1})) := by
  obtain ⟨s, hs, hsR, h0, hh0, D, hD⟩ :=
    m64WeightedMixedMetric_uniform_tangential_quotients dirichlet hR G T w V u hk hmu hC
      hw hG hLip hu huc hu0 hz hV hweak hflux hsource heq
  let O := ball a s ∩ {p : LoopPlane | 0 < p 1}
  have hO : IsOpen O := isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous)
  have hc : IsCompact (closure O) := (isCompact_closedBall a s).of_isClosed_subset
    isClosed_closure (closure_minimal
      (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall)
  obtain ⟨Q, hQ, hQw, hH1⟩ := m64TangentialHessian_of_integral_diffQuot_bound hO hc hV
    (fun i j => (hweak i j).restrict hO (subset_univ _)) hh0 (fun _ => D) hD
  have hsmall : ball a (s / 2) ∩ {p : LoopPlane | 0 < p 1} ⊆ O :=
    inter_subset_inter_left _ (ball_subset_ball (half_le_self hs.le))
  have hsmallOpen : IsOpen (ball a (s / 2) ∩ {p : LoopPlane | 0 < p 1}) :=
    isOpen_ball.inter (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous)
  have hsub : O ⊆ ball a R ∩ {p : LoopPlane | 0 < p 1} :=
    inter_subset_inter_left _ (ball_subset_ball hsR.le)
  have hdata : ∀ᵐ p ∂volume.restrict O, ‖G (u p)‖ ≤ C ∧
      kappa * ‖V 1 p‖ ^ 2 ≤ G (u p) (V 1 p) (V 1 p) ∧
      G (u p) (V 1 p) (V 1 p) = modulus ^ 2 * G (u p) (V 0 p) (V 0 p) := by
    filter_upwards [ae_mono (Measure.restrict_mono hsub le_rfl) hconf,
      ae_restrict_mem hO.measurableSet] with p hp hpO
    exact ⟨(hG p (hsub hpO)).1, (hG p (hsub hpO)).2.2 _, hp⟩
  refine ⟨s / 2, half_pos hs, (half_lt_self hs).trans hsR, Q,
    fun i => (hQ i).mono_measure (Measure.restrict_mono hsmall le_rfl),
    fun i j => (hQw i j).restrict hsmallOpen hsmall, ?_⟩
  intro q hq
  exact m64HalfBall_conformal_columns_memLp (G ∘ u) (half_lt_self hs) hk hH1
    ((hV 1).restrict O).aestronglyMeasurable hdata hq

end PoincareConjecture
