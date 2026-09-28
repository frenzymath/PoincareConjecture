import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ObservedLowerHolder
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LowerContinuousTrace
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakRepresentative










noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "nu" => volume.restrict (Icc (0 : ℝ) curvePeriod)

local instance : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr
  ((measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top).ne




theorem lower_representative_trace
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.annulus.map S)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + D)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + D)
    {U : LoopPlane → E} {O : Set LoopPlane} (hO : IsOpen O)
    (hsub : O ⊆ m64AnnulusLowerDomain) (hU : ContinuousOn U O)
    (hae : U =ᵐ[volume.restrict O] A.annulus.lowerReflectedValue) :
    EqOn U (e ∘ A.annulus.map) (O ∩ S) ∧
      ∀ x, annulusPoint x 0 ∈ O → U (annulusPoint x 0) = e (c0 (A.label0 x)) := by
  have hf : ContinuousOn (e ∘ A.annulus.map) S :=
    he.continuous.comp_continuousOn hA.continuousOn
  have hobs : U =ᵐ[volume.restrict (O ∩ S)] (e ∘ A.annulus.map) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hae,
      ae_restrict_mem (hO.inter isOpen_interior).measurableSet] with p hp hpOS
    have hn : ¬p 1 < 0 := not_lt.mpr
      (((m64AnnulusInterior_coordinates p).mp hpOS.2).2.2.1.le)
    simpa only [M64ObservedWeakAnnulus.lowerReflectedValue, m64AnnulusLowerExtend,
      if_neg hn] using hp
  have h0 : Continuous (e ∘ (c0 ∘ A.label0)) :=
    hc0.comp (A.labels_continuous hH0 hH1).1
  have h1 : Continuous (e ∘ (c1 ∘ A.label1)) :=
    hc1.comp (A.labels_continuous hH0 hH1).2
  have hpoint := A.raw_vertical_trace_pointwise he hA h0.integrableOn_Icc h1.integrableOn_Icc
  refine ⟨Measure.eqOn_open_of_ae_eq hobs (hO.inter isOpen_interior)
    (hU.mono inter_subset_left) (hf.mono inter_subset_right), ?_⟩
  exact m64Lower_continuous_trace hO hsub hU hf h0 hobs
    ((Lp.memLp (A.annulus.column 1)).integrable (by norm_num))
    (hpoint.mono fun x hx s hs => (hx s hs).1)




theorem lower_target_holder_representative
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.annulus.map S)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + D)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + D)
    {x0 rho K beta : ℝ} (hrho : 0 < rho)
    (hsub : closedBall (annulusPoint x0 0) (2 * rho) ⊆ m64AnnulusLowerDomain)
    (hK : 0 ≤ K) (hbeta : 0 < beta)
    (henergy : ∀ b ∈ closedBall (annulusPoint x0 0) rho, ∀ r ∈ Ioc (0 : ℝ) rho,
      (∫ p in closedBall b r ∩ S, ∑ i : Fin 2, ‖A.annulus.column i p‖ ^ 2) ≤
        K * r ^ beta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ F : LoopPlane → M,
      ContinuousOn F (ball (annulusPoint x0 0) (rho / 2)) ∧
      EqOn F A.annulus.map (ball (annulusPoint x0 0) (rho / 2) ∩ S) ∧
      (∀ x, annulusPoint x 0 ∈ ball (annulusPoint x0 0) (rho / 2) →
        F (annulusPoint x 0) = c0 (A.label0 x)) ∧
      ∀ x ∈ ball (annulusPoint x0 0) (rho / 2),
        ∀ y ∈ ball (annulusPoint x0 0) (rho / 2),
        dist (e (F x)) (e (F y)) ≤ C * (dist x y) ^ (beta / 2) := by
  obtain ⟨C, hC, U, hU, hUae, hholder⟩ :=
    A.annulus.lower_holder_representative hrho hsub hK hbeta henergy
  have hball : ball (annulusPoint x0 0) (rho / 2) ⊆ m64AnnulusLowerDomain :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall
      (by linarith : rho / 2 ≤ 2 * rho))).trans hsub
  obtain ⟨hinterior, htrace⟩ := A.lower_representative_trace he hA hc0 hc1 hH0 hH1
    isOpen_ball hball (hU.mono ball_subset_closedBall) hUae
  let raw := m64AnnulusLowerExtend (A.annulus.map ∘ m64AnnulusRadialFlip) A.annulus.map
  have hraw : e ∘ raw = A.annulus.lowerReflectedValue := by
    funext p
    dsimp only [raw, Function.comp_apply, M64ObservedWeakAnnulus.lowerReflectedValue,
      m64AnnulusLowerExtend]
    split_ifs <;> rfl
  obtain ⟨F, hF, -, hFe⟩ := m64ClosedEmbedding_continuous_representative hei isOpen_ball
    raw U (hU.mono ball_subset_closedBall) (hraw ▸ hUae)
  refine ⟨C, hC, F, hF, ?_, ?_, ?_⟩
  · intro p hp
    exact hei.injective ((hFe hp.1).trans (hinterior hp))
  · intro x hx
    exact hei.injective ((hFe hx).trans (htrace x hx))
  · intro x hx y hy
    change dist ((e ∘ F) x) ((e ∘ F) y) ≤ _
    rw [hFe hx, hFe hy]
    exact hholder x (ball_subset_closedBall hx) y (ball_subset_closedBall hy)

end PoincareConjecture.M64FreeWeakPhaseAnnulus
