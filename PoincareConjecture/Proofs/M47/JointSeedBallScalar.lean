import PoincareConjecture.Proofs.M47.JointSeedPhysical
import PoincareConjecture.Proofs.M47.JointSeedForward
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_SpatialBall
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.Regularity
import PoincareConjecture.Proofs.M35.Thm12_28.CapScalarEstimates











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



theorem jointSeed_reference_low_point_gap
    (P : M47ScalarPersistencePredecessors.{u}) [CompactSpace M]
    {J : Set ℝ} (F : RicciFlow 3 M J) {s t C L : ℝ} (q z : M)
    (hst : s ≤ t) (hJ : Icc s t ⊆ J) (hC : 1 ≤ C)
    (hscalar : ∀ p : M, 0 ≤ (F.connection s).scalarCurvature p)
    (hterminal : C * (F.connection t).scalarCurvature q ≤ L)
    (hhigh : L < (F.connection s).scalarCurvature z) :
    ∃ p : M, (C / 6) * (F.connection s).scalarCurvature p ≤
      (F.connection s).scalarCurvature z := by
  obtain ⟨p, _hp, hpScalar⟩ := exists_earlier_component_scalar_le P F (U := univ)
    isCompact_univ isOpen_univ hst hJ (mem_univ q)
  have hCpos : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans hC
  refine ⟨p, ?_⟩
  calc
    _ ≤ C * (F.connection s).scalarCurvature p :=
      mul_le_mul_of_nonneg_right (by linarith) (hscalar p)
    _ ≤ C * (F.connection t).scalarCurvature q :=
      mul_le_mul_of_nonneg_left hpScalar hCpos
    _ ≤ L := hterminal
    _ ≤ _ := hhigh.le



theorem jointSeed_physical_reference_low_point_gap
    (P : M47ScalarPersistencePredecessors.{u}) [CompactSpace M]
    {J : Set ℝ} (G : RicciFlow 3 M J)
    (F : SurgeryFlowData.{u}) {s t C L : ℝ} (q z : M)
    (phi : M → (F.slice s).carrier)
    (himage : ∀ p : M, phi p ∈ connectedComponent (phi z))
    (hread : ∀ p : M, (G.connection s).scalarCurvature p =
      (F.connection s).scalarCurvature (phi p))
    (hst : s ≤ t) (hJ : Icc s t ⊆ J) (hC : 1 ≤ C)
    (hscalar : ∀ p : M, 0 ≤ (G.connection s).scalarCurvature p)
    (hterminal : C * (G.connection t).scalarCurvature q ≤ L)
    (hhigh : L < (G.connection s).scalarCurvature z) :
    ∃ p ∈ connectedComponent (phi z),
      (C / 6) * (F.connection s).scalarCurvature p ≤
        (F.connection s).scalarCurvature (phi z) := by
  obtain ⟨p, hp⟩ := jointSeed_reference_low_point_gap P G q z
    hst hJ hC hscalar hterminal hhigh
  refine ⟨phi p, himage p, ?_⟩
  simpa only [hread] using hp



theorem jointSeed_scalar_le_on_closure_birth_ball
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {A L r : ℝ} (hA : 0 < A) (hL : 0 < L) (q : M)
    (hr : r < (Real.sqrt (2 * L))⁻¹ / (8 * A))
    (hcenter : D.scalarCurvature q ≤ 2 * L)
    (hgradient : ∀ z : M, 2 * L ≤ D.scalarCurvature z →
      scalarGradientNorm g D z ≤ A * D.scalarCurvature z ^ (3 / 2 : ℝ)) :
    ∀ z ∈ closure (g.ball q r), D.scalarCurvature z ≤ 4 * L := by
  have hsqrt : 0 < (Real.sqrt (2 * L))⁻¹ := by positivity
  have hsq : ((Real.sqrt (2 * L))⁻¹)⁻¹ ^ 2 = 2 * L := by
    rw [inv_inv, Real.sq_sqrt (by positivity : 0 ≤ 2 * L)]
  have hball := Proofs.M46.scalar_le_two_inv_sq_on_ball g D
    (M34.contMDiff_scalarCurvature D) hA hsqrt q
    (by simpa only [hsq] using hcenter) (fun z _hz hhigh v hv =>
      (D.abs_scalar_directional_le_scalarGradientNorm z v hv).trans
        (hgradient z (by simpa only [hsq] using hhigh)))
  have hsubset : g.ball q r ⊆ {z | D.scalarCurvature z ≤ 4 * L} := by
    intro z hz
    have hzbig : z ∈ g.ball q ((Real.sqrt (2 * L))⁻¹ / (8 * A)) :=
      lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal hr.le)
    have h := hball z hzbig
    rw [hsq] at h
    exact h.trans_eq (by ring)
  exact closure_minimal hsubset
    (isClosed_le (M34.contMDiff_scalarCurvature D).continuous continuous_const)




theorem jointSeed_early_ball_scalar_bound
    (P : M47ScalarPersistencePredecessors.{u})
    {J : Set ℝ} (F : RicciFlow 3 M J) {b v A L r : ℝ} (q : M)
    (hv : 0 ≤ v) (hJ : Icc b (b + v) ⊆ J) (hA : 0 ≤ A) (hL : 0 < L)
    (hinitial : ∀ z ∈ closure ((F.metric b).ball q r),
      (F.connection b).scalarCurvature z ≤ 4 * L)
    (hestimate : ∀ z ∈ closure ((F.metric b).ball q r), ∀ s ∈ Ioo b (b + v),
      4 * L < (F.connection s).scalarCurvature z →
      |(F.connection s).laplacian (F.connection s).scalarCurvature z +
          2 * (F.connection s).ricciNormSq z| ≤
        A * (F.connection s).scalarCurvature z ^ 2)
    (hbudget : A * L * v ≤ 1 / 64) :
    ∀ z ∈ closure ((F.metric b).ball q r), ∀ s ∈ Icc b (b + v),
      (F.connection s).scalarCurvature z < 8 * L := by
  intro z hz s hs
  have h := jointSeed_forward_of_evolution_bound P F z (by linarith)
    hJ hA (by positivity : 0 < 4 * L) (hinitial z hz) (hestimate z hz)
    (by nlinarith : A * (4 * L) * (b + v - b) ≤ 1 / 4) s hs
  linarith

end PoincareConjecture.M47
