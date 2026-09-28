import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Flow.Outward.Neighborhood
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Exhaustion
import Mathlib.Geometry.Manifold.PartitionOfUnity










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]




theorem exists_smooth_outward_field_of_singleton_horoball
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    {o p : M} {c : ℝ}
    (hlevel : letI := g.toMetricSpace;
      Poincare.Riemannian.Soul.horoballIntersection o c = {p})
    {r : ℝ} (hr : 0 < r) :
    ∃ X : (y : M) → TangentSpace (𝓡 n) y,
      ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) ∧
      ∀ y : M, r ≤ (g.edist y p).toReal → ∀ γ : ℝ → M,
        g.IsGeodesicOn γ (Icc 0 (g.edist y p).toReal) → γ 0 = y →
        γ (g.edist y p).toReal = p →
        (∀ t ∈ Icc 0 (g.edist y p).toReal,
          g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1) →
        (∀ s ∈ Icc 0 (g.edist y p).toReal, ∀ t ∈ Icc 0 (g.edist y p).toReal,
          g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) →
        g.inner y (X y) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) ≤ -1 := by
  classical
  let := g.toMetricSpace
  let : SecondCountableTopology M := g.secondCountableTopology
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let cone (y : M) : Set (TangentSpace (𝓡 n) y) :=
    if dist y p < r then univ else
      {v | ∀ γ : ℝ → M,
        g.IsGeodesicOn γ (Icc 0 (g.edist y p).toReal) → γ 0 = y →
        γ (g.edist y p).toReal = p →
        (∀ t ∈ Icc 0 (g.edist y p).toReal,
          g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1) →
        (∀ s ∈ Icc 0 (g.edist y p).toReal, ∀ t ∈ Icc 0 (g.edist y p).toReal,
          g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) →
        g.inner y v (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) ≤ -1}
  have hconv (y : M) : Convex ℝ (cone y) := by
    dsimp only [cone]
    split_ifs with hy
    · exact convex_univ
    · intro v hv w hw a b ha hb hab γ hγ hγ0 hγL hspeed hmin
      have hv' := hv γ hγ hγ0 hγL hspeed hmin
      have hw' := hw γ hγ hγ0 hγL hspeed hmin
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      calc
        _ ≤ a * (-1) + b * (-1) := add_le_add
          (mul_le_mul_of_nonneg_left hv' ha) (mul_le_mul_of_nonneg_left hw' hb)
        _ = -1 := by nlinarith only [hab]
  have hlocal (x : M) : ∃ U ∈ 𝓝 x, ∃ s : (y : M) → TangentSpace (𝓡 n) y,
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% s) U ∧
        ∀ y ∈ U, s y ∈ cone y := by
    by_cases hx : dist x p < r
    · let U : Set M := {y | dist y p < r}
      have hU : IsOpen U := isOpen_lt (continuous_id.dist continuous_const) continuous_const
      refine ⟨U, hU.mem_nhds hx, fun _ => 0, ?_, ?_⟩
      · exact (contMDiff_zeroSection ℝ (TangentSpace (𝓡 n) : M → Type _)).contMDiffOn
      · intro y hy
        change dist y p < r at hy
        simp only [cone, if_pos hy, mem_univ]
    · have hxp : x ≠ p := by
        intro heq
        exact hx (by simpa [heq] using hr)
      obtain ⟨U, rho, κ, hU, hxU, hrho, hκ, _, hderiv⟩ :=
        g.exists_common_inward_potential_neighborhood D hc hsec hlevel hxp
      refine ⟨U, hU.mem_nhds hxU, fun y => (-κ⁻¹) • g.gradient rho y, ?_, ?_⟩
      · exact ((g.contMDiff_gradient hrho).const_smul_section (a := -κ⁻¹)).contMDiffOn
      · intro y hy
        dsimp only [cone]
        split_ifs with hyr
        · exact mem_univ _
        · intro γ hγ hγ0 hγL hspeed hmin
          have hd := hderiv y hy γ hγ hγ0 hγL hspeed hmin
          simp only [map_smul, smul_apply, smul_eq_mul, g.inner_gradient]
          calc
            _ ≤ (-κ⁻¹) * κ := mul_le_mul_of_nonpos_left hd (neg_nonpos.mpr (inv_nonneg.mpr hκ.le))
            _ = -1 := by rw [neg_mul, inv_mul_cancel₀ hκ.ne']
  obtain ⟨X, hX⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    (𝓡 n) (TangentSpace (𝓡 n) : M → Type _) cone hconv hlocal
  refine ⟨X, X.contMDiff, ?_⟩
  intro y hy
  have hy' : ¬ dist y p < r := not_lt.mpr hy
  simpa only [cone, if_neg hy', mem_ofPred_eq] using hX y

end PoincareConjecture.RiemannianMetric
