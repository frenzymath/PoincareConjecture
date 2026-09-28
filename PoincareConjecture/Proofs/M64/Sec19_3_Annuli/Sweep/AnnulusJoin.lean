import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.MetricTransport
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.MetricLipschitzBridge
import PoincareConjecture.Proofs.M60.Mathlib.LipschitzGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

noncomputable def m64RadialDouble (d : ℝ) (p : LoopPlane) : LoopPlane :=
  annulusPoint (p 0) (2 * p 1 - d)

theorem m64RadialDouble_norm_sub_le (d : ℝ) (p q : LoopPlane) :
    ‖m64RadialDouble d p - m64RadialDouble d q‖ ≤ 2 * ‖p - q‖ := by
  have heq : m64RadialDouble d p - m64RadialDouble d q =
      (p - q) + (p 1 - q 1) • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    ext i
    fin_cases i <;> simp [m64RadialDouble, annulusPoint, EuclideanSpace.basisFun_apply]
    ring
  rw [heq]
  have hc : |p 1 - q 1| ≤ ‖p - q‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (p - q) 1
  calc
    _ ≤ ‖p - q‖ + ‖(p 1 - q 1) • EuclideanSpace.basisFun (Fin 2) ℝ 1‖ := norm_add_le _ _
    _ = ‖p - q‖ + |p 1 - q 1| := by
      rw [norm_smul, Real.norm_eq_abs, OrthonormalBasis.norm_eq_one, mul_one]
    _ ≤ 2 * ‖p - q‖ := by linarith

noncomputable def m64AnnulusJoinMap {M : Type u} (f h : LoopPlane → M) (p : LoopPlane) : M :=
  if p 1 ≤ (1 / 2 : ℝ) then f (m64RadialDouble 0 p) else h (m64RadialDouble 1 p)

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64AnnulusJoinMap_lipschitz
    {g : RiemannianMetric n M} {c0 c1 c2 : ℝ → M}
    (A : M64Annulus g c0 c1) (B : M64Annulus g c1 c2) :
    ∃ K : ℝ≥0, ∀ x y : m64AnnulusDomain,
      g.edist (m64AnnulusJoinMap A.map B.map x) (m64AnnulusJoinMap A.map B.map y) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : R1Space M := T2Space.r1Space
  let : RegularSpace M := RegularSpace.of_hasBasis
    isCompact_isClosed_basis_nhds (fun _ _ ⟨_, _, h⟩ => h)
  let : T3Space M := ⟨⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let K : ℝ≥0 := ⟨2 * A.lipschitz_constant, mul_nonneg (by norm_num) A.lipschitz_nonnegative⟩
  let L : ℝ≥0 := ⟨2 * B.lipschitz_constant, mul_nonneg (by norm_num) B.lipschitz_nonnegative⟩
  have hbound {c d : ℝ → M} (D : M64Annulus g c d) (shift : ℝ)
      {S : Set LoopPlane} (hS : MapsTo (m64RadialDouble shift) S m64AnnulusDomain) :
      LipschitzOnWith (⟨2 * D.lipschitz_constant,
        mul_nonneg (by norm_num) D.lipschitz_nonnegative⟩ : ℝ≥0)
        (fun p => D.map (m64RadialDouble shift p)) S := by
    intro x hx y hy
    change g.edist _ _ ≤ _
    have h := D.lipschitz_on_domain ⟨_, hS hx⟩ ⟨_, hS hy⟩
    calc
      _ ≤ ENNReal.ofReal D.lipschitz_constant *
          ENNReal.ofReal ‖m64RadialDouble shift x - m64RadialDouble shift y‖ := h
      _ ≤ ENNReal.ofReal D.lipschitz_constant * ENNReal.ofReal (2 * ‖x - y‖) := by
        gcongr
        exact m64RadialDouble_norm_sub_le shift x y
      _ = _ := by
        rw [ENNReal.coe_nnreal_eq]
        change ENNReal.ofReal D.lipschitz_constant * ENNReal.ofReal (2 * ‖x - y‖) =
          ENNReal.ofReal (2 * D.lipschitz_constant) * edist x y
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        simp only [edist_dist, dist_eq_norm]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        ring
  have hleft : LipschitzOnWith K (fun p => A.map (m64RadialDouble 0 p))
      (m64AnnulusDomain ∩ {p | p 1 ≤ (1 / 2 : ℝ)}) := by
    apply hbound A 0
    intro p hp
    change 0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ 2 * p 1 - 0 ∧ 2 * p 1 - 0 ≤ 1
    have hhalf : p 1 ≤ (1 / 2 : ℝ) := hp.2
    refine ⟨hp.1.1, hp.1.2.1, ?_, ?_⟩ <;> linarith [hp.1.2.2.1]
  have hright : LipschitzOnWith L (fun p => B.map (m64RadialDouble 1 p))
      (m64AnnulusDomain ∩ {p | (1 / 2 : ℝ) ≤ p 1}) := by
    apply hbound B 1
    intro p hp
    change 0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ 2 * p 1 - 1 ∧ 2 * p 1 - 1 ≤ 1
    have hhalf : (1 / 2 : ℝ) ≤ p 1 := hp.2
    refine ⟨hp.1.1, hp.1.2.1, ?_, ?_⟩ <;> linarith [hp.1.2.2.2]
  have hjoin := M60.lipschitzOnWith_piecewise_of_convex m64AnnulusDomain_convex
    (fun p : LoopPlane => p 1) (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).continuousOn
    (1 / 2 : ℝ) hleft hright (fun p _ hp => by
      simp only [m64RadialDouble, hp]
      norm_num
      rw [A.upper_boundary, B.lower_boundary])
  refine ⟨max K L, ?_⟩
  intro x y
  have h := hjoin x.property y.property
  change g.edist _ _ ≤ _ at h
  simpa only [m64AnnulusJoinMap, Set.piecewise, mem_ofPred_eq, edist_dist, dist_eq_norm] using
    h

theorem m64Annulus_join
    {g : RiemannianMetric n M} {c0 c1 c2 : ℝ → M}
    (A : M64Annulus g c0 c1) (B : M64Annulus g c1 c2) :
    ∃ C : M64Annulus g c0 c2, C.map = m64AnnulusJoinMap A.map B.map := by
  let f := m64AnnulusJoinMap A.map B.map
  obtain ⟨K, hK⟩ := m64AnnulusJoinMap_lipschitz A B
  have hLip : ∀ x y : m64AnnulusDomain, g.edist (f x) (f y) ≤
      ENNReal.ofReal (K : ℝ) * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
    simpa only [ENNReal.ofReal_coe_nnreal] using hK
  have hcontinuous : ContinuousOn f m64AnnulusDomain := by
    let : LocallyCompactSpace M :=
      ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
    let : R1Space M := T2Space.r1Space
    let : RegularSpace M := RegularSpace.of_hasBasis
      isCompact_isClosed_basis_nhds (fun _ _ ⟨_, _, h⟩ => h)
    let : T3Space M := ⟨⟩
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
    have h : LipschitzOnWith K f m64AnnulusDomain := by
      intro x hx y hy
      change g.edist (f x) (f y) ≤ _
      simpa only [edist_dist, dist_eq_norm] using hK ⟨x, hx⟩ ⟨y, hy⟩
    exact h.continuousOn
  have hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal) := by
    rw [← measure_congr m64AnnulusDomain_ae_eq_interior]
    exact m64AnnulusDomain_volume_ne_top
  obtain ⟨C, hmap, _⟩ := m64Annulus_of_lipschitz g (c0 := c0) (c1 := c2) f hcontinuous
    (by
      intro x s
      simp only [f, m64AnnulusJoinMap, m64RadialDouble, annulusPoint,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      split_ifs <;> first | exact A.periodic x (2 * s - 0) | exact B.periodic x (2 * s - 1))
    (by
      intro x
      norm_num [f, m64AnnulusJoinMap, m64RadialDouble, annulusPoint]
      exact A.lower_boundary x)
    (by
      intro x
      norm_num [f, m64AnnulusJoinMap, m64RadialDouble, annulusPoint]
      exact B.upper_boundary x)
    K.coe_nonneg hLip hfinite
    (show m64AnnulusArea g f < m64AnnulusArea g f + 1 by linarith)
  exact ⟨C, hmap⟩

end PoincareConjecture
