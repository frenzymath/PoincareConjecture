import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Heat.Dirichlet.Energy
import PoincareConjecture.Proofs.M07.Analysis.Parabolic.Dirichlet.Variational














set_option autoImplicit false

noncomputable section

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

theorem EnergyTest.memLp (f : EnergyTest D Ω) : MemLp (f : M → ℝ) 2 g.volumeMeasure :=
  f.smooth.continuous.memLp_of_hasCompactSupport f.hasCompactSupport


def testToL2 (D : LeviCivitaData g) (Ω : Set M) :
    EnergyTest D Ω →ₗ[ℝ] Lp ℝ 2 g.volumeMeasure where
  toFun f := f.memLp.toLp f
  map_add' f h := by
    exact MemLp.toLp_add f.memLp h.memLp
  map_smul' c f := by
    exact MemLp.toLp_const_smul c f.memLp

@[simp] theorem testToL2_inner (f h : EnergyTest D Ω) :
    ⟪testToL2 D Ω f, testToL2 D Ω h⟫_ℝ = ∫ x, f x * h x ∂g.volumeMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.memLp.coeFn_toLp, h.memLp.coeFn_toLp] with x hfx hhx
  change inner ℝ ((testToL2 D Ω f) x) ((testToL2 D Ω h) x) = f x * h x
  rw [show (testToL2 D Ω f) x = f x from hfx,
    show (testToL2 D Ω h) x = h x from hhx]
  simp [mul_comm]

theorem norm_testToL2_le (f : EnergyTest D Ω) : ‖testToL2 D Ω f‖ ≤ ‖f‖ := by
  have hsq : ‖testToL2 D Ω f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, testToL2_inner, f.norm_sq]
    exact le_add_of_nonneg_right (integral_gradient_self_nonneg f)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq


def testToL2CLM (D : LeviCivitaData g) (Ω : Set M) :
    EnergyTest D Ω →L[ℝ] Lp ℝ 2 g.volumeMeasure :=
  (testToL2 D Ω).mkContinuous 1 (fun f => by simpa using norm_testToL2_le f)


def toL2 (D : LeviCivitaData g) (Ω : Set M) :
    H1Zero D Ω →L[ℝ] Lp ℝ 2 g.volumeMeasure :=
  Poincare.Analysis.Dirichlet.completionMap (testToL2CLM D Ω)

@[simp] theorem toL2_coe (f : EnergyTest D Ω) : toL2 D Ω f = testToL2 D Ω f :=
  Poincare.Analysis.Dirichlet.completionMap_coe _ _

theorem norm_toL2_le (u : H1Zero D Ω) : ‖toL2 D Ω u‖ ≤ ‖u‖ := by
  exact (Poincare.Analysis.Dirichlet.norm_completionMap_apply_le
    (testToL2CLM D Ω) (C := 1) (fun f => by simpa [testToL2CLM] using norm_testToL2_le f) u).trans_eq
      (one_mul _)


def resolvent (D : LeviCivitaData g) (Ω : Set M) :
    Lp ℝ 2 g.volumeMeasure →L[ℝ] H1Zero D Ω :=
  Poincare.Analysis.Dirichlet.resolvent (testToL2CLM D Ω)

theorem resolvent_inner (f : Lp ℝ 2 g.volumeMeasure) (v : H1Zero D Ω) :
    ⟪resolvent D Ω f, v⟫_ℝ = ⟪f, toL2 D Ω v⟫_ℝ :=
  Poincare.Analysis.Dirichlet.resolvent_inner _ _ _

theorem existsUnique_weak_resolvent (f : Lp ℝ 2 g.volumeMeasure) :
    ∃! u : H1Zero D Ω, ∀ v : H1Zero D Ω, ⟪u, v⟫_ℝ = ⟪f, toL2 D Ω v⟫_ℝ := by
  refine ⟨resolvent D Ω f, resolvent_inner f, ?_⟩
  intro u hu
  exact Poincare.Analysis.Dirichlet.resolvent_unique _ _ _ hu

theorem norm_resolvent_le : ‖resolvent D Ω‖ ≤ 1 :=
  Poincare.Analysis.Dirichlet.norm_resolvent_le _ norm_testToL2_le

theorem EnergyTest.oneSubLaplacian_memLp (f : EnergyTest D Ω) :
    MemLp (fun x => f x - D.laplacian f x) 2 g.volumeMeasure :=
  (f.smooth.continuous.sub (D.continuous_laplacian f.smooth)).memLp_of_hasCompactSupport
    (f.hasCompactSupport.sub (D.hasCompactSupport_laplacian f.hasCompactSupport))


def EnergyTest.oneSubLaplacian (f : EnergyTest D Ω) : Lp ℝ 2 g.volumeMeasure :=
  f.oneSubLaplacian_memLp.toLp _

theorem EnergyTest.inner_oneSubLaplacian [PreconnectedSpace M] (f h : EnergyTest D Ω) :
    ⟪(f : H1Zero D Ω), (h : H1Zero D Ω)⟫_ℝ =
      ⟪f.oneSubLaplacian, testToL2 D Ω h⟫_ℝ := by
  rw [Completion.inner_coe, EnergyTest.inner_eq, energyInner_eq_integral_oneSubLaplacian,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.oneSubLaplacian_memLp.coeFn_toLp, h.memLp.coeFn_toLp] with x hfx hhx
  change (f x - D.laplacian f x) * h x =
    inner ℝ (f.oneSubLaplacian x) ((testToL2 D Ω h) x)
  rw [show f.oneSubLaplacian x = f x - D.laplacian f x from hfx,
    show (testToL2 D Ω h) x = h x from hhx]
  simp [mul_comm]


theorem resolvent_oneSubLaplacian [PreconnectedSpace M] (f : EnergyTest D Ω) :
    resolvent D Ω f.oneSubLaplacian = (f : H1Zero D Ω) := by
  symm
  exact Poincare.Analysis.Dirichlet.resolvent_unique_of_test
    (testToL2CLM D Ω) f.oneSubLaplacian f f.inner_oneSubLaplacian


theorem toL2_injective [PreconnectedSpace M] : Function.Injective (toL2 D Ω) := by
  suffices hzero : ∀ u : H1Zero D Ω, toL2 D Ω u = 0 → u = 0 from
    fun u v huv => sub_eq_zero.mp (hzero (u - v) (by simpa using sub_eq_zero.mpr huv))
  intro u hu
  have htest (v : EnergyTest D Ω) : ⟪(v : H1Zero D Ω), u⟫_ℝ = 0 := by
    rw [← resolvent_oneSubLaplacian v, resolvent_inner, hu, inner_zero_right]
  have hall (v : H1Zero D Ω) : ⟪v, u⟫_ℝ = 0 := by
    induction v using Completion.induction_on with
    | hp => exact isClosed_eq (continuous_id.inner continuous_const) continuous_const
    | ih v => exact htest v
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (hall u)


theorem denseRange_resolvent [PreconnectedSpace M] : DenseRange (resolvent D Ω) := by
  apply Completion.denseRange_coe.mono
  rintro _ ⟨f, rfl⟩
  exact ⟨f.oneSubLaplacian, resolvent_oneSubLaplacian f⟩


def l2Resolvent (D : LeviCivitaData g) (Ω : Set M) :
    Lp ℝ 2 g.volumeMeasure →L[ℝ] Lp ℝ 2 g.volumeMeasure :=
  (toL2 D Ω).comp (resolvent D Ω)

theorem l2Resolvent_isSelfAdjoint : IsSelfAdjoint (l2Resolvent D Ω) :=
  Poincare.Analysis.Dirichlet.ambientResolvent_isSelfAdjoint (testToL2CLM D Ω)

theorem l2Resolvent_inner (f h : Lp ℝ 2 g.volumeMeasure) :
    ⟪l2Resolvent D Ω f, h⟫_ℝ = ⟪resolvent D Ω f, resolvent D Ω h⟫_ℝ :=
  Poincare.Analysis.Dirichlet.ambientResolvent_inner _ _ _

theorem l2Resolvent_nonneg (f : Lp ℝ 2 g.volumeMeasure) :
    0 ≤ ⟪l2Resolvent D Ω f, f⟫_ℝ :=
  Poincare.Analysis.Dirichlet.ambientResolvent_nonneg _ _

end PoincareConjecture.LeviCivitaData.Dirichlet
