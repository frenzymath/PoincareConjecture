import PoincareConjecture.Proofs.M08.JacobiGlobalPair

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem parametricExtension_along_contMDiffOn {C : Set ℝ} {α : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (α s)}
    (E : ParametricAlongCurveExtensionOn C α Y)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α C) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (Y s)) C := by
  have h := E.smooth.comp (contMDiffOn_id.prodMk hα) (fun s hs ↦ E.graph_mem s hs)
  apply h.congr
  intro s hs
  change Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (Y s) =
    Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (E.extension s (α s))
  rw [E.agrees s hs]

theorem sqrtRegularField_isJacobiPair {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂} (R : RegularizedLGeodesicData p)
    {Y : ∀ τ, TangentSpace (𝓡 n) (p.curve τ)} (Q : SqrtRegularField R.path Y)
    (hres : ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
      ∀ W : TangentSpace (𝓡 n) (R.path.curve s), regularizedJacobiResidual R Q s W = 0) :
    IsJacobiPairOn F T R.path.curve (sqrtParameterInterval τ₁ τ₂)
      (Real.sqrt τ₁) (Real.sqrt τ₂) (fun s ↦ (Q.field s, Q.firstDerivative s)) := by
  refine ⟨Real.sqrt_lt_sqrt p.nonnegative p.ordered, Subset.rfl,
    parametricExtension_along_contMDiffOn Q.extension (R.path.smooth.mono R.path.interval_subset),
    parametricExtension_along_contMDiffOn Q.derivative_extension
      (R.path.smooth.mono R.path.interval_subset), Q.extension, Q.derivative_extension,
    fun _ _ ↦ rfl, ?_⟩
  intro s hs W
  exact hres s hs W

set_option maxHeartbeats 1500000 in
theorem exists_lJacobi_initialValue {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τ₁ τ₂ : ℝ}
    (p : BackwardTimePath F T τ₁ τ₂) (R : RegularizedLGeodesicData p)
    (Z : TangentSpace (𝓡 n) (p.curve τ₁)) :
    ∃ Y : ∀ τ, TangentSpace (𝓡 n) (p.curve τ),
      IsLJacobiField F T τ₁ τ₂ p Y ∧ HasLJacobiInitialDerivative R Y Z ∧
        ∀ Y' : ∀ τ, TangentSpace (𝓡 n) (p.curve τ),
          IsLJacobiField F T τ₁ τ₂ p Y' → HasLJacobiInitialDerivative R Y' Z →
            ∀ τ ∈ Icc τ₁ τ₂, Y' τ = Y τ := by
  have hab : Real.sqrt τ₁ < Real.sqrt τ₂ := Real.sqrt_lt_sqrt p.nonnegative p.ordered
  have ha : Real.sqrt τ₁ ∈ sqrtParameterInterval τ₁ τ₂ := ⟨le_rfl, hab.le⟩
  have htime (s : ℝ) (hs : s ∈ sqrtParameterInterval τ₁ τ₂) : T - s ^ 2 ∈ J :=
    p.time_mem (s ^ 2) (square_mem_backward_interval p hs)
  let hbase : R.path.curve (Real.sqrt τ₁) = p.curve τ₁ :=
    sqrtRegularPath_point_eq R.path ⟨le_rfl, p.ordered.le⟩
  let Z₀ : TangentSpace (𝓡 n) (R.path.curve (Real.sqrt τ₁)) := hbase.symm ▸ Z
  obtain ⟨z, hz, hz₀⟩ := exists_jacobiPairOn F hM04 T hab htime R.path.curve
    R.path.open_domain R.path.interval_subset R.path.smooth (0, Z₀)
  obtain ⟨EY, EP, hY, hP⟩ := hz.equations
  let Y := backwardFieldOfSqrt R.path (fun s ↦ (z s).1)
  let Q : SqrtRegularField R.path Y :=
    sqrtRegularFieldOfPullback R.path (fun s ↦ (z s).1) (fun s ↦ (z s).2) EY EP hY
  have hfirst (s : ℝ) (hs : s ∈ sqrtParameterInterval τ₁ τ₂) :
      Q.firstDerivative s = (z s).2 := hY s hs
  have hsecond (s : ℝ) : Q.secondDerivative s =
      pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) R.path.curve
        (fun r ↦ (z r).2) (sqrtParameterInterval τ₁ τ₂) EP s := rfl
  have hzero : Y τ₁ = 0 := backwardFieldOfSqrt_initial_zero R.path (fun s ↦ (z s).1)
    (congrArg Prod.fst hz₀)
  have hres : ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
      ∀ W : TangentSpace (𝓡 n) (R.path.curve s), regularizedJacobiResidual R Q s W = 0 := by
    intro s hs W
    change jacobiPairResidual F T R.path.curve (sqrtParameterInterval τ₁ τ₂) s
      (z s).1 (Q.firstDerivative s) (Q.secondDerivative s) W = 0
    rw [hfirst s hs, hsecond]
    exact hP s hs W
  refine ⟨Y, ⟨R, Q, hzero, hres⟩, ⟨Q, ?_⟩, ?_⟩
  · exact (hfirst _ ha).trans (congrArg Prod.snd hz₀)
  · intro Y' hY' hZ'
    obtain ⟨Q', hzero', hres'⟩ := isLJacobiField_residual_for_representative hY' R
    obtain ⟨Q₀, hQ₀⟩ := hZ'
    have hfirst' : Q'.firstDerivative (Real.sqrt τ₁) = Z₀ :=
      (sqrtRegularField_firstDerivative_eq Q' Q₀ ha).trans hQ₀
    have hzeroQ' : Q'.field (Real.sqrt τ₁) = 0 := by
      rw [Q'.agrees _ ha, tangent_cast_eq (n := n), Real.sq_sqrt p.nonnegative, hzero']
    have hinit : (Q'.field (Real.sqrt τ₁), Q'.firstDerivative (Real.sqrt τ₁)) =
        z (Real.sqrt τ₁) := by
      rw [hz₀, hzeroQ', hfirst']
    have heq := jacobiPairOn_unique hM04 htime R.path.open_domain R.path.interval_subset
      R.path.smooth (sqrtRegularField_isJacobiPair R Q' hres') hz hinit
    apply sqrtRegularField_eq_of_totalSpace_eq Q' Q
    intro s hs
    exact congrArg (fun v : TangentSpace (𝓡 n) (R.path.curve s) ↦
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.path.curve s) v)
        (show Q'.field s = Q.field s from congrArg Prod.fst (heq hs))

end PoincareConjecture.M08
