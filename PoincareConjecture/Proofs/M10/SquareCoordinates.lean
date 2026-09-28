import PoincareConjecture.Proofs.M10.EndpointCoordinates
import PoincareConjecture.Proofs.M10.InitialDifferentialCalculus

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

noncomputable def squareCoordinates (G : LExponentialGeometry F T τmax p)
    (z : TangentSpace (𝓡 n) p × ℝ) : EuclideanSpace ℝ (Fin n) :=
  extChartAt (𝓡 n) p (G.squareFamily z.1 z.2)

set_option backward.isDefEq.respectTransparency false in

theorem squareCoordinates_contDiffAt (G : LExponentialGeometry F T τmax p)
    (z : TangentSpace (𝓡 n) p × ℝ) (hz : z ∈ G.squareDomain)
    (hq : G.squareFamily z.1 z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    ContDiffAt ℝ ∞ (squareCoordinates G) z := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have hQ := G.square_smooth.contMDiffAt (G.square_open.mem_nhds hz)
  have he := (contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hq).comp z hQ
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at he
  exact he.contDiffAt

theorem squareDomain_at_zero (G : LExponentialGeometry F T τmax p)
    (hmax : 0 < τmax) (Z : TangentSpace (𝓡 n) p) : (Z, 0) ∈ G.squareDomain :=
  G.square_contains ⟨mem_univ _, le_rfl, Real.sqrt_pos.2 hmax⟩

theorem squareCoordinates_at_zero (G : LExponentialGeometry F T τmax p)
    (Z : TangentSpace (𝓡 n) p) : squareCoordinates G (Z, 0) = extChartAt (𝓡 n) p p := by
  simp only [squareCoordinates, G.square_at_zero]

set_option backward.isDefEq.respectTransparency false in

theorem mfderiv_extChartAt_apply_of_eq {q : M} (hq : q = p)
    (v : TangentSpace (𝓡 n) q) :
    mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) q v =
      (hq ▸ v : TangentSpace (𝓡 n) p) := by
  subst q
  rw [mfderiv_extChartAt_self]
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem squareCoordinates_time_at_zero (G : LExponentialGeometry F T τmax p)
    (hmax : 0 < τmax) (Z : TangentSpace (𝓡 n) p) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    fderiv ℝ (squareCoordinates G) (Z, 0) (0, 1) =
      (2 : ℝ) • ((trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n)) p).continuousLinearMapAt ℝ p Z) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have hz := squareDomain_at_zero G hmax Z
  have hq : G.squareFamily Z 0 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source := by
    rw [G.square_at_zero]
    exact mem_chart_source _ _
  have hQ := G.square_smooth.contMDiffAt (G.square_open.mem_nhds hz)
  have ht : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) (G.squareFamily Z) 0 :=
    (hQ.comp (0 : ℝ) (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hc := mfderiv_comp (0 : ℝ) (mdifferentiableAt_extChartAt hq) ht
  rw [mfderiv_eq_fderiv] at hc
  have hd := hasDerivAt_time_slice
    ((squareCoordinates_contDiffAt G (Z, 0) hz hq).differentiableAt (by simp))
  rw [← hd.deriv]
  change fderiv ℝ ((extChartAt (𝓡 n) p) ∘ G.squareFamily Z) 0 1 = _
  rw [hc]
  change mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (G.squareFamily Z 0)
    (curveVelocity (G.squareFamily Z) 0) = _
  rw [mfderiv_extChartAt_apply_of_eq (G.square_at_zero Z), G.initial_derivative,
    TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source _ _),
    mfderiv_extChartAt_self]
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem squareCoordinates_scaled_differential_tendsto
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (Z W : TangentSpace (𝓡 n) p) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    Tendsto (fun s : ℝ ↦ s⁻¹ • fderiv ℝ (squareCoordinates G) (Z, s) (W, 0))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((2 : ℝ) • ((trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n)) p).continuousLinearMapAt ℝ p W))) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let L : TangentSpace (𝓡 n) p →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (2 : ℝ) • (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) p).continuousLinearMapAt ℝ p
  apply tendsto_scaled_horizontal_fderiv L
    ((squareCoordinates_contDiffAt G (Z, 0) (squareDomain_at_zero G hmax Z)
      (by simpa only [G.square_at_zero] using mem_chart_source (EuclideanSpace ℝ (Fin n)) p)
      ).of_le (by decide))
    (squareCoordinates_at_zero G)
  exact squareCoordinates_time_at_zero G hmax

end PoincareConjecture.M10
