import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Pullback.Chart
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.MetricPair
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Coordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff Bundle
universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

open ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def variationChartDomain {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (x : M) : Set (ℝ × ℝ) :=
  V.squareDomain ∩ (fun z : ℝ × ℝ ↦ V.squareFamily z.1 z.2) ⁻¹'
    (chartAt (EuclideanSpace ℝ (Fin n)) x).source

def variationChart {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (x : M) (z : ℝ × ℝ) : EuclideanSpace ℝ (Fin n) :=
  extChartAt (𝓡 n) x (V.squareFamily z.1 z.2)

theorem variationChartDomain_open {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (x : M) : IsOpen (variationChartDomain V x) :=
  V.square_smooth.continuousOn.isOpen_inter_preimage V.square_open
    (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source

theorem variationChart_contDiffOn {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (x : M) :
    ContDiffOn ℝ ∞ (variationChart V x) (variationChartDomain V x) := by
  have h := (contMDiffOn_extChartAt (I := 𝓡 n) (x := x)).comp
    (V.square_smooth.mono inter_subset_left) (fun z hz ↦ by
      simpa only [extChartAt_source] using hz.2)
  apply ContMDiffOn.contDiffOn
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact h

variable {J : Set ℝ} {F : RicciFlow n M J} {T τ₁ τ₂ : ℝ}
  {p : BackwardTimePath F T τ₁ τ₂}

theorem variationChart_partialS_frame (V : LVariation F T τ₁ τ₂ p)
    {x : M} {z : ℝ × ℝ} (hz : z ∈ variationChartDomain V x) :
    chartFrame x (coordinatePartialS (variationChart V x) z) (V.squareFamily z.1 z.2) =
      curveVelocity (n := n) (fun r ↦ V.squareFamily r z.2) z.1 := by
  have hq := (((variationChart_contDiffOn V x) z hz).contDiffAt
    ((variationChartDomain_open V x).mem_nhds hz)).differentiableAt (by simp)
  have hd := (coordinateSlice_fst_hasDerivAt (variationChart V x) hq).deriv
  have hα := (((V.square_smooth z hz.1).contMDiffAt
    (V.square_open.mem_nhds hz.1)).mdifferentiableAt (by simp)).comp z.1
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  change deriv ((extChartAt (𝓡 n) x) ∘ (fun r ↦ V.squareFamily r z.2)) z.1 =
    coordinatePartialS (variationChart V x) z at hd
  rw [← hd]
  exact chartFrame_curveVelocity hz.2 hα

theorem variationChart_partialU_frame (V : LVariation F T τ₁ τ₂ p)
    {x : M} {z : ℝ × ℝ} (hz : z ∈ variationChartDomain V x) :
    chartFrame x (coordinatePartialU (variationChart V x) z) (V.squareFamily z.1 z.2) =
      curveVelocity (n := n) (V.squareFamily z.1) z.2 := by
  have hq := (((variationChart_contDiffOn V x) z hz).contDiffAt
    ((variationChartDomain_open V x).mem_nhds hz)).differentiableAt (by simp)
  have hd := (coordinateSlice_snd_hasDerivAt (variationChart V x) hq).deriv
  have hα := (((V.square_smooth z hz.1).contMDiffAt
    (V.square_open.mem_nhds hz.1)).mdifferentiableAt (by simp)).comp z.2
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  change deriv ((extChartAt (𝓡 n) x) ∘ V.squareFamily z.1) z.2 =
    coordinatePartialU (variationChart V x) z at hd
  rw [← hd]
  exact chartFrame_curveVelocity hz.2 hα

theorem variationBaseSquare_mdifferentiableAt (V : LVariation F T τ₁ τ₂ p)
    {s : ℝ} (hs : s ∈ sqrtParameterInterval τ₁ τ₂) :
    MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) V.baseSquareCurve s := by
  have hz : (s, (0 : ℝ)) ∈ V.squareDomain :=
    V.square_contains ⟨hs, neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  exact (((V.square_smooth (s, 0) hz).contMDiffAt
    (V.square_open.mem_nhds hz)).mdifferentiableAt (by simp)).comp s
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)

theorem variationChart_baseVelocity (V : LVariation F T τ₁ τ₂ p)
    {x : M} {s : ℝ} (hs : s ∈ sqrtParameterInterval τ₁ τ₂)
    (hx : V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    chartFrame x (coordinatePartialS (variationChart V x) (s, 0)) (V.baseSquareCurve s) =
      curveVelocityWithin (n := n) V.baseSquareCurve (sqrtParameterInterval τ₁ τ₂) s := by
  have hzero : (0 : ℝ) ∈ V.parameterDomain := ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have h := variationChart_partialS_frame V (x := x) (z := (s, 0))
    ⟨V.square_contains ⟨hs, hzero⟩, hx⟩
  unfold curveVelocityWithin
  dsimp only [sqrtParameterInterval]
  rw [mfderivWithin_eq_mfderiv
    ((uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered) s hs).uniqueMDiffWithinAt)
    (variationBaseSquare_mdifferentiableAt V hs)]
  exact h

theorem variationChart_squareVariationField (V : LVariation F T τ₁ τ₂ p)
    {x : M} {s : ℝ} (hs : s ∈ sqrtParameterInterval τ₁ τ₂)
    (hx : V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    chartFrame x (coordinatePartialU (variationChart V x) (s, 0)) (V.baseSquareCurve s) =
      squareVariationField V s := by
  have hzero : (0 : ℝ) ∈ V.parameterDomain := ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  exact variationChart_partialU_frame V ⟨V.square_contains ⟨hs, hzero⟩, hx⟩

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
