import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.AddCirclePLCharts
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PiecewiseAffinePi
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.AtlasOfCover

/-!
# The actual standard PL atlas of a finite-dimensional torus

Finite products of additive-circle quotient charts have PL
coordinate changes. Two punctures in each circle give an
explicit finite chart cover. This supplies the standard target
PL structure in Hamilton's torus diagram; it does not identify
an arbitrary pulled-back structure with it. See Hamilton 1976,
pp. 64--67 and M76 derivation 270.
-/

set_option autoImplicit false

open Set Geometry

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]

/-- Two actual puncture charts cover an additive circle. The
punctures are distinct because the period is positive. See
Hamilton pp. 64--66 and M76 derivation 270. -/
theorem two_puncture_charts_cover (x : AddCircle p) :
    ∃ b : Bool, x ∈ (openPartialHomeomorphCoe p (if b then 0 else p / 2)).target := by
  have hp : 0 < p := Fact.out
  have hhalfmem : p / 2 ∈ Ico (0 : ℝ) p := by
    constructor <;> linarith
  have hhalf : ((p / 2 : ℝ) : AddCircle p) ≠ 0 := by
    intro he
    have hz := (coe_eq_zero_iff_of_mem_Ico hhalfmem).mp he
    linarith
  by_cases hx : x = 0
  · refine ⟨false, ?_⟩
    change x ≠ ((p / 2 : ℝ) : AddCircle p)
    rw [hx]
    exact hhalf.symm
  · refine ⟨true, ?_⟩
    change x ≠ ((0 : ℝ) : AddCircle p)
    simpa only [QuotientAddGroup.mk_zero] using hx

variable {ι : Type*} [Fintype ι]

/-- The product of actual quotient charts is the standard
torus chart with its specified coordinate punctures. See
Hamilton pp. 64--67 and M76 derivation 270. -/
noncomputable def quotientProductChart (a : ι → ℝ) :
    OpenPartialHomeomorph (ι → AddCircle p) (ι → ℝ) :=
  OpenPartialHomeomorph.pi (fun i => (openPartialHomeomorphCoe p (a i)).symm)

/-- The actual standard torus chart transitions belong to the
existing PL groupoid, including inverse regularity. See
Hamilton pp. 64--67 and M76 derivation 270. -/
theorem quotientProductChart_transition_mem_piecewiseAffineGroupoid (a b : ι → ℝ) :
    (quotientProductChart p a).symm.trans (quotientProductChart p b) ∈
      piecewiseAffineGroupoid (ι → ℝ) := by
  have he : (quotientProductChart p a).symm.trans (quotientProductChart p b) =
      OpenPartialHomeomorph.pi (fun i =>
        (openPartialHomeomorphCoe p (a i)).trans (openPartialHomeomorphCoe p (b i)).symm) := by
    apply OpenPartialHomeomorph.toPartialEquiv_injective
    exact PartialEquiv.pi_trans _ _
  rw [he]
  exact piecewiseAffineGroupoid_pi _
    (fun i => quotient_chart_transition_mem_piecewiseAffineGroupoid p (a i) (b i))

/-- A finite-dimensional torus has an explicit finite family
of compatible standard PL quotient charts. Empty products
are included. This does not compare it with another PL
structure. See Hamilton pp. 64--67 and M76 derivation 270. -/
theorem exists_finite_piecewiseAffine_torus_chart_cover :
    ∃ c : (ι → Bool) → OpenPartialHomeomorph (ι → AddCircle p) (ι → ℝ),
      (∀ x, ∃ b, x ∈ (c b).source) ∧
      ∀ a b, (c a).symm.trans (c b) ∈ piecewiseAffineGroupoid (ι → ℝ) := by
  classical
  let c : (ι → Bool) → OpenPartialHomeomorph (ι → AddCircle p) (ι → ℝ) :=
    fun b => quotientProductChart p (fun i => if b i then 0 else p / 2)
  refine ⟨c, ?_, fun a b =>
    quotientProductChart_transition_mem_piecewiseAffineGroupoid p _ _⟩
  intro x
  choose b hb using fun i => two_puncture_charts_cover p (x i)
  exact ⟨b, fun i _ => hb i⟩

/-- The standard finite torus quotient charts supply an
actual PL charted-space structure on its existing product
topology. See Hamilton pp. 64--67 and M76 derivation 270. -/
theorem exists_piecewiseAffine_torus_chartedSpace :
    ∃ a : ChartedSpace (ι → ℝ) (ι → AddCircle p),
      letI := a
      HasGroupoid (ι → AddCircle p) (piecewiseAffineGroupoid (ι → ℝ)) := by
  obtain ⟨c, hcover, hcompat⟩ := exists_finite_piecewiseAffine_torus_chart_cover (ι := ι) p
  exact ⟨ChartedSpace.ofChartCover c hcover,
    ChartedSpace.hasGroupoid_ofChartCover c hcover _ hcompat⟩

end AddCircle
