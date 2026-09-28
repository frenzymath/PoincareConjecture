import PoincareConjecture.Proofs.M76.Mathlib.AddCirclePLCharts
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffinePi
import PoincareConjecture.Proofs.M76.Mathlib.AtlasOfCover

set_option autoImplicit false

open Set Geometry

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]

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

noncomputable def quotientProductChart (a : ι → ℝ) :
    OpenPartialHomeomorph (ι → AddCircle p) (ι → ℝ) :=
  OpenPartialHomeomorph.pi (fun i => (openPartialHomeomorphCoe p (a i)).symm)

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

theorem exists_piecewiseAffine_torus_chartedSpace :
    ∃ a : ChartedSpace (ι → ℝ) (ι → AddCircle p),
      letI := a
      HasGroupoid (ι → AddCircle p) (piecewiseAffineGroupoid (ι → ℝ)) := by
  obtain ⟨c, hcover, hcompat⟩ := exists_finite_piecewiseAffine_torus_chart_cover (ι := ι) p
  exact ⟨ChartedSpace.ofChartCover c hcover,
    ChartedSpace.hasGroupoid_ofChartCover c hcover _ hcompat⟩

end AddCircle
