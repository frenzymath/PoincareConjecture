import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.PeriodicLift
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.PeriodicSquare

local notation "P2" => (ℝ × ℝ)

theorem SourceSquareMap.polyhedralPL_torus_translation
    {E Z V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E} {S : Set X}
    (M : SourceSquareMap p K) (H : K.space ≃ₜ S)
    (F : E → X) (hF : PolyhedralPLInCharts e F K.space)
    (hFval : ∀ x : K.space, F x = (H x : X))
    (h : (AddCircle p × AddCircle p) ≃ₜ S)
    (hvalue : ∀ z : Square p, h (projection p z) = H (M.map z))
    (J : SimplicialComplex ℝ Z) (hJ : J.faces.Finite)
    (k : Z → AddCircle p × AddCircle p) (hk : ContinuousOn k J.space)
    (hf : PolyhedralPLInCharts e (fun z => (h (k z) : X)) J.space)
    (v : Z → P2) (hv : FinitePiecewiseAffineOn v J.space) :
    PolyhedralPLInCharts e
      (fun z => (h (k z + (((v z).1 : AddCircle p), ((v z).2 : AddCircle p))) : X)) J.space := by
  have hp : 0 < p := Fact.out
  let g (z : Z) : X := h (k z + (((v z).1 : AddCircle p), ((v z).2 : AddCircle p)))
  have hgc : ContinuousOn g J.space :=
    continuous_subtype_val.comp_continuousOn (h.continuous.comp_continuousOn
      (hk.add ((AddCircle.continuous_mk' p).comp_continuousOn hv.continuousOn.fst |>.prodMk
        ((AddCircle.continuous_mk' p).comp_continuousOn hv.continuousOn.snd))))
  refine ⟨hgc, ?_⟩
  intro x
  obtain ⟨a, ha⟩ := surjective_projection p (k x)
  let Q := (AddCircle.openPartialHomeomorphCoe p ((a.1 : ℝ) - p / 2)).prod
    (AddCircle.openPartialHomeomorphCoe p ((a.2 : ℝ) - p / 2))
  have haQ : ((a.1 : ℝ), (a.2 : ℝ)) ∈ Q.source := by
    change ((a.1 : ℝ) ∈ Ioo ((a.1 : ℝ) - p / 2) ((a.1 : ℝ) - p / 2 + p)) ∧
      ((a.2 : ℝ) ∈ Ioo ((a.2 : ℝ) - p / 2) ((a.2 : ℝ) - p / 2 + p))
    constructor <;> constructor <;> linarith
  have hxQ : k x ∈ Q.target := ha ▸ Q.map_source haQ
  obtain ⟨N, W, hN, hNJ, hW, hxW, hWN, hNQ⟩ :=
    J.exists_relative_polyhedral_neighborhood hJ x
      (Q.open_target.preimage hk.domRestrict) hxQ
  have hnQ (z : Z) (hz : z ∈ N.space) : k z ∈ Q.target :=
    hNQ (show (⟨z, hNJ hz⟩ : J.space) ∈ Subtype.val ⁻¹' N.space from hz)
  let r : Z → P2 := Q.symm ∘ k
  have hrc : ContinuousOn r N.space :=
    Q.symm.continuousOn.comp (hk.mono hNJ) (fun z hz => hnQ z hz)
  have hrval (z : Z) (hz : z ∈ N.space) :
      (((r z).1 : AddCircle p), ((r z).2 : AddCircle p)) = k z := Q.right_inv (hnQ z hz)
  have hfr : PolyhedralPLInCharts e
      (fun z => (h (((r z).1 : AddCircle p), ((r z).2 : AddCircle p)) : X)) N.space :=
    (hf.restrict_finite N hN hNJ).congr (fun z hz => by rw [hrval z hz])
  have hr := M.finitePiecewiseAffineOn_periodic_lift hcompat H F hF hFval h hvalue N hN hrc hfr
  have htranslated := M.polyhedralPL_periodic_comp H F hF hFval h hvalue N hN
    (hr.add (hv.restrict N hN hNJ))
  have hgN : PolyhedralPLInCharts e g N.space := htranslated.congr (by
    intro z hz
    change (h (((r z + v z).1 : AddCircle p), ((r z + v z).2 : AddCircle p)) : X) = _
    simp only [Prod.fst_add, Prod.snd_add, AddCircle.coe_add]
    change (h ((((r z).1 : AddCircle p), ((r z).2 : AddCircle p)) +
      (((v z).1 : AddCircle p), ((v z).2 : AddCircle p))) : X) = _
    rw [hrval z hz])
  have hxN : (x : Z) ∈ N.space := hWN ⟨x, hxW, rfl⟩
  obtain ⟨i, L, U, hL, hLN, hU, hxU, hUL, htarget, hformula⟩ := hgN.coordinates ⟨x, hxN⟩
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.mp hU
  have hxO : (x : Z) ∈ O := by
    change (⟨x, hxN⟩ : N.space) ∈ Subtype.val ⁻¹' O
    rw [hOU]
    exact hxU
  refine ⟨i, L, W ∩ (Subtype.val : J.space → Z) ⁻¹' O, hL, hLN.trans hNJ,
    hW.inter (hO.preimage continuous_subtype_val), ⟨hxW, hxO⟩, ?_, htarget, hformula⟩
  rintro z ⟨y, hy, rfl⟩
  have hyN : (y : Z) ∈ N.space := hWN ⟨y, hy.1, rfl⟩
  have hyU : (⟨y, hyN⟩ : N.space) ∈ U := by rw [← hOU]; exact hy.2
  exact hUL ⟨⟨y, hyN⟩, hyU, rfl⟩

end PoincareConjecture.M76.PeriodicSquare
