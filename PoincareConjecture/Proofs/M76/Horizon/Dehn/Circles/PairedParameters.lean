import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.PairedComponentNeighborhoods
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquarePolygonUniformBoundary
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem OrdinaryDoubleCurveModel.exists_paired_circle_parameters
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (old : OrdinaryDoubleCurveModel e f R) (hf : PolyhedralPLInCharts e f D2)
    (hin : MapsTo f D2 R) (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (i : old.Index) (hi : old.mate i ≠ i)
    {n : ℕ} (P : Polygon V2 (n + 3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) (hPs : P.boundary ℝ = old.pieces i)
    (hQ : Disjoint (old.pieces i) Q2) :
    ∃ (a : Q2 ≃ₜ old.pieces i) (b : Q2 ≃ₜ old.pieces (old.mate i)) (circle : V2 → X),
      a.IsFinitePL ∧ b.IsFinitePL ∧
      (∀ u : Q2, ∃ hx : (a u : V2) ∈ doubleLocusOn f D2,
        (b u : V2) = (old.partner ⟨a u, hx⟩ : V2)) ∧
      IsEmbedding (fun u : Q2 ↦ circle u) ∧ PolyhedralPLInCharts e circle Q2 ∧
      (∀ u : Q2, circle u = f (a u) ∧ circle u = f (b u)) ∧
      circle '' Q2 = f '' old.pieces i ∧ MapsTo circle Q2 (interior R) ∧
      ∀ x ∈ D2, f x ∈ circle '' Q2 ↔ x ∈ old.pieces i ∪ old.pieces (old.mate i) := by
  obtain ⟨a0, ha0, _, _⟩ := exists_square_polygon_uniform_boundary P hP hPi
  let a : Q2 ≃ₜ old.pieces i := a0.trans (Homeomorph.setCongr hPs)
  have ha : a.IsFinitePL := by
    obtain ⟨l, hl, hlval⟩ := ha0
    exact ⟨l, hl, hlval⟩
  obtain ⟨l, hl, hlval⟩ := ha
  have hlimage : l '' Q2 = old.pieces i := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [← hlval ⟨u, hu⟩]
      exact (a ⟨u, hu⟩).property
    · intro hx
      refine ⟨a.symm ⟨x, hx⟩, (a.symm ⟨x, hx⟩).property, ?_⟩
      rw [← hlval, a.apply_symm_apply]
  obtain ⟨K, hK, hKs⟩ := hl.exists_finite_triangulation_image
  have hKi : K.space = old.pieces i := hKs.trans hlimage
  let d := old.partner.restrictSubsets (old.piece_subset_double i)
    (old.piece_subset_double (old.mate i)) (old.partner_component_iff i)
  have hd : d.IsFinitePL := old.partnerPL.restrictSubsets (old.piece_subset_double i)
    (old.piece_subset_double (old.mate i)) (old.partner_component_iff i) K hK hKi
  let b := a.trans d
  have hb : b.IsFinitePL := (show a.IsFinitePL from ⟨l, hl, hlval⟩).trans hd
  let circle := f ∘ l
  have hcval (u : Q2) : circle u = f (a u) := congrArg f (hlval u).symm
  have hcval' (u : Q2) : circle u = f (b u) :=
    (hcval u).trans (old.partner_value ⟨a u, old.piece_subset_double i (a u).property⟩).symm
  have hlD : MapsTo l Q2 D2 := fun x hx ↦
    (old.piece_subset_double i (hlimage.subset ⟨x, hx, rfl⟩)).1
  have hcPL : PolyhedralPLInCharts e circle Q2 := by
    obtain ⟨J, hJ, hJs, hJa⟩ := hl
    have h := hf.comp_finitePiecewiseAffineOn J hJ
      (show FinitePiecewiseAffineOn l J.space from ⟨J, hJ, rfl, hJa⟩)
      (by simpa only [hJs] using hlD)
    simpa only [hJs] using h
  have hci : Function.Injective (fun u : Q2 ↦ circle u) := by
    intro u v huv
    exact a.injective (Subtype.ext ((old.injOn_piece_of_mate_ne i hi)
      (a u).property (a v).property ((hcval u).symm.trans (huv.trans (hcval v)))))
  have himage : circle '' Q2 = f '' old.pieces i := by
    rw [← hlimage, ← image_comp]
  have hinside : MapsTo circle Q2 (interior R) := by
    intro u hu
    rw [hcval ⟨u, hu⟩]
    have hx := old.piece_subset_double i (a ⟨u, hu⟩).property
    have hfR := hin hx.1
    have hn : f (a ⟨u, hu⟩) ∉ frontier R := fun h ↦
      disjoint_left.mp hQ (a ⟨u, hu⟩).property ((hfront _ hx.1).mp h)
    by_contra hni
    exact hn ⟨subset_closure hfR, hni⟩
  refine ⟨a, b, circle, ⟨l, hl, hlval⟩, hb,
    fun u ↦ ⟨old.piece_subset_double i (a u).property, rfl⟩,
    (hcPL.continuousOn.domRestrict.isClosedEmbedding hci).isEmbedding,
    hcPL, fun u ↦ ⟨hcval u, hcval' u⟩, himage, hinside, ?_⟩
  intro x hx
  rw [himage]
  exact old.piece_image_preimage i x hx

end PoincareConjecture.M76.Dehn
