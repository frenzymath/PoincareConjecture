import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SelfPairedSourceCircle
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.EndpointLoopPolygon
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.ComponentAxisModel
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedPartnerPL

set_option autoImplicit false
open Set Metric Geometry Topology unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}

theorem OrdinaryDoubleCurveModel.exists_selfpaired_physical_polygon
    (M : OrdinaryDoubleCurveModel e f R)
    (hf : PolyhedralPLInCharts e f D2) (hinside : MapsTo f D2 R)
    (hfrontier : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (i : M.Index) (hself : M.mate i = i)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : X → E) (hF : FinitePiecewiseAffineOn (F ∘ f) (M.pieces i))
    (hFi : InjOn F (f '' M.pieces i)) :
    ∃ (N : ℕ) (Q : Polygon E (N + 3)), Function.Injective Q ∧
      Q.HasSimplicialEdges ∧ Q.boundary ℝ = (F ∘ f) '' M.pieces i := by
  obtain ⟨a, b, U, V, alpha, beta, _, _, _, hcover, _, halpha, _, _, _, _, _, _, _,
    hfib, himage, _⟩ := M.exists_selfpaired_twofold_source_arcs hf hinside hfrontier i hself
  obtain ⟨l, hl, hlval⟩ := halpha
  have hU : U ⊆ M.pieces i := subset_union_left.trans hcover.subset
  have hlmaps : MapsTo l (Icc (0 : ℝ) 1) (M.pieces i) := by
    intro t ht
    rw [← hlval ⟨t, ht⟩]
    exact hU (alpha ⟨t, ht⟩).property
  have hloopPL : FinitePiecewiseAffineOn ((F ∘ f) ∘ l) (Icc (0 : ℝ) 1) :=
    hF.comp hl hlmaps
  have hloopFib : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ((F ∘ f) ∘ l) x = ((F ∘ f) ∘ l) y ↔
        x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
    intro x hx y hy
    have hFiff : F (f (l x)) = F (f (l y)) ↔ f (l x) = f (l y) :=
      ⟨fun h => hFi (mem_image_of_mem f (hlmaps hx))
        (mem_image_of_mem f (hlmaps hy)) h, congrArg F⟩
    change F (f (l x)) = F (f (l y)) ↔ _
    rw [hFiff, ← hlval ⟨x, hx⟩, ← hlval ⟨y, hy⟩, hfib]
    simp only [Subtype.ext_iff]
    rfl
  obtain ⟨N, Q, hQi, hQs, hQb⟩ := exists_polygon_of_endpoint_loop hloopPL hloopFib
  refine ⟨N, Q, hQi, hQs, hQb.trans ?_⟩
  have hlimage : l '' Icc (0 : ℝ) 1 = U := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [← hlval ⟨t, ht⟩]
      exact (alpha ⟨t, ht⟩).property
    · intro hx
      refine ⟨alpha.symm ⟨x, hx⟩, (alpha.symm ⟨x, hx⟩).property, ?_⟩
      rw [← hlval, alpha.apply_symm_apply]
  rw [image_comp (F ∘ f) l, hlimage, image_comp F f, himage, image_comp F f]

theorem OrdinaryDoubleCurveModel.exists_selfpaired_component_axis_model
    (M : OrdinaryDoubleCurveModel e f R)
    (hf : PolyhedralPLInCharts e f D2) (he : PLDomain e R)
    (hinside : MapsTo f D2 R)
    (hfrontier : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (i : M.Index) (hself : M.mate i = i)
    {W : Set X} (hW : IsOpen W) (hAW : f '' M.pieces i ⊆ W) :
    ∃ (s : Finset (f '' M.pieces i)) (F : X → (s → ℝ × V3)) (C : Set X)
      (K A : SimplicialComplex ℝ (s → ℝ × V3))
      (H : C ≃ₜ K.space) (g : (s → ℝ × V3) → C)
      (B : f '' M.pieces i → OpenPartialHomeomorph X V3),
      IsCompact C ∧ f '' M.pieces i ⊆ interior C ∧ C ⊆ W ∧ Continuous F ∧
      (∀ x ∈ C, ∀ y : X, F x = F y → x = y) ∧ K.faces.Finite ∧ A ≤ K ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ A.vertices) → t ∈ A.faces) ∧
      K.space = F '' C ∧ A.space = (F ∘ f) '' M.pieces i ∧
      (∀ x : C, (H x : s → ℝ × V3) = F x) ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z ↦ (g z : X)) K.space ∧
      FinitePiecewiseAffineOn (F ∘ f) (M.pieces i) ∧
      (∀ y, (y : X) ∈ (B y).source ∧ (B y).source ⊆ W ∧
        (∀ k, (e k).symm.trans (B y) ∈ piecewiseAffineGroupoid V3) ∧
        ∀ z ∈ (B y).source,
          z ∈ f '' M.pieces i ↔ z ∈ R ∧ B y z 0 = 0 ∧ B y z 1 = 0) ∧
      (∀ p ∈ A.vertices, ∃ y : f '' M.pieces i,
        MapsTo (fun z ↦ (g z : X)) (K.closedStar p).space (B y).source ∧
        (K.closedStar p).AffineOnFaces (fun z ↦ B y (g z))) ∧
      ∃ (N : ℕ) (Q : Polygon (s → ℝ × V3) (N + 3)),
        Function.Injective Q ∧ Q.HasSimplicialEdges ∧ Q.boundary ℝ = A.space := by
  obtain ⟨P, hP, hPs, _⟩ := (M.models i).finitePL_id
  obtain ⟨s, F, C, K, A, H, g, B, hC, hAC, hCW, hFc, hsep, hK, hAK, hfull,
    hKs, hAs, hH, hg, hgPL, hF, hB, hstar⟩ :=
    M.exists_component_axis_model hf he i P hP hPs hW hAW
  obtain ⟨N, Q, hQi, hQs, hQb⟩ := M.exists_selfpaired_physical_polygon
    hf hinside hfrontier i hself F hF (fun x hx y _ hxy => hsep x (interior_subset (hAC hx)) y hxy)
  exact ⟨s, F, C, K, A, H, g, B, hC, hAC, hCW, hFc, hsep, hK, hAK, hfull,
    hKs, hAs, hH, hg, hgPL, hF, hB, hstar, N, Q, hQi, hQs, hQb.trans hAs.symm⟩

end PoincareConjecture.M76.Dehn
