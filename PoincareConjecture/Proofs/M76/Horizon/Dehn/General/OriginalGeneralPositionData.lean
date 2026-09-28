import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgeryOldGerms

set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {R Fmark : Set M}
  {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}

structure OriginalGeneralPositionData (step : Step s t)
    (old : StageMarkedDisk t R Fmark base Jgroup) where
  initial : StageMarkedDisk t R Fmark base Jgroup
  eta : old.rim.Homotopy initial.rim
  K : SimplicialComplex ℝ V2
  A : SimplicialComplex ℝ V2
  basepath : initial.basepath = old.basepath.trans (eta.evalAt squareRimBase)
  source_finite : K.faces.Finite
  source_space : K.space = D2
  boundary_finite : A.faces.Finite
  boundary_subcomplex : A ≤ K
  boundary_space : A.space = Q2
  length : ℕ
  order : Fin length → K.faces
  previous : ℕ → SimplicialComplex ℝ V2
  boundary : Fin length → Bool
  upperChart : Fin length → OpenPartialHomeomorph t.Carrier V3
  lowerChart : Fin length → OpenPartialHomeomorph s.Carrier V3
  carrier : Fin length → SimplicialComplex ℝ V3
  window : K.faces → Set t.Carrier
  states : ℕ → FaceDiskState t K window R Fmark
  motions : ∀ i : Fin length, FaceMotionData step K (previous i.val)
    (previous (i.val + 1)) (states i.val).map (upperChart i) (lowerChart i)
    (carrier i) window R Fmark (boundary i)
  order_bijective : Function.Bijective order
  order_before : ∀ i k, (order k).val ⊂ (order i).val → k < i
  boundary_phase : ∀ i k, k < i → (order i).val ∈ A.faces → (order k).val ∈ A.faces
  previous_faces : ∀ k, previous k ≤ K ∧
    (previous k).faces = {a | ∃ i : Fin length, i.val < k ∧ (order i).val = a}
  successor_space : ∀ i : Fin length, (previous (i.val + 1)).space =
    (previous i.val).space ∪ convexHull ℝ ((order i).val : Set V2)
  boundary_iff : ∀ i, boundary i = true ↔ (order i).val ∈ A.faces
  upper_compatible : ∀ i k,
    (t.charts k).symm.trans (upperChart i) ∈ piecewiseAffineGroupoid V3
  lower_compatible : ∀ i k,
    (s.charts k).symm.trans (lowerChart i) ∈ piecewiseAffineGroupoid V3
  chart_values : ∀ i z,
    upperChart i z = lowerChart i (step.projection (step.inclusion z))
  chart_mapsTo : ∀ i, MapsTo (step.projection ∘ step.inclusion)
    (upperChart i).source (lowerChart i).source
  window_subset : ∀ i, window (order i) ⊆ (upperChart i).source
  first_state : (states 0).map = old.map
  final_state : initial.map = (states length).map
  transitions : ∀ i : Fin length,
    (states (i.val + 1)).map = (motions i).ambient 1 ∘ (states i.val).map
  stable : ∀ i k, i ≤ k → k ≤ length →
    EqOn (states k).map (states i).map (previous i).space
  cell_injective : ∀ a : K.faces,
    InjOn ((step.projection ∘ step.inclusion) ∘ initial.map)
      (convexHull ℝ (a.val : Set V2))
  relation : SimplicialComplex ℝ (V2 × V2)
  locus : SimplicialComplex ℝ V2
  first : relation.space ≃ₜ locus.space
  exceptional : Set (V2 × V2)
  relation_finite : relation.faces.Finite
  locus_finite : locus.faces.Finite
  relation_space : relation.space = {z | z.1 ∈ D2 ∧ z.2 ∈ D2 ∧
    step.projection (step.inclusion (initial.map z.1)) =
      step.projection (step.inclusion (initial.map z.2)) ∧ z.1 ≠ z.2}
  locus_space : locus.space = {x | x ∈ D2 ∧ ∃ y ∈ D2, x ≠ y ∧
    step.projection (step.inclusion (initial.map x)) =
      step.projection (step.inclusion (initial.map y))}
  relation_dimension : ∀ a ∈ relation.faces, a.card ≤ 2
  locus_dimension : ∀ a ∈ locus.faces, a.card ≤ 2
  first_PL : first.IsFinitePL
  first_inverse_PL : first.symm.IsFinitePL
  first_value : ∀ z : relation.space, (first z : V2) = z.val.1
  exceptional_finite : exceptional.Finite
  exceptional_eq : exceptional = {z | z ∈ relation.space ∧
    ∃ a ∈ K.faces, a.card ≤ 2 ∧
      (z.1 ∈ convexHull ℝ (a : Set V2) ∨ z.2 ∈ convexHull ℝ (a : Set V2))}
  crossings : ∀ a b : D2, a ≠ b →
    step.projection (step.inclusion (initial.map a)) =
      step.projection (step.inclusion (initial.map b)) →
    ((a : V2), (b : V2)) ∉ exceptional →
    ∀ W : Set s.Carrier, IsOpen W →
      step.projection (step.inclusion (initial.map a)) ∈ W →
      ∃ (a' b' : D2) (w : TwoBranchWindow (step.projection ∘ step.inclusion))
        (c : V3 ≃L[ℝ] C3) (T : OpenPartialHomeomorph s.Carrier V3),
        ((a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a)) ∧
        initial.map a' ∈ w.left.source ∧ initial.map b' ∈ w.right.source ∧
        step.projection (step.inclusion (initial.map a)) ∈ T.source ∧
        T.source ⊆ W ∩ (interior (s.projection ⁻¹' R) ∩ w.target) ∧
        T (step.projection (step.inclusion (initial.map a))) = 0 ∧
        (∀ k, (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
        (∀ k, (t.charts k).symm.trans (w.left.trans T) ∈ piecewiseAffineGroupoid V3 ∧
          (t.charts k).symm.trans (w.right.trans T) ∈ piecewiseAffineGroupoid V3) ∧
        (step.projection ∘ step.inclusion) ⁻¹' T.source =
          (w.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∪
            (w.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∧
        (∀ y ∈ T.source, y ∈ (step.projection ∘ step.inclusion) ''
          (initial.map '' D2 ∩ w.left.source) ↔ (c (T y)).2 = 0) ∧
        ∀ y ∈ T.source, y ∈ (step.projection ∘ step.inclusion) ''
          (initial.map '' D2 ∩ w.right.source) ↔ (c (T y)).1.1 = 0

theorem Step.nonempty_originalGeneralPositionData (step : Step s t)
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    (old : StageMarkedDisk t R Fmark base Jgroup) :
    Nonempty (OriginalGeneralPositionData step old) := by
  obtain ⟨initial, eta, K, A, hpath, hK, hKs, hA, hAK, hAs,
    n, order, P, boundary, Q, B, J, U, states, motions,
    horder, hbefore, hphase, hP, hsucc, hboundary, hQ, hB, hval, hmaps, hUQ,
    hstart, hend, htrans, hstable, hcell,
    Z, G, first, E, hZ, hG, hZs, hGs, hZdim, hGdim,
    hfirst, hinverse, hfirstval, hE, hEs, hcross⟩ :=
    step.exists_original_old_crossing_assembly he hF hopen old
  exact ⟨⟨initial, eta, K, A, hpath, hK, hKs, hA, hAK, hAs,
    n, order, P, boundary, Q, B, J, U, states, motions,
    horder, hbefore, hphase, hP, hsucc, hboundary, hQ, hB, hval, hmaps, hUQ,
    hstart, hend, htrans, hstable, hcell,
    Z, G, first, E, hZ, hG, hZs, hGs, hZdim, hGdim,
    hfirst, hinverse, hfirstval, hE, hEs, hcross⟩⟩

noncomputable def Step.originalGeneralPositionData (step : Step s t)
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    (old : StageMarkedDisk t R Fmark base Jgroup) : OriginalGeneralPositionData step old :=
  Classical.choice (step.nonempty_originalGeneralPositionData he hF hopen old)

end Geometry.OriginalPLTower
