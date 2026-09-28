import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineCellLiftMarks
import PoincareConjecture.Proofs.M76.Mathlib.TwoSheetLiftImageCollision
import PoincareConjecture.Proofs.M76.Mathlib.FixedSourceLiftVertexCount
import PoincareConjecture.Proofs.M76.Mathlib.FinitePiecewiseAffine

set_option autoImplicit false

universe w z

open Set Topology

namespace Geometry

theorem exists_finite_marks_strict_two_sheet_count
    {U V ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
    (D : Set U) (hD : D.Nonempty) (C : ι → Set U)
    (hcompact : ∀ i, IsCompact (C i)) (hconvex : ∀ i, Convex ℝ (C i))
    (hcover : D = ⋃ i, C i)
    (F : U → V) (A : ι → U →ᴬ[ℝ] V) (hF : ∀ i, EqOn F (A i) (C i)) :
    ∃ S : Set D, S.Finite ∧
      ∀ (X : Type z) [TopologicalSpace X] (q : X → V), IsLocallyInjective q →
        ∀ (E : Type w) [TopologicalSpace E] [T2Space E] [ConnectedSpace E]
          (p : E → X), IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) →
          ∀ (f : C(D, X)), (∀ u, q (f u) = F u) →
          ∀ (g : C(D, E)), (∀ u, p (g u) = f u) →
          ∀ (r : C(X, X)), (ContinuousMap.id X).HomotopyRel r (range f) →
            (∀ x, r x ∈ range f) →
            (f '' S).ncard < (g '' S).ncard ∧ (g '' S).ncard ≤ S.ncard ∧
              S.ncard - (g '' S).ncard < S.ncard - (f '' S).ncard := by
  obtain ⟨S, hS, hmarks⟩ :=
    exists_finite_marks_for_affine_cell_lifts D C hcompact hconvex hcover F A hF
  have hcompactD : IsCompact D := by
    rw [hcover]
    exact isCompact_iUnion hcompact
  let : CompactSpace D := isCompact_iff_compactSpace.mp hcompactD
  let : Nonempty D := hD.to_subtype
  refine ⟨S, hS, ?_⟩
  intro X instX q hq E instE instT2 instConn p hp hcard f hqf g hpg r H hr
  obtain ⟨T, hTp, _, hTne, _, a0, b0, hab0, _, _⟩ :=
    hp.exists_two_sheet_lift_image_collision hcard f g hpg H hr
  have hmeet : (range g ∩ T '' range g).Nonempty :=
    ⟨g a0, mem_range_self a0, ⟨g b0, mem_range_self b0, hab0.symm⟩⟩
  have hqp : IsLocallyInjective (q ∘ p) :=
    hq.comp hp.isLocalHomeomorph.isLocallyInjective hp.continuous
  obtain ⟨a, ha, b, hb, hab, hne⟩ := hmarks E (q ∘ p) hqp g
    (fun u => (congrArg q (hpg u)).trans (hqf u)) T
    (fun e => congrArg q (hTp e)) hTne hmeet
  have heq : f a = f b := (hpg a).symm.trans
    ((congrArg p hab).trans ((hTp (g b)).trans (hpg b)))
  exact Set.ncard_image_lt_of_fixed_source_lift_collision hS
    (fun u _ => hpg u) ha hb hne heq

theorem FinitePiecewiseAffineOn.exists_strict_two_sheet_count
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : U → V} {D : Set U} (hF : FinitePiecewiseAffineOn F D) (hD : D.Nonempty) :
    ∃ S : Set D, S.Finite ∧
      ∀ (X : Type z) [TopologicalSpace X] (q : X → V), IsLocallyInjective q →
        ∀ (E : Type w) [TopologicalSpace E] [T2Space E] [ConnectedSpace E]
          (p : E → X), IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) →
          ∀ (f : C(D, X)), (∀ u, q (f u) = F u) →
          ∀ (g : C(D, E)), (∀ u, p (g u) = f u) →
          ∀ (r : C(X, X)), (ContinuousMap.id X).HomotopyRel r (range f) →
            (∀ x, r x ∈ range f) →
            (f '' S).ncard < (g '' S).ncard ∧ (g '' S).ncard ≤ S.ncard ∧
              S.ncard - (g '' S).ncard < S.ncard - (f '' S).ncard := by
  classical
  obtain ⟨K, hK, hKD, hFK⟩ := hF
  let : Finite K.faces := hK.to_subtype
  choose A hA using fun s : K.faces => hFK s.val s.property
  have hcover : D = ⋃ s : K.faces, convexHull ℝ (s.val : Set U) := by
    rw [← hKD]
    ext x
    simp only [SimplicialComplex.mem_space_iff, mem_iUnion, Subtype.exists, exists_prop]
  exact exists_finite_marks_strict_two_sheet_count D hD
    (fun s : K.faces => convexHull ℝ (s.val : Set U))
    (fun s => s.val.finite_toSet.isCompact_convexHull ℝ)
    (fun s => convex_convexHull ℝ (s.val : Set U)) hcover F A hA

end Geometry
