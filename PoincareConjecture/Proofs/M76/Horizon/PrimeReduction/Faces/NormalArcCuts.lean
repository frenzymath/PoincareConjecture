import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NormalFaceArcFamily
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.AffineTriangleComponents
import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalBoundary
import PoincareConjecture.Proofs.M76.PrimeReduction.ReturningFaceCoordinates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Arcs.InnermostReturningContacts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProperArcCut
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCircleArcs











noncomputable section
set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

theorem isFinitePLBallPair_independent_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (hind : AffineIndependent ℝ ((↑) : s → E)) (hcard : s.card = 3) :
    IsFinitePLBallPair (ℝ × ℝ) (convexHull ℝ (s : Set E))
      (intrinsicFrontier ℝ (convexHull ℝ (s : Set E))) := by
  classical
  let hi : ∀ a ∈ ({s} : Set (Finset E)), AffineIndependent ℝ ((↑) : a → E) := by
    rintro a rfl
    exact hind
  let hx : ∀ a ∈ ({s} : Set (Finset E)), ∀ b ∈ ({s} : Set (Finset E)),
      convexHull ℝ (a : Set E) ∩ convexHull ℝ (b : Set E) ⊆
        convexHull ℝ ((a : Set E) ∩ b) := by
    rintro a rfl b rfl
    simp
  let K := SimplicialComplex.ofGenerators {s} hi hx
  have hs : s ∈ K.faces := by
    exact ⟨Finset.card_pos.mp (by omega), s, by simp, Finset.Subset.rfl⟩
  obtain ⟨v0, v1, v2, h01, h02, h12, hverts⟩ := Finset.card_eq_three.mp hcard
  obtain ⟨F, R, hRF, _, _, _, _, hface, _⟩ :=
    K.exists_returning_face_coordinates h01 h02 h12 (hverts ▸ hs)
  let Δ := convexHull ℝ (range TriangleDiskModel.rightTriangle)
  have htarget : F '' Δ = convexHull ℝ (s : Set E) := by
    simpa only [hverts, Finset.coe_insert, Finset.coe_singleton] using hface
  have hmodel := (TriangleDiskModel.rightTriangle.isFinitePLBallPair_convexHull_triangle
    TriangleDiskModel.independent_rightTriangle).affine_image F hRF.injective.injOn
  have hrim : F '' frontier Δ = intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyΔ : y ∈ Δ :=
        ((Set.finite_range _).isCompact_convexHull ℝ).isClosed.frontier_subset hy
      have hFx := htarget.subset (mem_image_of_mem F hyΔ)
      apply (affine_triangle_frontier_coordinates F R hRF htarget hFx).mp
      rwa [hRF y]
    · intro hx
      have hxT : x ∈ convexHull ℝ (s : Set E) := by
        have hc := frontier_subset_closure (intrinsicFrontier_subset_frontier hx)
        simpa only [s.finite_toSet.isCompact_convexHull ℝ |>.isClosed.closure_eq] using hc
      obtain ⟨y, hy, rfl⟩ := htarget.symm.subset hxT
      refine ⟨y, ?_, rfl⟩
      have hh := (affine_triangle_frontier_coordinates F R hRF htarget
        (htarget.subset (mem_image_of_mem F hy))).mpr hx
      rwa [hRF y] at hh
  rw [htarget, hrim] at hmodel
  exact hmodel




theorem exists_normal_arc_cut_with_allocation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} {T B : Set E} (hT : IsFinitePLBallPair (ℝ × ℝ) T B)
    (d r : ι → Set E) (hd : ∀ i, IsFinitePLBallPair ℝ (d i) (r i))
    (hsub : ∀ i, d i ⊆ T) (hrim : ∀ i, r i = d i ∩ B)
    (hdis : Pairwise fun i j => Disjoint (d i) (d j)) (i : ι) :
    ∃ (U C : Bool → Set E),
      (∀ b, IsFinitePLBallPair ℝ (U b) (r i)) ∧
      U false ∪ U true = B ∧ U false ∩ U true = r i ∧
      (∀ b, IsFinitePLBallPair (ℝ × ℝ) (C b) (U b ∪ d i)) ∧
      C false ∪ C true = T ∧ C false ∩ C true = d i ∧
      (∀ b, C b ∩ B = U b) ∧
      ∀ j, j ≠ i → ∃! b : Bool, d j ⊆ C b \ d i := by
  classical
  obtain ⟨a, b, hab, habr⟩ := (hd i).exists_boundary_eq_pair
  have ha : a ∈ B := (hrim i ▸ (habr.symm ▸ (show a ∈ ({a, b} : Set E) by simp))).2
  have hb : b ∈ B := (hrim i ▸ (habr.symm ▸ (show b ∈ ({a, b} : Set E) by simp))).2
  obtain ⟨U, V, hU, hV, hUV, hcommon⟩ := hT.exists_boundary_arcs ha hb hab
  have hproper : d i \ {a, b} ⊆ T \ B := by
    intro x hx
    refine ⟨hsub i hx.1, ?_⟩
    intro hxB
    exact hx.2 (habr ▸ ((hrim i).symm ▸ ⟨hx.1, hxB⟩))
  obtain ⟨C, D, hC, hD, hCD, hinter, hCB, hDB⟩ :=
    hT.exists_proper_arc_cut hU hV (habr ▸ hd i) hab hcommon.subset hUV hproper
  let A : Bool → Set E := fun b => if b then V else U
  let P : Bool → Set E := fun b => if b then D else C
  have hPball (b) : IsFinitePLBallPair (ℝ × ℝ) (P b) (A b ∪ d i) := by
    cases b
    · exact hC
    · simpa only [P, A, if_pos, union_comm] using hD
  refine ⟨A, P, ?_, hUV, habr.symm ▸ hcommon, hPball, hCD, hinter, ?_, ?_⟩
  · intro c
    cases c
    · simpa only [A, Bool.false_eq_true, if_false, habr] using hU
    · simpa only [A, if_true, habr] using hV
  · intro b
    cases b <;> assumption
  · intro j hji
    have hjmiss : Disjoint (d j) (d i) := hdis hji
    have hcover : d j ⊆ C ∪ D := (hsub j).trans hCD.symm.subset
    have hside : d j ⊆ C ∨ d j ⊆ D := by
      by_cases hc : d j ⊆ C
      · exact Or.inl hc
      · right
        obtain ⟨x, hx, hxC⟩ := not_subset.mp hc
        have hxD := (hcover hx).resolve_left hxC
        intro y hy
        by_contra hyD
        have hyC := (hcover hy).resolve_right hyD
        obtain ⟨z, hz, hzC, hzD⟩ := isPreconnected_closed_iff.mp (hd j).isConnected.isPreconnected
          C D hC.isCompact.isClosed hD.isCompact.isClosed hcover
          ⟨y, hy, hyC⟩ ⟨x, hx, hxD⟩
        exact disjoint_left.mp hjmiss hz (hinter.subset ⟨hzC, hzD⟩)
    have hchoose : ∃ b : Bool, d j ⊆ P b \ d i := by
      rcases hside with hside | hside
      · exact ⟨false, fun z hz => ⟨hside hz, disjoint_left.mp hjmiss hz⟩⟩
      · exact ⟨true, fun z hz => ⟨hside hz, disjoint_left.mp hjmiss hz⟩⟩
    obtain ⟨b, hb⟩ := hchoose
    refine ⟨b, hb, ?_⟩
    intro c hc
    obtain ⟨z, hz⟩ := (hd j).isConnected.nonempty
    by_contra hcb
    cases b <;> cases c
    · exact hcb rfl
    · exact (hb hz).2 (hinter.subset ⟨(hb hz).1, (hc hz).1⟩)
    · exact (hb hz).2 (hinter.subset ⟨(hc hz).1, (hb hz).1⟩)
    · exact hcb rfl

local notation "V3" => (Fin 3 → ℝ)



theorem InCircleFreeNonreturningTriangleGraphPosition.exists_normal_arc_cuts
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {S : Set X} (hposition : InCircleFreeNonreturningTriangleGraphPosition Q S g s A) :
    ∃ (γ : Type) (_ : Finite γ) (d r : γ → Set V3),
      (Pairwise fun i j => Disjoint (d i) (d j)) ∧
      Q.symm '' (⋃ i, d i) = S ∩ (g '' convexHull ℝ (s : Set E)) ∧
      (⋃ i, d i) ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target ∧
      (∀ i, IsFinitePLBallPair ℝ (d i) (r i) ∧
        r i = d i ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))) ∧
      ∀ i, ∃ (U C : Bool → Set V3),
        (∀ b, IsFinitePLBallPair ℝ (U b) (r i)) ∧
        U false ∪ U true = intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) ∧
        U false ∩ U true = r i ∧
        (∀ b, IsFinitePLBallPair (ℝ × ℝ) (C b) (U b ∪ d i)) ∧
        C false ∪ C true = convexHull ℝ (A '' (s : Set E)) ∧
        C false ∩ C true = d i ∧
        (∀ b, C b ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = U b) ∧
        ∀ j, j ≠ i → ∃! b : Bool, d j ⊆ C b \ d i := by
  classical
  obtain ⟨γ, hγ, d, r, hdis, hphysical, htarget, harcs⟩ :=
    hposition.exists_normal_arc_family K g hgi hs Q A hmap hA
  have hAi : InjOn A (s : Set E) := by
    intro x hx y hy hxy
    have hx' := subset_convexHull ℝ (s : Set E) hx
    have hy' := subset_convexHull ℝ (s : Set E) hy
    exact hgi (K.convexHull_subset_space hs hx') (K.convexHull_subset_space hs hy')
      (Q.injOn (hmap hx') (hmap hy') ((hA hx').trans (hxy.trans (hA hy').symm)))
  have hind : AffineIndependent ℝ ((↑) : (s.image A) → V3) := by
    change AffineIndependent ℝ ((↑) : ↥((s.image A : Finset V3) : Set V3) → V3)
    rw [Finset.coe_image]
    exact affineIndependent_original_face_chart K g hgi hs Q A hmap hA
  have hcard : (s.image A).card = 3 := by
    rw [Finset.card_image_of_injOn hAi, hs3]
  have htriangle := isFinitePLBallPair_independent_triangle (s.image A) hind hcard
  rw [Finset.coe_image] at htriangle
  refine ⟨γ, hγ, d, r, hdis, hphysical, htarget,
    fun i => ⟨(harcs i).1, (harcs i).2.1⟩, fun i => ?_⟩
  exact exists_normal_arc_cut_with_allocation htriangle d r (fun j => (harcs j).1)
    (fun j x hx => (htarget (mem_iUnion.mpr ⟨j, hx⟩)).1)
    (fun j => (harcs j).2.1) hdis i

end PoincareConjecture.M76
