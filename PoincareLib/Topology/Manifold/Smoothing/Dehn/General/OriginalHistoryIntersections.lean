import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.OriginalFinalFaceIntersection
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.OriginalFaceDiskState
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.Mathlib.FaceOrderIntersections

/-!
# Actual final double pairs use the constructed face history

Choose the later of the two original minimal source faces. Its actual
recorded motion supplies the endpoint image and comparison complex.
The motion family is chosen once over the original finite order.
Whole-prefix stabilization gives both required map identities, while
retained source charts and the produced support field give all domains.
See Hudson1969, Lemma4.6, and Dehn032, sections4--7.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

/-- Every actual final double pair in the constructed history selects
one of its fixed finite motion family and two unchanged comparison faces. Their
intrinsic interiors contain the literal projected point; their ranks
and cardinality bounds refer to the original two source faces. All
support, chart and prefix obligations follow from the retained history.
See Dehn032, sections4--7 and finite-assembly supplement, section5. -/
theorem Step.exists_history_intersection_faces
    {s t : Stage e S f r C} (step : Step s t)
    {K : SimplicialComplex ℝ V2} (hK : K.faces.Finite)
    {n : ℕ} (order : Fin n → K.faces) (horder : Function.Bijective order)
    (hbefore : ∀ i k, (order k).val ⊂ (order i).val → k < i)
    (P : ℕ → SimplicialComplex ℝ V2)
    (hP : ∀ k, P k ≤ K ∧
      (P k).faces = {a | ∃ i : Fin n, i.val < k ∧ (order i).val = a})
    (hsucc : ∀ i : Fin n, (P (i.val + 1)).space = (P i.val).space ∪
      convexHull ℝ ((order i).val : Set V2))
    (boundary : Fin n → Bool)
    (Q : Fin n → OpenPartialHomeomorph t.Carrier V3)
    (B : Fin n → OpenPartialHomeomorph s.Carrier V3)
    (J : Fin n → SimplicialComplex ℝ V3)
    (hQ : ∀ i k, (t.charts k).symm.trans (Q i) ∈ piecewiseAffineGroupoid V3)
    (hval : ∀ i z, Q i z = B i (step.projection (step.inclusion z)))
    (hmaps : ∀ i, MapsTo (step.projection ∘ step.inclusion) (Q i).source (B i).source)
    (U : K.faces → Set t.Carrier) (hUQ : ∀ i, U (order i) ⊆ (Q i).source)
    {R Fmark : Set M} (states : ℕ → FaceDiskState t K U R Fmark)
    (motions : ∀ i : Fin n,
      FaceMotionData step K (P i.val) (P (i.val + 1)) (states i.val).map
        (Q i) (B i) (J i) U R Fmark (boundary i))
    (htransitions : ∀ i : Fin n,
      (states (i.val + 1)).map = (motions i).ambient 1 ∘ (states i.val).map)
    (hstable : ∀ i k, i ≤ k → k ≤ n →
      EqOn (states k).map (states i).map (P i).space)
    (hcell : ∀ a : K.faces, InjOn ((step.projection ∘ step.inclusion) ∘ (states n).map)
      (convexHull ℝ (a.val : Set V2)))
    {x y : V2} (hx : x ∈ K.space) (hy : y ∈ K.space) (hne : x ≠ y)
    (hxy : step.projection (step.inclusion ((states n).map x)) =
      step.projection (step.inclusion ((states n).map y))) :
    ∃ (i k : Fin n) (x' y' : V2) (old : (P i.val).faces) (a b : Finset V3),
      k < i ∧ ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x)) ∧
      x' ∈ intrinsicInterior ℝ (convexHull ℝ ((order i).val : Set V2)) ∧
      y' ∈ intrinsicInterior ℝ (convexHull ℝ ((order k).val : Set V2)) ∧
      old.val = (order k).val ∧
      (states (i.val + 1)).map = (motions i).ambient 1 ∘ (states i.val).map ∧
      a ∈ (motions i).freeComplex.faces ∧ a ∉ (motions i).fixedComplex.faces ∧
      b ∈ ((motions i).targets old).faces ∧
      Q i ((states n).map x') ∈ intrinsicInterior ℝ
        (convexHull ℝ ((motions i).coordinates.map 1 '' (a : Set V3))) ∧
      B i (step.projection (step.inclusion ((states n).map y'))) ∈
        intrinsicInterior ℝ (convexHull ℝ (b : Set V3)) ∧
      a.card ≤ (order i).val.card ∧ b.card ≤ (order k).val.card ∧
      affineSpan ℝ ((motions i).coordinates.map 1 '' (a : Set V3) ∪ (b : Set V3)) =
        (motions i).plane ∧
      Module.finrank ℝ ((affineSpan ℝ ((motions i).coordinates.map 1 '' (a : Set V3)) ⊓
        affineSpan ℝ (b : Set V3)).direction) + Module.finrank ℝ (motions i).plane.direction =
        (a.card - 1) + (b.card - 1) := by
  obtain ⟨i, k, x', y', hki, hswap, hxface, hyface, hxold, hkold, hpair⟩ :=
    SimplicialComplex.exists_ordered_faces_of_double_pair hK order horder hbefore P
      (fun k => (hP k).2) hcell hx hy hne hxy
  let motion := motions i
  have htransition := htransitions i
  let old : (P i.val).faces := ⟨(order k).val, hkold⟩
  have hinj : InjOn (states i.val).map K.space := by
    intro z hz w hw hzw
    have heq : (⟨z, hz⟩ : K.space) = ⟨w, hw⟩ :=
      (states i.val).embedding.injective hzw
    exact congrArg Subtype.val heq
  have hold := hstable i.val n i.isLt.le le_rfl
  have hnext : EqOn (states n).map (motion.ambient 1 ∘ (states i.val).map)
      (P (i.val + 1)).space := by
    intro z hz
    exact (hstable (i.val + 1) n (by omega) le_rfl hz).trans (congrFun htransition z)
  have hxQ : (states i.val).map x' ∈ (Q i).source :=
    hUQ i ((states i.val).retained (order i) (intrinsicInterior_subset hxface))
  obtain ⟨a, b, ha, ha0, hb, hxa, hyb, hacard, hbcard, hspan, hrank⟩ :=
    motion.exists_final_intersection_faces hK (hP i.val).1 (order i).property (hsucc i)
      (states i.val).original_PL hinj (hQ i) (hval i) (hmaps i) hold hnext
      (intrinsicInterior_subset hxface) hxold hxQ old (intrinsicInterior_subset hyface) hpair
  exact ⟨i, k, x', y', old, a, b, hki, hswap, hxface, hyface, rfl,
    htransition, ha, ha0, hb, hxa, hyb, hacard, hbcard, hspan, hrank⟩

end Geometry.OriginalPLTower
