import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.FinitePairs
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.SurfaceState
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FaceOrderIntersections












set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}






theorem Step.finite_surface_history_original_edge_pairs
    {s t : Stage e S f r C} (step : Step s t)
    {K : SimplicialComplex ℝ V} (hK : K.faces.Finite)
    (hKdim : ∀ c ∈ K.faces, c.card ≤ 3)
    (A : SimplicialComplex ℝ V) (hAdim : ∀ c ∈ A.faces, c.card ≤ 2)
    {n : ℕ} (order : Fin n → K.faces) (horder : Function.Bijective order)
    (hbefore : ∀ i k, (order k).val ⊂ (order i).val → k < i)
    (hphase : ∀ i k, k < i → (order i).val ∈ A.faces → (order k).val ∈ A.faces)
    (P : ℕ → SimplicialComplex ℝ V)
    (hP : ∀ k, P k ≤ K ∧
      (P k).faces = {a | ∃ i : Fin n, i.val < k ∧ (order i).val = a})
    (hsucc : ∀ i : Fin n, (P (i.val + 1)).space = (P i.val).space ∪
      convexHull ℝ ((order i).val : Set V))
    (boundary : Fin n → Bool)
    (hboundary : ∀ i, boundary i = true ↔ (order i).val ∈ A.faces)
    (Q : Fin n → OpenPartialHomeomorph t.Carrier V3)
    (B : Fin n → OpenPartialHomeomorph s.Carrier V3)
    (J : Fin n → SimplicialComplex ℝ V3)
    (hQ : ∀ i k, (t.charts k).symm.trans (Q i) ∈ piecewiseAffineGroupoid V3)
    (hval : ∀ i z, Q i z = B i (step.projection (step.inclusion z)))
    (hmaps : ∀ i, MapsTo (step.projection ∘ step.inclusion) (Q i).source (B i).source)
    (U : K.faces → Set t.Carrier) (hUQ : ∀ i, U (order i) ⊆ (Q i).source)
    {R Fmark : Set M} {rimSet : Set V}
    (states : ℕ → MarkedSurfaceState t K U R Fmark rimSet)
    (motions : ∀ i : Fin n,
      MarkedSurfaceMotionData step K (P i.val) (P (i.val + 1)) (states i.val).map
        (Q i) (B i) (J i) U R Fmark (boundary i))
    (htransitions : ∀ i : Fin n,
      (states (i.val + 1)).map = (motions i).ambient 1 ∘ (states i.val).map)
    (hstable : ∀ i k, i ≤ k → k ≤ n →
      EqOn (states k).map (states i).map (P i).space)
    (hcell : ∀ a : K.faces, InjOn ((step.projection ∘ step.inclusion) ∘ (states n).map)
      (convexHull ℝ (a.val : Set V))) :
    {z : V × V | z.1 ∈ K.space ∧ z.2 ∈ K.space ∧ z.1 ≠ z.2 ∧
      step.projection (step.inclusion ((states n).map z.1)) =
        step.projection (step.inclusion ((states n).map z.2)) ∧
      ∃ a ∈ K.faces, a.card ≤ 2 ∧
        (z.1 ∈ convexHull ℝ (a : Set V) ∨ z.2 ∈ convexHull ℝ (a : Set V))}.Finite := by
  let p : V → s.Carrier := (step.projection ∘ step.inclusion) ∘ (states n).map
  let ordered (i k : Fin n) : Set (V × V) :=
    {z | k < i ∧ ((order i).val.card ≤ 2 ∨ (order k).val.card ≤ 2) ∧
      z.1 ∈ intrinsicInterior ℝ (convexHull ℝ ((order i).val : Set V)) ∧
      z.1 ∉ (P i.val).space ∧
      z.2 ∈ convexHull ℝ ((order k).val : Set V) ∧ p z.1 = p z.2}
  have hinj (l : ℕ) : InjOn (states l).map K.space := by
    intro x hx y hy hxy
    have heq : (⟨x, hx⟩ : K.space) = ⟨y, hy⟩ := (states l).embedding.injective hxy
    exact congrArg Subtype.val heq
  have hfinite (i k : Fin n) : (ordered i k).Finite := by
    by_cases hki : k < i
    · by_cases hsmall : (order i).val.card ≤ 2 ∨ (order k).val.card ≤ 2
      · have hkold : (order k).val ∈ (P i.val).faces :=
          (hP i.val).2.symm.subset ⟨k, hki, rfl⟩
        let old : (P i.val).faces := ⟨(order k).val, hkold⟩
        have hmarked : boundary i = true →
            (order i).val ∈ A.faces ∧ old.val ∈ A.faces := by
          intro hb
          have hiA := (hboundary i).mp hb
          exact ⟨hiA, hphase i k hki hiA⟩
        have hnext : EqOn (states n).map ((motions i).ambient 1 ∘ (states i.val).map)
            (P (i.val + 1)).space := by
          intro x hx
          exact (hstable (i.val + 1) n (by omega) le_rfl hx).trans
            (congrFun (htransitions i) x)
        have hpairfinite := (motions i).finite_original_edge_pairs hK (hP i.val).1
          (order i).property (hsucc i) (states i.val).original_PL (hinj i.val) (hinj n)
          (hQ i) (fun x hx => hUQ i ((states i.val).retained (order i) hx))
          (hval i) (hmaps i) (hstable i.val n i.isLt.le le_rfl) hnext
          hKdim A hAdim old hmarked (Or.inr hsmall) (hcell (order k))
        apply hpairfinite.subset
        intro z hz
        exact ⟨intrinsicInterior_subset hz.2.2.1,
          hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2⟩
      · exact finite_empty.subset (fun _ hz => False.elim (hsmall hz.2.1))
    · exact finite_empty.subset (fun _ hz => False.elim (hki hz.1))
  have hunion : (⋃ i, ⋃ k, ordered i k ∪ Prod.swap '' ordered i k).Finite :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun k =>
      (hfinite i k).union ((hfinite i k).image Prod.swap)
  apply hunion.subset
  intro z hz
  obtain ⟨i, k, x, y, hki, hswap, hx, hy, hxold, _, hpair⟩ :=
    SimplicialComplex.exists_ordered_faces_of_double_pair hK order horder hbefore P
      (fun l => (hP l).2) hcell hz.1 hz.2.1 hz.2.2.1 hz.2.2.2.1
  have hsmall : (order i).val.card ≤ 2 ∨ (order k).val.card ≤ 2 := by
    obtain ⟨a, ha, hacard, hza⟩ := hz.2.2.2.2
    have hbound {l : Fin n} {w : V}
        (hw : w ∈ intrinsicInterior ℝ (convexHull ℝ ((order l).val : Set V)))
        (hwa : w ∈ convexHull ℝ (a : Set V)) : (order l).val.card ≤ 2 :=
      (Finset.card_le_card
        (K.subset_of_mem_intrinsicInterior_face (order l).property ha hw hwa)).trans hacard
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hza.elim (fun h => Or.inl (hbound hx h)) (fun h => Or.inr (hbound hy h))
    · exact hza.elim (fun h => Or.inr (hbound hy h)) (fun h => Or.inl (hbound hx h))
  have hordered : (x, y) ∈ ordered i k :=
    ⟨hki, hsmall, hx, hxold, intrinsicInterior_subset hy, hpair⟩
  refine mem_iUnion₂.mpr ⟨i, k, ?_⟩
  rcases hswap with ⟨hxz, hyz⟩ | ⟨hxz, hyz⟩
  · exact Or.inl ((show (x, y) = z from Prod.ext hxz hyz) ▸ hordered)
  · exact Or.inr ⟨(x, y), hordered, Prod.ext hyz hxz⟩

end Geometry.OriginalPLTower
