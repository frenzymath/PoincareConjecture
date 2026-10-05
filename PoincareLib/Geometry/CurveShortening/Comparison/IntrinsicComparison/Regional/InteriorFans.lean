import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Metric.InteriorFan
import PoincareLib.Geometry.Riemannian.Surface.GaussBonnet.VertexIncidence

/-!
# Interior fans of the actual regional triangulation

Compatibility identifies the unique corner of every incident face.
Removing the finitely many nonincident closed faces preserves a
neighborhood of the vertex. The proved metric fan then evaluates the
literal canonical vertex contribution used by regional Gauss-Bonnet.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, especially Claim 19.40, pp.
470-471. The explicit coordinate-mesh and regional Gauss--Bonnet constructions are project
derivations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold Bundle
open PoincareMT.Topology.Surface

namespace PoincareMT

/-- Interior canonical vertices of a compatible coordinate triangulation have angle sum two
pi, derived from the actual geometric cover. Source: Morgan--Tian Proposition 19.35, printed
pp. 467-481, especially Claim 19.40, pp. 470-471; the explicit project tangent-fan
derivation is reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-fans.md`, Mathematical Checks. -/
theorem m64Intrinsic_regional_interior_vertex_fan
    {I : Type*} [Fintype I] (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hinj : ∀ i k, InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1))
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ w : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i w)})
    (hfront : ∀ i j, i ≠ j →
      (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
    (g : RiemannianMetric 2 AnnulusCoordinates)
    (q : Euler.CoordinateVertex F b)
    (hq : q.1 ∈ interior (⋃ i, (face i).carrier)) :
    coordinateVertexAngleContribution g F b q.1 = 2 * Real.pi := by
  classical
  let J := {i : I // q.1 ∈ (face i).carrier}
  have hcorner (i : J) : ∃! k : Fin 3, F i.1 (b i.1 k) = q.1 :=
    (coordinate_vertex_mem_face_iff face F b hsource hcarrier hboundary hinj hinter q i.1).mp i.2
  choose k hk hkunique using hcorner
  let c (i : J) := (b i.1).reindex (Equiv.swap 0 (k i))
  have hrange (i : J) : range (c i) = range (b i.1) := by
    exact (Equiv.swap 0 (k i)).symm.surjective.range_comp (b i.1)
  have hvertex (i : J) : F i.1 (c i 0) = q.1 := by
    simpa only [c, AffineBasis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_left] using hk i
  have hnear : ∀ᶠ z in 𝓝 q.1, ∀ i, z ∈ (face i).carrier → q.1 ∈ (face i).carrier := by
    rw [eventually_all]
    intro i
    by_cases hi : q.1 ∈ (face i).carrier
    · exact Eventually.of_forall (fun _ _ => hi)
    · filter_upwards [(face i).isCompact_carrier.isClosed.isOpen_compl.mem_nhds hi] with z hz
      exact fun hm => False.elim (hz hm)
  have hstar : q.1 ∈ interior (⋃ i : J, F i.1 '' convexHull ℝ (range (c i))) := by
    rw [mem_interior_iff_mem_nhds]
    filter_upwards [mem_interior_iff_mem_nhds.mp hq, hnear] with z hz hznear
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    refine mem_iUnion.mpr ⟨⟨i, hznear i hi⟩, ?_⟩
    rwa [hrange, ← hcarrier]
  have hsum := m64Intrinsic_coordinate_interior_vertex_angle_sum g
    (fun i : J => F i.1) c (fun i => hF i.1) (fun i => hFi i.1)
    (fun i => by rw [hrange]; exact hsource i.1)
    (fun i j hij => by
      rw [hrange, hrange, ← hcarrier, ← hcarrier]
      exact hfront i.1 j.1 (fun heq => hij (Subtype.ext heq)))
    q.1 hvertex hstar
  let term (i : I) := ∑ v : Fin 3,
    if F i (b i v) = q.1 then coordinateTriangleAngle g (F i) (b i) v else 0
  have hterm (i : J) : term i.1 = coordinateTriangleAngle g (F i.1) (c i) 0 := by
    dsimp only [term]
    rw [Finset.sum_eq_single (k i)]
    · rw [if_pos (hk i)]
      simp only [c, coordinateTriangleAngle_reindex, Equiv.symm_swap, Equiv.swap_apply_left]
    · intro v _ hv
      exact if_neg (fun heq => hv (hkunique i v heq))
    · simp
  have hzero (i : {i : I // ¬ q.1 ∈ (face i).carrier}) : term i.1 = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    apply if_neg
    intro heq
    apply i.2
    rw [hcarrier]
    exact ⟨b i.1 v, subset_convexHull ℝ _ (mem_range_self v), heq⟩
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : I => q.1 ∈ (face i).carrier) term
  have hs0 : (∑ i : {i : I // ¬ q.1 ∈ (face i).carrier}, term i.1) = 0 :=
    Finset.sum_eq_zero (fun i _ => hzero i)
  rw [hs0, add_zero] at hsplit
  have hsumterm : (∑ i : J, term i.1) = 2 * Real.pi := by
    simpa only [hterm] using hsum
  have hcanonical : coordinateVertexAngleContribution g F b q.1 = ∑ i, term i := by
    unfold coordinateVertexAngleContribution
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> rfl
  exact hcanonical.trans (hsplit.symm.trans hsumterm)

end PoincareMT
