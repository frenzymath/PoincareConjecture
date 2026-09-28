import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerMetricFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.VertexIncidence

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_regional_corner_vertex_fan
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
    {phi : AnnulusCoordinates → ℝ × ℝ}
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hphi : HasFDerivAt phi L.toContinuousLinearMap q.1) (hzero : phi q.1 = 0)
    (positive : Bool)
    (hregion : ∀ᶠ z in 𝓝 q.1, z ∈ ⋃ i, (face i).carrier ↔
      if positive then 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2
      else (phi z).1 ≤ 0 ∨ (phi z).2 ≤ 0) :
    coordinateVertexAngleContribution g F b q.1 =
      if positive then g.cornerAngle q.1 (L.symm (1, 0)) (L.symm (0, 1))
      else 2 * Real.pi - g.cornerAngle q.1 (L.symm (1, 0)) (L.symm (0, 1)) := by
  classical
  let J := {i : I // q.1 ∈ (face i).carrier}
  have hcorner (i : J) : ∃! k : Fin 3, F i.1 (b i.1 k) = q.1 :=
    (coordinate_vertex_mem_face_iff face F b hsource hcarrier hboundary hinj hinter q i.1).mp i.2
  choose k hk hkunique using hcorner
  let c (i : J) := (b i.1).reindex (Equiv.swap 0 (k i))
  have hrange (i : J) : range (c i) = range (b i.1) :=
    (Equiv.swap 0 (k i)).symm.surjective.range_comp (b i.1)
  have hvertex (i : J) : F i.1 (c i 0) = q.1 := by
    simpa only [c, AffineBasis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_left] using hk i
  have hnear : ∀ᶠ z in 𝓝 q.1, ∀ i, z ∈ (face i).carrier → q.1 ∈ (face i).carrier := by
    rw [eventually_all]
    intro i
    by_cases hi : q.1 ∈ (face i).carrier
    · exact Eventually.of_forall (fun _ _ => hi)
    · filter_upwards [(face i).isCompact_carrier.isClosed.isOpen_compl.mem_nhds hi] with z hz
      exact fun hm => False.elim (hz hm)
  have hstar : ∀ᶠ z in 𝓝 q.1,
      z ∈ ⋃ i : J, F i.1 '' convexHull ℝ (range (c i)) ↔
        if positive then 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2
        else (phi z).1 ≤ 0 ∨ (phi z).2 ≤ 0 := by
    filter_upwards [hregion, hnear] with z hz hznear
    constructor
    · intro h
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      apply hz.mp
      refine mem_iUnion.mpr ⟨i.1, ?_⟩
      rwa [hrange, ← hcarrier] at hi
    · intro h
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hz.mpr h)
      refine mem_iUnion.mpr ⟨⟨i, hznear i hi⟩, ?_⟩
      rwa [hrange, ← hcarrier]
  have hsum := m64Intrinsic_coordinate_corner_vertex_angle_sum g
    (fun i : J => F i.1) c (fun i => hF i.1) (fun i => hFi i.1)
    (fun i => by rw [hrange]; exact hsource i.1)
    (fun i j hij => by
      rw [hrange, hrange, ← hcarrier, ← hcarrier]
      exact hfront i.1 j.1 (fun heq => hij (Subtype.ext heq)))
    q.1 hvertex L hphi hzero positive hstar
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
  have hzeroTerm (i : {i : I // ¬ q.1 ∈ (face i).carrier}) : term i.1 = 0 := by
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
    Finset.sum_eq_zero (fun i _ => hzeroTerm i)
  rw [hs0, add_zero] at hsplit
  have hcanonical : coordinateVertexAngleContribution g F b q.1 = ∑ i, term i := by
    unfold coordinateVertexAngleContribution
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> rfl
  exact hcanonical.trans (hsplit.symm.trans (by simpa only [hterm] using hsum))

end PoincareConjecture
