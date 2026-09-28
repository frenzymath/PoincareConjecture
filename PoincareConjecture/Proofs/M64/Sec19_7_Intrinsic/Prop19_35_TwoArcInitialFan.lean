import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalCornerFans

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Bundle Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_two_arc_initial_normal_fan
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
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0) (hareg : deriv alpha 0 ≠ 0)
    (horth : g.inner (alpha 0) (deriv alpha 0) (deriv beta 0) = 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U)
    (hnorm : ‖alpha 0‖ = 1)
    (hinward : 0 < inner ℝ (alpha 0) (deriv beta 0))
    (hsub : closure U ⊆ standardAnnulusDomain)
    (hcover : (⋃ i, (face i).carrier) = closure U)
    (q : Euler.CoordinateVertex F b) (hq : q.1 = alpha 0) :
    coordinateVertexAngleContribution g F b q.1 = Real.pi / 2 := by
  let W : Set AnnulusCoordinates :=
    alpha '' Icc (A / 2) A ∪ beta '' Icc (B / 2) B
  have hAhalf : 0 < A / 2 := by linarith
  have hBhalf : 0 < B / 2 := by linarith
  have hW : IsCompact W :=
    (isCompact_Icc.image ha.continuous).union (isCompact_Icc.image hb.continuous)
  have hpW : alpha 0 ∉ W := by
    intro hp
    rcases hp with hp | hp
    · obtain ⟨t, ht, ht0⟩ := hp
      have h0 : (0 : ℝ) ∈ Icc 0 A := ⟨le_rfl, hA.le⟩
      have ht' : t ∈ Icc 0 A := ⟨(by linarith [ht.1]), ht.2⟩
      have : t = 0 := hai ht' h0 ht0
      linarith [ht.1]
    · obtain ⟨t, ht, ht0⟩ := hp
      have h0 : (0 : ℝ) ∈ Icc 0 B := ⟨le_rfl, hB.le⟩
      have ht' : t ∈ Icc 0 B := ⟨(by linarith [ht.1]), ht.2⟩
      have : t = 0 := hbi ht' h0 (ht0.trans hbase.symm)
      linarith [ht.1]
  have hsplitA : Icc (0 : ℝ) A = Icc 0 (A / 2) ∪ Icc (A / 2) A := by
    ext t
    constructor
    · intro ht
      rcases le_total t (A / 2) with htHalf | hHalfT
      · exact Or.inl ⟨ht.1, htHalf⟩
      · exact Or.inr ⟨hHalfT, ht.2⟩
    · rintro (ht | ht)
      · exact ⟨ht.1, ht.2.trans (by linarith)⟩
      · exact ⟨(by linarith [ht.1]), ht.2⟩
  have hsplitB : Icc (0 : ℝ) B = Icc 0 (B / 2) ∪ Icc (B / 2) B := by
    ext t
    constructor
    · intro ht
      rcases le_total t (B / 2) with htHalf | hHalfT
      · exact Or.inl ⟨ht.1, htHalf⟩
      · exact Or.inr ⟨hHalfT, ht.2⟩
    · rintro (ht | ht)
      · exact ⟨ht.1, ht.2.trans (by linarith)⟩
      · exact ⟨(by linarith [ht.1]), ht.2⟩
  have hfU' : frontier U =
      alpha '' Icc 0 (A / 2) ∪ beta '' Icc 0 (B / 2) ∪ W := by
    rw [hfU, hsplitA, hsplitB, image_union, image_union]
    change (_ ∪ _) ∪ (_ ∪ _) = _ ∪ _ ∪ (_ ∪ _)
    ac_rfl
  apply m64Intrinsic_annular_normal_corner_fan face F b hF hFi hsource hcarrier
    hboundary hinj hinter hfront g ha hb hAhalf hBhalf
    (hai.mono (Icc_subset_Icc le_rfl (by linarith)))
    (hbi.mono (Icc_subset_Icc le_rfl (by linarith))) hbase hareg horth
    hW hpW hU hV hdisj hfU' hfV hnorm hinward hsub hcover q hq

end PoincareConjecture
