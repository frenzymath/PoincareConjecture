import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Strips.Central
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Strips.Topology

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)

theorem exists_recut_exterior_strips {M : Type*} [TopologicalSpace M] [T2Space M]
    {h : M → Real} {c r η : Real}
    (e : OpenPartialHomeomorph E2 M) (hr : 0 < r)
    (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2)
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) M)
    (a b a₀ b₀ : Fin 2 → Real) (hη : 0 < η)
    (hchain : ∀ i, a i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < b i)
    (hrect : ∀ i, Icc (a i) (b i) ×ˢ Icc (-η) η ⊆ (F i).source)
    (hheight : ∀ i z, z ∈ (F i).source → h (F i z) = c + z.2)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i).target (F j).target))
    (hcentral : (⋃ i, F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
      (h ⁻¹' {c}) \ e '' openSquare r)
    (hends : ∀ i, range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
      (F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
        {F i (a₀ i, 0), F i (b₀ i, 0)})
    (hband : h ⁻¹' Icc (c - η) (c + η) ⊆ e '' openSquare r ∪
      ⋃ i, F i '' (Icc (a i) (b i) ×ˢ Icc (-η) η)) :
    ∃ (δ : Real) (L : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2))
        (A B : Fin 2 → Real → Real),
      0 < δ ∧ δ < η ∧ δ < r ^ 2 ∧
      (∀ k, F k.1 (stripEndpoint a₀ b₀ k, 0) = e (contact r (L k))) ∧
      (∀ i, A i 0 = a₀ i ∧ B i 0 = b₀ i) ∧
      ∀ t ∈ Icc (-δ) δ,
        (∀ i, ContinuousAt (A i) t ∧ ContinuousAt (B i) t ∧
          a i < A i t ∧ A i t < B i t ∧ B i t < b i ∧
          (Icc (A i t) (B i t) ×ˢ ({t} : Set Real) ⊆ (F i).source) ∧
          F i (A i t, t) = e (movingContact r t (L (i, 0))) ∧
          F i (B i t, t) = e (movingContact r t (L (i, 1))) ∧
          (∀ s ∈ Icc (a i) (b i),
            F i (s, t) ∉ e '' openSquare r ↔ s ∈ Icc (A i t) (B i t))) ∧
        ((h ⁻¹' {c + t}) \ e '' openSquare r) =
          ⋃ i, F i '' (Icc (A i t) (B i t) ×ˢ ({t} : Set Real)) := by
  classical
  let U := e '' openSquare r
  let C := e '' closedSquare r
  let m : Fin 2 → Real := fun i => (a₀ i + b₀ i) / 2
  have hU : IsOpen U := e.isOpen_image_of_subset_source (isOpen_openSquare r)
    ((openSquare_subset_closedSquare r).trans hrs)
  have hC : IsClosed C := ((isCompact_closedSquare hr.le).image_of_continuousOn
    (e.continuousOn.mono hrs)).isClosed
  have hzero : (0 : Real) ∈ Icc (-η) η := ⟨by linarith, hη.le⟩
  have hsource (i : Fin 2) : Icc (a i) (b i) ×ˢ ({0} : Set Real) ⊆ (F i).source := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact hrect i ⟨hs, hzero⟩
  have hsmall (i : Fin 2) : Icc (a₀ i) (b₀ i) ⊆ Icc (a i) (b i) :=
    fun _ hs => ⟨(hchain i).1.le.trans hs.1, hs.2.trans (hchain i).2.2.le⟩
  have hsource₀ (i : Fin 2) : Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real) ⊆ (F i).source :=
    (prod_mono (hsmall i) Subset.rfl).trans (hsource i)
  obtain ⟨L, hL⟩ := exists_strip_contact_labels e r F a₀ b₀
    (fun i => (hchain i).2.1) hsource₀ hdisjoint hends
  let u (k : Fin 2 × Fin 2) := movingContactCoordinate e (F k.1) r (L k)
  let lo (k : Fin 2 × Fin 2) := if k.2 = 0 then a k.1 else m k.1
  let hi (k : Fin 2 × Fin 2) := if k.2 = 0 then m k.1 else b k.1
  have hmid (i : Fin 2) : a₀ i < m i ∧ m i < b₀ i := by
    dsimp [m]
    constructor <;> linarith [(hchain i).2.1]
  have hep (k : Fin 2 × Fin 2) :
      (stripEndpoint a₀ b₀ k, 0) ∈ (F k.1).source := by
    apply hsource₀ k.1
    refine ⟨?_, rfl⟩
    unfold stripEndpoint
    split_ifs <;> exact ⟨by linarith [(hchain k.1).2.1],
      by linarith [(hchain k.1).2.1]⟩
  have hbounds (k : Fin 2 × Fin 2) :
      lo k < stripEndpoint a₀ b₀ k ∧ stripEndpoint a₀ b₀ k < hi k := by
    dsimp [lo, hi, stripEndpoint]
    split_ifs
    · exact ⟨(hchain k.1).1, (hmid k.1).1⟩
    · exact ⟨(hmid k.1).2, (hchain k.1).2.2⟩
  choose d hd hdr hu0 hcoord using fun k : Fin 2 × Fin 2 =>
    exists_movingContactCoordinate_band e (F k.1) hr hrs hform (hheight k.1)
      (L k) (hep k) (hbounds k).1 (hbounds k).2 (hL k)
  have hcoords : ∀ᶠ t in 𝓝 (0 : Real), ∀ k,
      ContinuousAt (u k) t ∧ u k t ∈ Ioo (lo k) (hi k) ∧
      (u k t, t) ∈ (F k.1).source ∧ F k.1 (u k t, t) = e (movingContact r t (L k)) := by
    apply Filter.eventually_all.mpr
    intro k
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : Real) ∈ Ioo (-d k) (d k)
      from ⟨by linarith [hd k], hd k⟩)] with t ht
    exact hcoord k t (Ioo_subset_Icc_self ht)
  have hslice (i : Fin 2) (s : Real) (hs : s ∈ Icc (a i) (b i)) :
      ContinuousAt (fun t => F i (s, t)) 0 :=
    ((F i).continuousOn.continuousAt ((F i).open_source.mem_nhds
      (hsource i (show (s, 0) ∈ Icc (a i) (b i) ×ˢ ({0} : Set Real) from ⟨hs, rfl⟩)))).comp
      (f := fun t : Real => (s, t)) (continuous_const.prodMk continuous_id).continuousAt
  have htests : ∀ᶠ t in 𝓝 (0 : Real), ∀ i,
      F i (a i, t) ∈ U ∧ F i (b i, t) ∈ U ∧ F i (m i, t) ∉ C := by
    apply Filter.eventually_all.mpr
    intro i
    have hc := hchain i
    have hab := hc.1.trans (hc.2.1.trans hc.2.2)
    have hm := hmid i
    obtain ⟨ha, hb, hmC⟩ := central_strip_test_points e hr hrs hform F a b a₀ b₀
      hchain hsource hheight hdisjoint hcentral hends i
    filter_upwards [(hslice i (a i) ⟨le_rfl, hab.le⟩).eventually (hU.mem_nhds ha),
      (hslice i (b i) ⟨hab.le, le_rfl⟩).eventually (hU.mem_nhds hb),
      (hslice i (m i) ⟨hc.1.le.trans hm.1.le, hm.2.le.trans hc.2.2.le⟩).eventually
        (hC.isOpen_compl.mem_nhds hmC)] with t ha hb hmC
    exact ⟨ha, hb, hmC⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hcoords.and htests)
  let δ := min ε (min η (r ^ 2)) / 2
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hδ : 0 < δ := half_pos (lt_min hε (lt_min hη hr2))
  have hδε : δ < ε :=
    (half_lt_self (lt_min hε (lt_min hη hr2))).trans_le (min_le_left _ _)
  have hδη : δ < η :=
    (half_lt_self (lt_min hε (lt_min hη hr2))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hδr : δ < r ^ 2 :=
    (half_lt_self (lt_min hε (lt_min hη hr2))).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  let A (i : Fin 2) := u (i, 0)
  let B (i : Fin 2) := u (i, 1)
  refine ⟨δ, L, A, B, hδ, hδη, hδr, hL, ?_, ?_⟩
  · intro i
    exact ⟨hu0 (i, 0), hu0 (i, 1)⟩
  intro t ht
  have htδ : |t| ≤ δ := abs_le.mpr ht
  have htη : t ∈ Icc (-η) η := abs_le.mp (htδ.trans hδη.le)
  have htr : |t| < r ^ 2 := htδ.trans_lt hδr
  have hnear := hεsub (show t ∈ ball (0 : Real) ε by
    rw [mem_ball_zero_iff, Real.norm_eq_abs]
    exact htδ.trans_lt hδε)
  have hbds (i : Fin 2) : a i < A i t ∧ A i t < m i ∧
      m i < B i t ∧ B i t < b i :=
    ⟨(hnear.1 (i, 0)).2.1.1, (hnear.1 (i, 0)).2.1.2,
      (hnear.1 (i, 1)).2.1.1, (hnear.1 (i, 1)).2.1.2⟩
  have hboundary (i : Fin 2) (s : Real) (hs : s ∈ Icc (a i) (b i))
      (hf : F i (s, t) ∈ frontier U) : s = A i t ∨ s = B i t := by
    have hst : (s, t) ∈ (F i).source := hrect i ⟨hs, htη⟩
    obtain ⟨j, hj⟩ := frontier_image_openSquare_level_subset e hr hrs hform htr
      ⟨hf, hheight i (s, t) hst⟩
    let k := L.symm j
    have hjk : L k = j := L.apply_symm_apply j
    have hk := hnear.1 k
    have heq : F k.1 (u k t, t) = F i (s, t) := hk.2.2.2.trans (hjk ▸ hj)
    have hki : k.1 = i := by
      by_contra hn
      exact disjoint_left.mp (hdisjoint hn) ((F k.1).map_source hk.2.2.1)
        (heq ▸ (F i).map_source hst)
    have hst' : (s, t) ∈ (F k.1).source := by simpa only [hki] using hst
    have heq' : F k.1 (u k t, t) = F k.1 (s, t) := by simpa only [hki] using heq
    have hparamPair : (u k t, t) = (s, t) := (F k.1).injOn hk.2.2.1 hst' heq'
    have hparam : u k t = s := congrArg Prod.fst hparamPair
    have hkcases : k.2 = 0 ∨ k.2 = 1 := by omega
    rcases hkcases with hk0 | hk1
    · left
      have hkpair : k = (i, 0) := Prod.ext hki hk0
      simpa only [hkpair] using hparam.symm
    · right
      have hkpair : k = (i, 1) := Prod.ext hki hk1
      simpa only [hkpair] using hparam.symm
  have hiff (i : Fin 2) (s : Real) (hs : s ∈ Icc (a i) (b i)) :
      F i (s, t) ∉ U ↔ s ∈ Icc (A i t) (B i t) := by
    have hb := hbds i
    have hγ : ContinuousOn (fun s => F i (s, t)) (Icc (a i) (b i)) :=
      (F i).continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => hrect i ⟨hs, htη⟩)
    apply strip_slice_exterior_iff hU hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hγ
      (hnear.2 i).1 (hnear.2 i).2.1
      (fun hc => (hnear.2 i).2.2 (closure_image_openSquare_subset e hr hrs hc))
      (by rw [(hnear.1 (i, 0)).2.2.2]; exact image_movingContact_notMem_openSquare e hr hrs htr _)
      (by rw [(hnear.1 (i, 1)).2.2.2]; exact image_movingContact_notMem_openSquare e hr hrs htr _)
      (hboundary i) hs
  have hsub (i : Fin 2) : Icc (A i t) (B i t) ⊆ Icc (a i) (b i) :=
    fun s hs => ⟨(hbds i).1.le.trans hs.1, hs.2.trans (hbds i).2.2.2.le⟩
  refine ⟨?_, ?_⟩
  · intro i
    refine ⟨(hnear.1 (i, 0)).1, (hnear.1 (i, 1)).1, (hbds i).1,
      (hbds i).2.1.trans (hbds i).2.2.1, (hbds i).2.2.2, ?_,
      (hnear.1 (i, 0)).2.2.2, (hnear.1 (i, 1)).2.2.2, hiff i⟩
    rintro ⟨s, v⟩ ⟨hs, hv⟩
    have hvt : v = t := hv
    subst v
    exact hrect i ⟨hsub i hs, htη⟩
  · ext q
    constructor
    · rintro ⟨hqheight, hqout⟩
      have hqband : q ∈ h ⁻¹' Icc (c - η) (c + η) := by
        change h q = c + t at hqheight
        change c - η ≤ h q ∧ h q ≤ c + η
        constructor <;> linarith [htη.1, htη.2]
      obtain ⟨i, ⟨s, v⟩, ⟨hs, hv⟩, heq⟩ :=
        mem_iUnion.mp ((hband hqband).resolve_left hqout)
      have hvheight := hheight i (s, v) (hrect i ⟨hs, hv⟩)
      have hvt : v = t := by
        rw [heq] at hvheight
        change h q = c + t at hqheight
        linarith
      subst v
      exact mem_iUnion_of_mem i ⟨(s, t), ⟨(hiff i s hs).mp (heq ▸ hqout), rfl⟩, heq⟩
    · intro hq
      obtain ⟨i, ⟨s, v⟩, ⟨hs, hv⟩, rfl⟩ := mem_iUnion.mp hq
      have hvt : v = t := hv
      subst v
      exact ⟨hheight i (s, t) (hrect i ⟨hsub i hs, htη⟩),
        (hiff i s (hsub i hs)).mpr hs⟩

end Poincare.Manifold.Schoenflies.SaddleLevel
