import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Strips.Labels

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)

theorem central_strip_exterior_iff {M : Type*} [TopologicalSpace M]
    {h : M → Real} {c : Real} {U : Set M}
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) M)
    (a b a₀ b₀ : Fin 2 → Real)
    (hchain : ∀ i, a i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < b i)
    (hsource : ∀ i, Icc (a i) (b i) ×ˢ ({0} : Set Real) ⊆ (F i).source)
    (hheight : ∀ i z, z ∈ (F i).source → h (F i z) = c + z.2)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i).target (F j).target))
    (hcover : (⋃ i, F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
      (h ⁻¹' {c}) \ U)
    (i : Fin 2) {s : Real} (hs : s ∈ Icc (a i) (b i)) :
    F i (s, 0) ∉ U ↔ s ∈ Icc (a₀ i) (b₀ i) := by
  have hsmall (j : Fin 2) : Icc (a₀ j) (b₀ j) ⊆ Icc (a j) (b j) :=
    fun _ ht => ⟨(hchain j).1.le.trans ht.1, ht.2.trans (hchain j).2.2.le⟩
  have hsi : (s, 0) ∈ (F i).source := hsource i ⟨hs, rfl⟩
  constructor
  · intro hout
    have hlev : h (F i (s, 0)) = c := by simpa using hheight i (s, 0) hsi
    obtain ⟨j, ⟨u, t⟩, ⟨hu, ht⟩, he⟩ := mem_iUnion.mp (hcover.superset ⟨hlev, hout⟩)
    have ht0 : t = 0 := ht
    subst t
    have hsj : (u, 0) ∈ (F j).source := hsource j ⟨hsmall j hu, rfl⟩
    have hji : j = i := by
      by_contra hn
      exact disjoint_left.mp (hdisjoint hn) ((F j).map_source hsj)
        (he ▸ (F i).map_source hsi)
    subst j
    have hus : u = s := congrArg Prod.fst ((F i).injOn hsj hsi he)
    exact hus ▸ hu
  · intro hmid
    exact (hcover.subset (mem_iUnion_of_mem i ⟨(s, 0), ⟨hmid, rfl⟩, rfl⟩)).2

theorem central_strip_test_points {M : Type*} [TopologicalSpace M]
    {h : M → Real} {c r : Real}
    (e : OpenPartialHomeomorph E2 M) (hr : 0 < r)
    (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2)
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) M)
    (a b a₀ b₀ : Fin 2 → Real)
    (hchain : ∀ i, a i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < b i)
    (hsource : ∀ i, Icc (a i) (b i) ×ˢ ({0} : Set Real) ⊆ (F i).source)
    (hheight : ∀ i z, z ∈ (F i).source → h (F i z) = c + z.2)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i).target (F j).target))
    (hcover : (⋃ i, F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
      (h ⁻¹' {c}) \ e '' openSquare r)
    (hends : ∀ i, range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
      (F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
        {F i (a₀ i, 0), F i (b₀ i, 0)}) (i : Fin 2) :
    F i (a i, 0) ∈ e '' openSquare r ∧
    F i (b i, 0) ∈ e '' openSquare r ∧
    F i ((a₀ i + b₀ i) / 2, 0) ∉ e '' closedSquare r := by
  classical
  have hc := hchain i
  have hab : a i < b i := hc.1.trans (hc.2.1.trans hc.2.2)
  have hiff {s : Real} (hs : s ∈ Icc (a i) (b i)) :=
    central_strip_exterior_iff F a b a₀ b₀ hchain hsource hheight hdisjoint hcover i hs
  refine ⟨?_, ?_, ?_⟩
  · by_contra hn
    exact (not_le.mpr hc.1) ((hiff ⟨le_rfl, hab.le⟩).mp hn).1
  · by_contra hn
    exact (not_le.mpr hc.2.2) ((hiff ⟨hab.le, le_rfl⟩).mp hn).2
  · let m := (a₀ i + b₀ i) / 2
    have ham : a₀ i < m := by dsimp [m]; linarith
    have hmb : m < b₀ i := by dsimp [m]; linarith
    have hmi : m ∈ Icc (a i) (b i) := ⟨hc.1.le.trans ham.le, hmb.le.trans hc.2.2.le⟩
    have hm0 : (m, 0) ∈ (F i).source := hsource i ⟨hmi, rfl⟩
    have hmout := (hiff hmi).mpr ⟨ham.le, hmb.le⟩
    rintro ⟨x, hx, he⟩
    have hlev : h (F i (m, 0)) = c := by simpa using hheight i (m, 0) hm0
    have hzero : x 0 ^ 2 = x 1 ^ 2 := by
      rw [← he, hform x (hrs hx)] at hlev
      linarith
    have hxo : x ∉ openSquare r := fun hxo => hmout ⟨x, hxo, he⟩
    obtain ⟨j, rfl⟩ := (square_boundary_zeroLevel hr).subset ⟨⟨hx, hxo⟩, hzero⟩
    have hend : F i (m, 0) ∈ ({F i (a₀ i, 0), F i (b₀ i, 0)} : Set M) :=
      (hends i).subset ⟨⟨j, he⟩, (m, 0), ⟨⟨ham.le, hmb.le⟩, rfl⟩, rfl⟩
    have ha0 : (a₀ i, 0) ∈ (F i).source :=
      hsource i ⟨⟨hc.1.le, hc.2.1.le.trans hc.2.2.le⟩, rfl⟩
    have hb0 : (b₀ i, 0) ∈ (F i).source :=
      hsource i ⟨⟨hc.1.le.trans hc.2.1.le, hc.2.2.le⟩, rfl⟩
    rcases mem_insert_iff.mp hend with heq | heq
    · have hh := congrArg Prod.fst ((F i).injOn hm0 ha0 heq)
      exact ham.ne' hh
    · have hh := congrArg Prod.fst ((F i).injOn hm0 hb0 (mem_singleton_iff.mp heq))
      exact hmb.ne hh

end Poincare.Manifold.Schoenflies.SaddleLevel
