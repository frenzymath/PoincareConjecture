import PoincareConjecture.Proofs.M25.Topology3D.Plane.InscribedIntervals
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.PolygonalArc

set_option autoImplicit false

open Set Function

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isSimplePolygonalArc_and_bijOn_of_ordered_projection
    {n : ℕ} (p : Polygon E (n + 2)) (P : E → ℝ) (m : Fin (n + 2) → ℝ)
    (hm : StrictMono m)
    (hv : ∀ k, P (p k) = m k)
    (hmono : ∀ i : Fin (n + 1),
      StrictMonoOn (fun t : ℝ => P (p.edgePath ℝ i.castSucc t))
        (Icc (0 : ℝ) 1))
    (himage : ∀ i : Fin (n + 1),
      (fun t : ℝ => P (p.edgePath ℝ i.castSucc t)) '' Icc (0 : ℝ) 1 =
        Icc (m i.castSucc) (m i.succ)) :
    IsSimplePolygonalArc p ∧
      BijOn P (polygonArcBoundary p) (Icc (m 0) (m (Fin.last (n + 1)))) := by
  have h0 : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  have hmem : ∀ i : Fin (n + 1), ∀ t ∈ Icc (0 : ℝ) 1,
      P (p.edgePath ℝ i.castSucc t) ∈ Icc (m i.castSucc) (m i.succ) := by
    intro i t ht
    rw [← himage i]
    exact mem_image_of_mem _ ht
  have hends : ∀ i : Fin (n + 1),
      P (p.edgePath ℝ i.castSucc 0) = m i.castSucc ∧
      P (p.edgePath ℝ i.castSucc 1) = m i.succ := by
    intro i
    have hab : m i.castSucc ≤ m i.succ := hm.monotone (by
      change i.val ≤ i.val + 1
      omega)
    have hl : m i.castSucc ∈
        (fun t : ℝ => P (p.edgePath ℝ i.castSucc t)) '' Icc (0 : ℝ) 1 := by
      rw [himage i]
      exact ⟨le_rfl, hab⟩
    have hr : m i.succ ∈
        (fun t : ℝ => P (p.edgePath ℝ i.castSucc t)) '' Icc (0 : ℝ) 1 := by
      rw [himage i]
      exact ⟨hab, le_rfl⟩
    obtain ⟨t, ht, hlt⟩ := hl
    obtain ⟨u, hu, hut⟩ := hr
    constructor
    · exact le_antisymm (hlt ▸ (hmono i).monotoneOn h0 ht ht.1)
        (hmem i 0 h0).1
    · exact le_antisymm (hmem i 1 h1).2
        (hut ▸ (hmono i).monotoneOn hu h1 hu.2)
  have hend : ∀ i : Fin (n + 1), ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      (P (p.edgePath ℝ i.castSucc t) = m i.castSucc ∨
        P (p.edgePath ℝ i.castSucc t) = m i.succ) →
      (t = 0 ∧ p.edgePath ℝ i.castSucc t = p i.castSucc) ∨
        (t = 1 ∧ p.edgePath ℝ i.castSucc t = p i.succ) := by
    intro i t ht he
    rcases he with he | he
    · have ht0 : t = 0 := (hmono i).injOn ht h0
        (he.trans (hends i).1.symm)
      left
      subst t
      exact ⟨rfl, by simp [Polygon.edgePath]⟩
    · have ht1 : t = 1 := (hmono i).injOn ht h1
        (he.trans (hends i).2.symm)
      right
      subst t
      exact ⟨rfl, by simp [Polygon.edgePath]⟩
  have hvertices : Function.Injective p := by
    intro i j hij
    apply hm.injective
    exact (hv i).symm.trans ((congrArg P hij).trans (hv j))
  have hclass : ∀ i : Fin (n + 1), ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      ∀ j : Fin (n + 1), ∀ u : ℝ, u ∈ Icc (0 : ℝ) 1 →
      P (p.edgePath ℝ i.castSucc t) = P (p.edgePath ℝ j.castSucc u) →
      (i = j ∧ t = u) ∨
        ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1) ∧
          p.edgePath ℝ i.castSucc t = p.edgePath ℝ j.castSucc u) := by
    intro i t ht j u hu hp
    by_cases hij : i = j
    · subst j
      exact Or.inl ⟨rfl, (hmono i).injOn ht hu hp⟩
    · have hi := hmem i t ht
      have hj := hmem j u hu
      obtain ⟨hiend, hjend⟩ := eq_endpoints_of_mem_adjacent_mesh_intervals hm hij hi
        (hp ▸ hj)
      obtain ⟨ht0, hxt⟩ | ⟨ht1, hxt⟩ := hend i t ht hiend
      · rcases hend j u hu (by simpa only [hp] using hjend) with ⟨hu0, hyu⟩ | ⟨hu1, hyu⟩
        · have hidx : i.castSucc = j.castSucc := by
            apply hm.injective
            calc
              m i.castSucc = P (p i.castSucc) := (hv i.castSucc).symm
              _ = P (p.edgePath ℝ i.castSucc t) := congrArg P hxt.symm
              _ = P (p.edgePath ℝ j.castSucc u) := hp
              _ = P (p j.castSucc) := congrArg P hyu
              _ = m j.castSucc := hv j.castSucc
          exact Or.inr ⟨Or.inl ht0, Or.inl hu0, by
            calc
              p.edgePath ℝ i.castSucc t = p i.castSucc := hxt
              _ = p j.castSucc := congrArg p hidx
              _ = p.edgePath ℝ j.castSucc u := hyu.symm⟩
        · have hidx : i.castSucc = j.succ := by
            apply hm.injective
            calc
              m i.castSucc = P (p i.castSucc) := (hv i.castSucc).symm
              _ = P (p.edgePath ℝ i.castSucc t) := congrArg P hxt.symm
              _ = P (p.edgePath ℝ j.castSucc u) := hp
              _ = P (p j.succ) := congrArg P hyu
              _ = m j.succ := hv j.succ
          exact Or.inr ⟨Or.inl ht0, Or.inr hu1, by
            calc
              p.edgePath ℝ i.castSucc t = p i.castSucc := hxt
              _ = p j.succ := congrArg p hidx
              _ = p.edgePath ℝ j.castSucc u := hyu.symm⟩
      · rcases hend j u hu (by simpa only [hp] using hjend) with ⟨hu0, hyu⟩ | ⟨hu1, hyu⟩
        · have hidx : i.succ = j.castSucc := by
            apply hm.injective
            calc
              m i.succ = P (p i.succ) := (hv i.succ).symm
              _ = P (p.edgePath ℝ i.castSucc t) := congrArg P hxt.symm
              _ = P (p.edgePath ℝ j.castSucc u) := hp
              _ = P (p j.castSucc) := congrArg P hyu
              _ = m j.castSucc := hv j.castSucc
          exact Or.inr ⟨Or.inr ht1, Or.inl hu0, by
            calc
              p.edgePath ℝ i.castSucc t = p i.succ := hxt
              _ = p j.castSucc := congrArg p hidx
              _ = p.edgePath ℝ j.castSucc u := hyu.symm⟩
        · have hidx : i.succ = j.succ := by
            apply hm.injective
            calc
              m i.succ = P (p i.succ) := (hv i.succ).symm
              _ = P (p.edgePath ℝ i.castSucc t) := congrArg P hxt.symm
              _ = P (p.edgePath ℝ j.castSucc u) := hp
              _ = P (p j.succ) := congrArg P hyu
              _ = m j.succ := hv j.succ
          exact Or.inr ⟨Or.inr ht1, Or.inr hu1, by
            calc
              p.edgePath ℝ i.castSucc t = p i.succ := hxt
              _ = p j.succ := congrArg p hidx
              _ = p.edgePath ℝ j.castSucc u := hyu.symm⟩
  have hedge_inter : ∀ i j : Fin (n + 1), i ≠ j →
      p.edgeSet ℝ i.castSucc ∩ p.edgeSet ℝ j.castSucc ⊆
        {p i.castSucc, p i.succ} ∩ {p j.castSucc, p j.succ} := by
    intro i j hij x hx
    obtain ⟨t, ht, hxt⟩ := hx.1
    obtain ⟨u, hu, hxu⟩ := hx.2
    have hp : P (p.edgePath ℝ i.castSucc t) =
        P (p.edgePath ℝ j.castSucc u) := congrArg P (hxt.trans hxu.symm)
    rcases hclass i t ht j u hu hp with ⟨hij', _⟩ | ⟨hte, hue, heq⟩
    · exact (hij hij').elim
    · constructor
      · rcases hte with ht0 | ht1
        · change x = p i.castSucc ∨ x = p i.succ
          exact Or.inl (by
            calc
              x = p.edgePath ℝ i.castSucc t := hxt.symm
              _ = p.edgePath ℝ i.castSucc 0 := by rw [ht0]
              _ = p i.castSucc := by simp [Polygon.edgePath])
        · change x = p i.castSucc ∨ x = p i.succ
          exact Or.inr (by
            calc
              x = p.edgePath ℝ i.castSucc t := hxt.symm
              _ = p.edgePath ℝ i.castSucc 1 := by rw [ht1]
              _ = p i.succ := by simp [Polygon.edgePath])
      · rcases hue with hu0 | hu1
        · change x = p j.castSucc ∨ x = p j.succ
          exact Or.inl (by
            calc
              x = p.edgePath ℝ j.castSucc u := hxu.symm
              _ = p.edgePath ℝ j.castSucc 0 := by rw [hu0]
              _ = p j.castSucc := by simp [Polygon.edgePath])
        · change x = p j.castSucc ∨ x = p j.succ
          exact Or.inr (by
            calc
              x = p.edgePath ℝ j.castSucc u := hxu.symm
              _ = p.edgePath ℝ j.castSucc 1 := by rw [hu1]
              _ = p j.succ := by simp [Polygon.edgePath])
  have hmaps : MapsTo P (polygonArcBoundary p)
      (Icc (m 0) (m (Fin.last (n + 1)))) := by
    intro x hx
    change x ∈ ⋃ i : Fin (n + 1), p.edgeSet ℝ i.castSucc at hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨t, ht, rfl⟩ := hi
    have hleft : m 0 ≤ m i.castSucc := hm.monotone (Fin.zero_le _)
    have hright : m i.succ ≤ m (Fin.last (n + 1)) := hm.monotone (Fin.le_last _)
    exact ⟨hleft.trans (hmem i t ht).1, (hmem i t ht).2.trans hright⟩
  have hinj : InjOn P (polygonArcBoundary p) := by
    intro x hx y hy hxy
    change x ∈ ⋃ i : Fin (n + 1), p.edgeSet ℝ i.castSucc at hx
    change y ∈ ⋃ i : Fin (n + 1), p.edgeSet ℝ i.castSucc at hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    obtain ⟨t, ht, rfl⟩ := hi
    obtain ⟨u, hu, rfl⟩ := hj
    rcases hclass i t ht j u hu hxy with ⟨hij, htu⟩ | ⟨_, _, heq⟩
    · subst j
      simp [htu]
    · exact heq
  have hsurj : SurjOn P (polygonArcBoundary p)
      (Icc (m 0) (m (Fin.last (n + 1)))) := by
    intro x hx
    obtain ⟨i, hi⟩ := exists_mem_adjacent_mesh_interval (n := n + 1)
      (by omega : 0 < n + 1) m hx
    have hxi : x ∈
        (fun t : ℝ => P (p.edgePath ℝ i.castSucc t)) '' Icc (0 : ℝ) 1 := by
      rw [himage i]
      exact hi
    obtain ⟨t, ht, htx⟩ := hxi
    refine ⟨p.edgePath ℝ i.castSucc t,
      polygon_arcEdge_subset_boundary p i ⟨t, ht, rfl⟩, ?_⟩
    exact htx
  refine ⟨⟨hvertices, hedge_inter⟩, hmaps, hinj, hsurj⟩

end PoincareConjecture.M25.Topology3D
