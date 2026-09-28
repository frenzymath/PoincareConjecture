import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.InscribedIntervals
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.SimplePolygon
import Mathlib.Algebra.Field.Periodic










set_option autoImplicit false

open Set Metric Function

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}



def inscribedPolygon (γ : ℝ → E) (s : Fin (n + 1) → ℝ) : Polygon E n :=
  ⟨fun i => γ (s i.castSucc)⟩



theorem inscribedPolygon_edgePath (γ : ℝ → E) (s : Fin (n + 1) → ℝ)
    (hloop : γ (s (Fin.last n)) = γ (s 0)) (i : Fin n) :
    (inscribedPolygon γ s).edgePath ℝ i =
      AffineMap.lineMap (γ (s i.castSucc)) (γ (s i.succ)) := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    have hnext : γ (s (finRotate (m + 1) i).castSucc) = γ (s i.succ) := by
      by_cases hi : i = Fin.last m
      · subst i
        rw [finRotate_last]
        exact hloop.symm
      · have hidx : (finRotate (m + 1) i).castSucc = i.succ := by
          apply Fin.ext
          exact coe_finRotate_of_ne_last hi
        rw [hidx]
    change AffineMap.lineMap (γ (s i.castSucc)) (γ (s (finRotate (m + 1) i).castSucc)) = _
    rw [hnext]




theorem inscribedPolygon_simple_and_bijOn_projection (e : ℂ ≃ₗᵢ[ℝ] E)
    (γ : ℝ → E) (P : E → sphere (0 : E) 1) (hn : 3 ≤ n)
    (s : Fin (n + 1) → ℝ) (hs : StrictMono s)
    (hs0 : s 0 = 0) (hsN : s (Fin.last n) = 2 * Real.pi)
    (hloop : γ (2 * Real.pi) = γ 0) (g : Fin n → ℝ → ℝ)
    (hmono : ∀ i, StrictMonoOn (g i) (Icc (0 : ℝ) 1))
    (himage : ∀ i, g i '' Icc (0 : ℝ) 1 = Icc (s i.castSucc) (s i.succ))
    (hproj : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
      P ((inscribedPolygon γ s).edgePath ℝ i t) = sphereCircleParameter e (g i t)) :
    IsSimplePolygon (inscribedPolygon γ s) ∧
      BijOn P ((inscribedPolygon γ s).boundary ℝ) univ := by
  let p := inscribedPolygon γ s
  have h0 : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  have hmesh : ∀ k, s k ∈ Icc 0 (2 * Real.pi) := by
    intro k
    constructor
    · rw [← hs0]
      exact hs.monotone (Fin.zero_le k)
    · rw [← hsN]
      exact hs.monotone (Fin.le_last k)
  have hmem : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
      g i t ∈ Icc (s i.castSucc) (s i.succ) := by
    intro i t ht
    rw [← himage i]
    exact mem_image_of_mem (g i) ht
  have hends : ∀ i, g i 0 = s i.castSucc ∧ g i 1 = s i.succ := by
    intro i
    have hab : s i.castSucc ≤ s i.succ := hs.monotone (by
      change i.val ≤ i.val + 1
      omega)
    have hl : s i.castSucc ∈ g i '' Icc (0 : ℝ) 1 := by
      rw [himage i]
      exact ⟨le_rfl, hab⟩
    have hr : s i.succ ∈ g i '' Icc (0 : ℝ) 1 := by
      rw [himage i]
      exact ⟨hab, le_rfl⟩
    obtain ⟨t, ht, hgt⟩ := hl
    obtain ⟨u, hu, hgu⟩ := hr
    constructor
    · exact le_antisymm (hgt ▸ (hmono i).monotoneOn h0 ht ht.1) (hmem i 0 h0).1
    · exact le_antisymm (hmem i 1 h1).2 (hgu ▸ (hmono i).monotoneOn hu h1 hu.2)
  have hedge : ∀ i, p.edgePath ℝ i =
      AffineMap.lineMap (γ (s i.castSucc)) (γ (s i.succ)) := by
    apply inscribedPolygon_edgePath γ s
    simpa only [hsN, hs0] using hloop
  have hend : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      (g i t = s i.castSucc ∨ g i t = s i.succ) →
      (t = 0 ∨ t = 1) ∧ p.edgePath ℝ i t = γ (g i t) := by
    intro i t ht he
    rcases he with he | he
    · have ht0 : t = 0 := (hmono i).injOn ht h0 (he.trans (hends i).1.symm)
      subst t
      refine ⟨Or.inl rfl, ?_⟩
      rw [hedge, AffineMap.lineMap_apply_zero, (hends i).1]
    · have ht1 : t = 1 := (hmono i).injOn ht h1 (he.trans (hends i).2.symm)
      subst t
      refine ⟨Or.inr rfl, ?_⟩
      rw [hedge, AffineMap.lineMap_apply_one, (hends i).2]
  have hfull : ∀ i t, t ∈ Icc (0 : ℝ) 1 → g i t ∈ Icc 0 (2 * Real.pi) := by
    intro i t ht
    exact ⟨(hmesh i.castSucc).1.trans (hmem i t ht).1,
      (hmem i t ht).2.trans (hmesh i.succ).2⟩
  have hend0 : ∀ i t, t ∈ Icc (0 : ℝ) 1 → g i t = 0 →
      (t = 0 ∨ t = 1) ∧ p.edgePath ℝ i t = γ (g i t) := by
    intro i t ht he
    apply hend i t ht
    exact Or.inl (by linarith [(hmesh i.castSucc).1, (hmem i t ht).1])
  have hendN : ∀ i t, t ∈ Icc (0 : ℝ) 1 → g i t = 2 * Real.pi →
      (t = 0 ∨ t = 1) ∧ p.edgePath ℝ i t = γ (g i t) := by
    intro i t ht he
    apply hend i t ht
    exact Or.inr (by linarith [(hmesh i.succ).2, (hmem i t ht).2])
  have hclass : ∀ i t, t ∈ Icc (0 : ℝ) 1 → ∀ j u, u ∈ Icc (0 : ℝ) 1 →
      P (p.edgePath ℝ i t) = P (p.edgePath ℝ j u) →
      (i = j ∧ t = u) ∨ ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1) ∧
        p.edgePath ℝ i t = p.edgePath ℝ j u) := by
    intro i t ht j u hu hp
    have heq := (hproj i t ht).symm.trans (hp.trans (hproj j u hu))
    rcases eq_or_endpoints_of_sphereCircleParameter_eq e (hfull i t ht)
      (hfull j u hu) heq with he | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · by_cases hij : i = j
      · subst j
        exact Or.inl ⟨rfl, (hmono i).injOn ht hu he⟩
      · have hj : g i t ∈ Icc (s j.castSucc) (s j.succ) := he ▸ hmem j u hu
        obtain ⟨hiend, hjend⟩ := eq_endpoints_of_mem_adjacent_mesh_intervals hs hij
          (hmem i t ht) hj
        obtain ⟨htend, hxi⟩ := hend i t ht hiend
        obtain ⟨huend, hyj⟩ := hend j u hu (by simpa only [he] using hjend)
        exact Or.inr ⟨htend, huend, hxi.trans ((congrArg γ he).trans hyj.symm)⟩
    · obtain ⟨htend, hxi⟩ := hend0 i t ht ha
      obtain ⟨huend, hyj⟩ := hendN j u hu hb
      refine Or.inr ⟨htend, huend, ?_⟩
      calc
        p.edgePath ℝ i t = γ (g i t) := hxi
        _ = γ 0 := congrArg γ ha
        _ = γ (2 * Real.pi) := hloop.symm
        _ = γ (g j u) := (congrArg γ hb).symm
        _ = p.edgePath ℝ j u := hyj.symm
    · obtain ⟨htend, hxi⟩ := hendN i t ht ha
      obtain ⟨huend, hyj⟩ := hend0 j u hu hb
      refine Or.inr ⟨htend, huend, ?_⟩
      calc
        p.edgePath ℝ i t = γ (g i t) := hxi
        _ = γ (2 * Real.pi) := congrArg γ ha
        _ = γ 0 := hloop
        _ = γ (g j u) := (congrArg γ hb).symm
        _ = p.edgePath ℝ j u := hyj.symm
  have hvproj : ∀ i, P (p i) = sphereCircleParameter e (s i.castSucc) := by
    intro i
    simpa only [Polygon.edgePath, AffineMap.lineMap_apply_zero, (hends i).1]
      using hproj i 0 h0
  have hvparam : ∀ i : Fin n, s i.castSucc ∈ Ico 0 (2 * Real.pi) := by
    intro i
    refine ⟨(hmesh i.castSucc).1, ?_⟩
    rw [← hsN]
    exact hs (show i.castSucc < Fin.last n from i.isLt)
  have hvertices : Injective p := by
    intro i j hij
    have hQ := (hvproj i).symm.trans ((congrArg P hij).trans (hvproj j))
    have hparam := injOn_sphereCircleParameter_Ico e (a := 0) (b := 2 * Real.pi)
      (by simp) (hvparam i) (hvparam j) hQ
    exact Fin.ext (congrArg (fun k : Fin (n + 1) => k.val) (hs.injective hparam))
  constructor
  · refine ⟨hn, hvertices, ?_⟩
    intro i j hij x hx
    obtain ⟨t, ht, hxt⟩ := hx.1
    obtain ⟨u, hu, hxu⟩ := hx.2
    have heq := hxt.trans hxu.symm
    rcases hclass i t ht j u hu (congrArg P heq) with ⟨hij', _⟩ | ⟨hte, hue, _⟩
    · exact (hij hij').elim
    · constructor
      · rcases hte with ht0 | ht1
        · exact Or.inl (by simpa only [ht0, Polygon.edgePath,
            AffineMap.lineMap_apply_zero] using hxt.symm)
        · exact Or.inr (by simpa only [mem_singleton_iff, ht1, Polygon.edgePath,
            AffineMap.lineMap_apply_one] using hxt.symm)
      · rcases hue with hu0 | hu1
        · exact Or.inl (by simpa only [hu0, Polygon.edgePath,
            AffineMap.lineMap_apply_zero] using hxu.symm)
        · exact Or.inr (by simpa only [mem_singleton_iff, hu1, Polygon.edgePath,
            AffineMap.lineMap_apply_one] using hxu.symm)
  · refine ⟨fun _ _ => mem_univ _, ?_, ?_⟩
    · intro x hx y hy hxy
      obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff p x).mp hx
      obtain ⟨j, hj⟩ := (polygon_mem_boundary_iff p y).mp hy
      obtain ⟨t, ht, rfl⟩ := hi
      obtain ⟨u, hu, rfl⟩ := hj
      rcases hclass i t ht j u hu hxy with ⟨rfl, rfl⟩ | ⟨_, _, heq⟩
      · rfl
      · exact heq
    · intro q _
      have hq : q ∈ range (sphereCircleParameter e) :=
        surjective_sphereCircleParameter e q
      rw [← (periodic_sphereCircleParameter e).image_Icc (by positivity) 0] at hq
      obtain ⟨a, ha, haq⟩ : q ∈ sphereCircleParameter e '' Icc 0 (2 * Real.pi) :=
        by simpa only [zero_add] using hq
      obtain ⟨i, hi⟩ := exists_mem_adjacent_mesh_interval (by omega : 0 < n) s
        (by simpa only [hs0, hsN] using ha)
      have haimage : a ∈ g i '' Icc (0 : ℝ) 1 := by rwa [himage i]
      obtain ⟨t, ht, hgt⟩ := haimage
      refine ⟨p.edgePath ℝ i t, polygon_edgeSet_subset_boundary p i ⟨t, ht, rfl⟩, ?_⟩
      exact (hproj i t ht).trans ((congrArg (sphereCircleParameter e) hgt).trans haq)

end Poincare.Manifold.Schoenflies.Plane
