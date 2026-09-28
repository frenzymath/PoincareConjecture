import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_regular_separating_height_cuts
    (psi : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (hfinite : {q : UnitTwoSphere | mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q = 0}.Finite) :
    let f := fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ
    let critical := {q : UnitTwoSphere | mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q = 0}
    ∃ C : Set ℝ, C.Finite ∧
      (∀ t ∈ C, ∀ q : UnitTwoSphere, f q = t →
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q ≠ 0) ∧
      (∀ p ∈ critical, ∀ q ∈ critical, f p < f q →
        ∃ t ∈ C, f p < t ∧ t < f q) ∧
      (∀ t ∈ C, ∃ p ∈ critical, ∃ q ∈ critical,
        f p < t ∧ t < f q) := by
  classical
  let f := fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ
  let critical := {q : UnitTwoSphere | mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q = 0}
  let V := f '' critical
  let pairs := {p : ℝ × ℝ | p ∈ V ×ˢ V ∧ p.1 < p.2}
  have hV : V.Finite := hfinite.image f
  have hpairs : pairs.Finite := (hV.prod hV).subset (fun _ hp => hp.1)
  let : Fintype pairs := hpairs.fintype
  have hchoice (i : pairs) : ∃ t : ℝ, t ∈ Ioo i.1.1 i.1.2 ∧ t ∉ V :=
    (Ioo_infinite i.2.2).exists_notMem_finite hV
  choose g hg hnot using hchoice
  refine ⟨range g, finite_range g, ?_, ?_, ?_⟩
  · rintro t ⟨i, rfl⟩ q hq hcritical
    exact hnot i ⟨q, hcritical, hq⟩
  · intro p hp q hq hpq
    let i : pairs := ⟨(f p, f q), ⟨⟨⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩⟩, hpq⟩⟩
    exact ⟨g i, mem_range_self i, (hg i).1, (hg i).2⟩
  · rintro t ⟨i, rfl⟩
    obtain ⟨p, hp, hfp⟩ := i.2.1.1
    obtain ⟨q, hq, hfq⟩ := i.2.1.2
    refine ⟨p, hp, q, hq, ?_, ?_⟩
    · change f p < g i
      rw [hfp]
      exact (hg i).1
    · change g i < f q
      rw [hfq]
      exact (hg i).2

theorem exists_separated_regular_height_buffers
    (psi : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (hfinite : {q : UnitTwoSphere | mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q = 0}.Finite)
    (C : Set ℝ) (hC : C.Finite)
    (hregular : ∀ t ∈ C, ∀ q : UnitTwoSphere,
      ⟪(u : E3), psi (q, 0)⟫_ℝ = t →
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q ≠ 0)
    (eps : ℝ → ℝ) (heps : ∀ t ∈ C, 0 < eps t) :
    ∃ d : ℝ, 0 < d ∧
      (∀ t ∈ C, d < eps t) ∧
      (∀ t ∈ C, ∀ q : UnitTwoSphere,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q = 0 →
        4 * d < |⟪(u : E3), psi (q, 0)⟫_ℝ - t|) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t →
        Disjoint (Icc (s - d) (s + d)) (Icc (t - d) (t + d))) := by
  classical
  let f := fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ
  let critical := {q : UnitTwoSphere | mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q = 0}
  let V := f '' critical
  let unequal := {p : ℝ × ℝ | p ∈ C ×ˢ C ∧ p.1 ≠ p.2}
  let bound := fun p : ℝ × ℝ => |p.1 - p.2| / 4
  let G := eps '' C ∪ bound '' (C ×ˢ V) ∪ bound '' unequal
  have hV : V.Finite := hfinite.image f
  have hu : unequal.Finite := (hC.prod hC).subset (fun _ hp => hp.1)
  have hG : G.Finite := ((hC.image eps).union ((hC.prod hV).image bound)).union
    (hu.image bound)
  have hpositive : ∀ a ∈ G, 0 < a := by
    rintro a ((⟨t, ht, rfl⟩ | ⟨⟨t, v⟩, ⟨ht, hv⟩, rfl⟩) | ⟨p, hp, rfl⟩)
    · exact heps t ht
    · have hne : t ≠ v := by
        intro htv
        obtain ⟨q, hq, hqv⟩ := hv
        exact hregular t ht q (hqv.trans htv.symm) hq
      exact div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by norm_num)
    · exact div_pos (abs_pos.mpr (sub_ne_zero.mpr hp.2)) (by norm_num)
  obtain ⟨m, hm, hbound⟩ := hG.isCompact.exists_forall_le' continuousOn_id hpositive
  let d := m / 2
  refine ⟨d, half_pos hm, ?_, ?_, ?_⟩
  · intro t ht
    have hb : m ≤ eps t := hbound _ (Or.inl (Or.inl ⟨t, ht, rfl⟩))
    dsimp only [d]
    linarith only [hm, hb]
  · intro t ht q hq
    have hb : m ≤ |t - f q| / 4 :=
      hbound _ (Or.inl (Or.inr ⟨(t, f q), ⟨ht, ⟨q, hq, rfl⟩⟩, rfl⟩))
    rw [abs_sub_comm t (f q)] at hb
    change 4 * d < |f q - t|
    dsimp only [d]
    linarith only [hm, hb]
  · intro s hs t ht hst
    have hb : m ≤ |s - t| / 4 :=
      hbound _ (Or.inr ⟨(s, t), ⟨⟨hs, ht⟩, hst⟩, rfl⟩)
    have hgap : 2 * d < |s - t| := by
      dsimp only [d]
      linarith only [hm, hb]
    apply disjoint_left.mpr
    intro y hys hyt
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · rw [abs_of_neg (sub_neg.mpr hlt)] at hgap
      linarith only [hgap, hys.2, hyt.1]
    · rw [abs_of_pos (sub_pos.mpr hgt)] at hgap
      linarith only [hgap, hys.1, hyt.2]

end PoincareConjecture.M25.Topology3D
