import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeVerticalGerms
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.ClosedGermGluing
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.PositivePartition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}

theorem gauge_recoveries_glue {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (hab : t 0 < t (Fin.last m)) (gamma : ℝ → G.Point) (hgamma : Continuous gamma)
    (T : ℝ) (hclock : ∀ s ∈ Icc (t 0) (t (Fin.last m)),
      G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (e : Fin m → AttainmentGauge G) (l r : Fin m → ℝ)
    (hbig : ∀ i, Icc (l i) (r i) ⊆ Icc (t 0) (t (Fin.last m)))
    (hcore : ∀ i, Icc (t i.castSucc) (t i.succ) ⊆ Icc (l i) (r i))
    (hnear : ∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) →
      Icc (l i) (r i) ∈ 𝓝[Icc (t 0) (t (Fin.last m))] s)
    (hsrc : ∀ i, MapsTo gamma (Icc (l i) (r i)) (e i).source)
    (alpha : ∀ i, ℝ → G.gaugeCover.spatial (e i).index)
    (halpha : ∀ i, ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (alpha i))
    (hleft : ∀ i, alpha i (t i.castSucc) = ((e i).lift (gamma (t i.castSucc))).2)
    (hright : ∀ i, alpha i (t i.succ) = ((e i).lift (gamma (t i.succ))).2)
    (hleftgerm : ∀ i, alpha i =ᶠ[𝓝 (t i.castSucc)]
      fun _ => ((e i).lift (gamma (t i.castSucc))).2)
    (hrightgerm : ∀ i, alpha i =ᶠ[𝓝 (t i.succ)]
      fun _ => ((e i).lift (gamma (t i.succ))).2) :
    ∃ g : ℝ → G.Point,
      ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) ∞ g (Icc (t 0) (t (Fin.last m))) ∧
      (∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) →
        g s = (G.gaugeCover.cylinder (e i).index).toSpacetime
          (((e i).lift (gamma s)).1, alpha i s)) ∧
      g (t 0) = gamma (t 0) ∧ g (t (Fin.last m)) = gamma (t (Fin.last m)) ∧
      ∀ s ∈ Icc (t 0) (t (Fin.last m)),
        G.spacetime.timeFunction (g s) = T - s ^ 2 := by
  classical
  let A := Icc (t 0) (t (Fin.last m))
  let beta (i : Fin m) (s : ℝ) := (G.gaugeCover.cylinder (e i).index).toSpacetime
    (((e i).lift (gamma s)).1, alpha i s)
  have hbeta (i : Fin m) :
      ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) ∞ (beta i) (Icc (l i) (r i)) :=
    (G.gaugeCover.cylinder (e i).index).smooth.comp_contMDiffOn
      ((gauge_square_clock_smooth (e i) gamma T (hsrc i)
        (fun s hs => hclock s (hbig i hs))).prodMk (halpha i).contMDiffOn)
  have hordered (i : Fin m) : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  have hleftbeta (i : Fin m) : beta i (t i.castSucc) = gamma (t i.castSucc) := by
    change (G.gaugeCover.cylinder (e i).index).toSpacetime
      (((e i).lift (gamma (t i.castSucc))).1, alpha i (t i.castSucc)) = _
    rw [hleft i]
    exact (e i).right_inv _ (hsrc i (hcore i ⟨le_rfl, hordered i⟩))
  have hrightbeta (i : Fin m) : beta i (t i.succ) = gamma (t i.succ) := by
    change (G.gaugeCover.cylinder (e i).index).toSpacetime
      (((e i).lift (gamma (t i.succ))).1, alpha i (t i.succ)) = _
    rw [hright i]
    exact (e i).right_inv _ (hsrc i (hcore i ⟨hordered i, le_rfl⟩))
  have hpair {i j : Fin m} (hij : i < j)
      (hi : t i.castSucc < t i.succ) (hj : t j.castSucc < t j.succ)
      {c : ℝ} (hci : c ∈ Icc (t i.castSucc) (t i.succ))
      (hcj : c ∈ Icc (t j.castSucc) (t j.succ)) :
      beta i =ᶠ[𝓝 c] beta j := by
    obtain ⟨hci', hcj', hc⟩ := positive_partition_intersection t ht hij hi hj hci hcj
    have hiG : beta i =ᶠ[𝓝 c] fun s => (G.gaugeCover.cylinder (e i).index).toSpacetime
        (((e i).lift (gamma s)).1, ((e i).lift (gamma c)).2) := by
      rw [hci']
      filter_upwards [hrightgerm i] with s hs
      exact congrArg (fun z => (G.gaugeCover.cylinder (e i).index).toSpacetime
        (((e i).lift (gamma s)).1, z)) hs
    have hjG : beta j =ᶠ[𝓝 c] fun s => (G.gaugeCover.cylinder (e j).index).toSpacetime
        (((e j).lift (gamma s)).1, ((e j).lift (gamma c)).2) := by
      rw [hcj']
      filter_upwards [hleftgerm j] with s hs
      exact congrArg (fun z => (G.gaugeCover.cylinder (e j).index).toSpacetime
        (((e j).lift (gamma s)).1, z)) hs
    exact (hiG.trans (gauge_vertical_germs (e i) (e j) gamma hgamma hclock hc
      (hsrc i (hcore i hci)) (hsrc j (hcore j hcj)))).trans hjG.symm
  let Active := {i : Fin m // t i.castSucc < t i.succ}
  have hcover (s : ℝ) (hs : s ∈ A) :
      ∃ i : Active, s ∈ Icc (t i.val.castSucc) (t i.val.succ) := by
    obtain ⟨i, hi, hsi⟩ := positive_partition_covers t ht hab hs
    exact ⟨⟨i, hi⟩, hsi⟩
  let : Nonempty Active := ⟨Classical.choose (hcover (t 0) ⟨le_rfl, hab.le⟩)⟩
  obtain ⟨g, hg, hpieces, _⟩ := exists_closed_germ_gluing A
    (fun i : Active => Icc (t i.val.castSucc) (t i.val.succ)) (fun _ => isClosed_Icc)
    hcover (fun i => beta i.val)
    (fun i s _ hs => (hbeta i.val s (hcore i.val hs)).mono_of_mem_nhdsWithin
      (hnear i.val s hs)) (fun i j s _ hi hj => by
      rcases lt_trichotomy i.val j.val with hij | hij | hji
      · exact (hpair hij i.property j.property hi hj).filter_mono nhdsWithin_le_nhds
      · simpa only [hij] using (Filter.EventuallyEq.rfl : beta j.val =ᶠ[𝓝[A] s] beta j.val)
      · exact (hpair hji j.property i.property hj hi).symm.filter_mono nhdsWithin_le_nhds)
  have hnode (k : Fin (m + 1)) : g (t k) = gamma (t k) := by
    have hk : t k ∈ A := ⟨ht (Fin.zero_le k), ht (Fin.le_last k)⟩
    obtain ⟨i, hi⟩ := hcover (t k) hk
    rw [hpieces i ⟨hk, hi⟩]
    rcases partition_node_endpoint t ht k i.val hi with hl | hr
    · rw [hl, hleftbeta]
    · rw [hr, hrightbeta]
  refine ⟨g, hg, ?_, hnode 0, hnode (Fin.last m), ?_⟩
  · intro i s hs
    by_cases hi : t i.castSucc < t i.succ
    · exact hpieces ⟨i, hi⟩ ⟨hbig i (hcore i hs), hs⟩
    · have heq : t i.castSucc = t i.succ := le_antisymm (hordered i) (le_of_not_gt hi)
      have hs' : s = t i.castSucc := le_antisymm (hs.2.trans heq.symm.le) hs.1
      change g s = beta i s
      rw [hs', hnode, hleftbeta]
  · intro s hs
    obtain ⟨i, hi⟩ := hcover s hs
    rw [hpieces i ⟨hs, hi⟩]
    change G.spacetime.timeFunction ((G.gaugeCover.cylinder (e i.val).index).toSpacetime
      (((e i.val).lift (gamma s)).1, alpha i.val s)) = _
    rw [(G.gaugeCover.cylinder (e i.val).index).time_eq,
      (e i.val).clock (gamma s) (hsrc i.val (hcore i.val hi))]
    exact hclock s hs

end PoincareConjecture.Proofs.M46
