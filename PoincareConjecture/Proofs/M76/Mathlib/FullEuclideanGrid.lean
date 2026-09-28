import PoincareConjecture.Proofs.M76.Mathlib.DirectedSimplicialUnion
import PoincareConjecture.Proofs.M02.Topology.AmbientSimplicialGrid
import Mathlib.Topology.LocallyFinite

set_option autoImplicit false

open Set Metric Topology
open PoincareConjecture.Proofs.M02.Topology

namespace Geometry.SimplicialComplex

variable {N : ℕ}

def fullEuclideanGridFaces (h : ℝ) : Set (Finset (EuclideanSpace ℝ (Fin N))) :=
  {s | s.Nonempty ∧ ∃ (z : Fin N → ℤ) (p : Equiv.Perm (Fin N)),
    s ⊆ ambientGridSimplex h z p}

theorem exists_fullEuclideanGrid (h : ℝ) (hh : 0 < h) :
    ∃ K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)),
      K.faces = fullEuclideanGridFaces h ∧ K.space = univ ∧
      LocallyFinite (fun s : K.faces => convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin N)))) := by
  classical
  let E := EuclideanSpace ℝ (Fin N)
  choose K hfaces _ hspace using fun n : ℕ =>
    exists_ambient_grid_complex (N := N) h hh (n + 1) (Nat.zero_lt_succ n)
  have hmono : Monotone K := by
    intro n m hnm s hs
    change s ∈ (K n).faces at hs
    change s ∈ (K m).faces
    rw [hfaces n] at hs
    rw [hfaces m]
    obtain ⟨hsne, z, p, hz, hsub⟩ := hs
    refine ⟨hsne, z, p, fun i => ?_, hsub⟩
    have hi := hz i
    constructor <;> omega
  have hdir : Directed (· ≤ ·) K := fun i j =>
    ⟨max i j, hmono (le_max_left i j), hmono (le_max_right i j)⟩
  let D := directedUnion K hdir
  have hDfaces : D.faces = fullEuclideanGridFaces h := by
    ext s
    constructor
    · intro hs
      obtain ⟨n, hn⟩ := mem_iUnion.mp hs
      rw [hfaces n] at hn
      obtain ⟨hne, z, p, _, hsub⟩ := hn
      exact ⟨hne, z, p, hsub⟩
    · rintro ⟨hne, z, p, hsub⟩
      let n := Finset.univ.sup (fun i : Fin N => (z i).natAbs)
      apply mem_iUnion.mpr
      refine ⟨n, ?_⟩
      rw [hfaces n]
      refine ⟨hne, z, p, fun i => ?_, hsub⟩
      have hi : (z i).natAbs ≤ n :=
        Finset.le_sup (f := fun i : Fin N => (z i).natAbs) (Finset.mem_univ i)
      have hiabs : |z i| ≤ (n : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hi
      have hib := abs_le.mp hiabs
      constructor <;> omega
  refine ⟨D, hDfaces, ?_, ?_⟩
  · apply eq_univ_of_forall
    intro x
    change x ∈ (directedUnion K hdir).space
    rw [directedUnion_space]
    obtain ⟨n, hn⟩ := exists_nat_gt (‖x‖ / h)
    have hnorm : ‖x‖ ≤ (n + 1 : ℝ) * h := by
      have hn' := (div_lt_iff₀ hh).mp hn
      nlinarith
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    rw [hspace n]
    intro i
    have hi : |x i| ≤ (n + 1 : ℝ) * h :=
      (show |x i| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i).trans hnorm
    have hib := abs_le.mp hi
    constructor <;> push_cast <;> linarith
  · intro c
    refine ⟨ball c 1, ball_mem_nhds c (by norm_num), ?_⟩
    have hfin := ambient_grid_faces_locally_finite (N := N) h hh c 1
    have hfinfaces := hfin.biUnion fun q _ =>
      (ambientGridSimplex h q.1 q.2).powerset.finite_toSet
    apply (hfinfaces.preimage (f := (Subtype.val : D.faces → Finset E))
      Subtype.val_injective.injOn).subset
    intro s hs
    have hsface : s.val ∈ fullEuclideanGridFaces h := hDfaces ▸ s.property
    obtain ⟨_, z, p, hsub⟩ := hsface
    apply mem_iUnion₂.mpr
    refine ⟨(z, p), ?_, Finset.mem_powerset.mpr hsub⟩
    obtain ⟨x, hxs, hxc⟩ := hs
    exact ⟨x, convexHull_mono (show (s.val : Set E) ⊆ ambientGridSimplex h z p from hsub) hxs,
      ball_subset_closedBall hxc⟩

end Geometry.SimplicialComplex
