import PoincareLib.Topology.Homotopy.Cube.CubeSphere
import PoincareLib.Topology.Homotopy.Cube.CubePrescribedNullhomotopy

/-!
# Sphere nullhomotopies at a prescribed basepoint

Morgan--Tian Lemma 18.27, printed p. 434, ends by contracting a sphere map
in a manifold with trivial pi2. A path to the prescribed basepoint supplies
the side trace of a cubical nullhomotopy, which descends to the sphere.
This implements the basepoint principle of Hatcher, pp. 341-342, cited as
[38] by Morgan--Tian, using M02's exact boundary extension theorem.
-/

set_option autoImplicit false

open Set Metric Topology
open scoped unitInterval

namespace PoincareMT.LoopSpace

/-- A nullhomotopy with a common side trace descends from a cube quotient.
Source: MT Lemma 18.27, p. 434; the basepoint path is the construction of
Hatcher, pp. 341-342. The target need not be Hausdorff. -/
theorem homotopic_const_of_cube_quotient
    {S X : Type*} [TopologicalSpace S] [T2Space S] [TopologicalSpace X]
    (n : ℕ) (q : C((Fin (n + 1) → I), S))
    (hq : Function.Surjective q)
    (hfiber : ∀ a b, q a = q b ↔ a = b ∨
      (a ∈ Cube.boundary (Fin (n + 1)) ∧ b ∈ Cube.boundary (Fin (n + 1))))
    (x : X) (hpi : Subsingleton (HomotopyGroup.Pi (n + 1) X x))
    (f : C(S, X)) (p : Path (f (q (fun _ => 0))) x) :
    f.Homotopic (ContinuousMap.const S x) := by
  let a : Fin (n + 1) → I := fun _ => 0
  have ha : a ∈ Cube.boundary (Fin (n + 1)) := ⟨0, Or.inl rfl⟩
  let h : C(I × Cube.boundary (Fin (n + 1)), X) :=
    ⟨fun z => p z.1, p.continuous.comp continuous_fst⟩
  have h0 (z : Cube.boundary (Fin (n + 1))) : h (0, z) = (f.comp q) z := by
    change p 0 = f (q z)
    rw [p.source]
    exact congrArg f ((hfiber a z).mpr (Or.inr ⟨ha, z.property⟩))
  obtain ⟨H, hH⟩ := Poincare.Topology.exists_cube_nullhomotopy_with_prescribed_boundary
    n x hpi (f.comp q) h h0 (fun _ => p.target)
  let Q : C(I × (Fin (n + 1) → I), I × S) :=
    ⟨fun z => (z.1, q z.2), continuous_fst.prodMk (q.continuous.comp continuous_snd)⟩
  have hQ : IsQuotientMap Q := by
    apply IsQuotientMap.of_surjective_continuous _ Q.continuous
    rintro ⟨t, s⟩
    obtain ⟨z, rfl⟩ := hq s
    exact ⟨(t, z), rfl⟩
  have hfactor : Function.FactorsThrough H.toContinuousMap Q := by
    rintro ⟨t, b⟩ ⟨s, c⟩ heq
    have ht : t = s := congrArg Prod.fst heq
    have hbc : q b = q c := congrArg Prod.snd heq
    subst s
    rcases (hfiber b c).mp hbc with rfl | ⟨hb, hc⟩
    · rfl
    · exact (hH t ⟨b, hb⟩).trans (hH t ⟨c, hc⟩).symm
  let F := hQ.lift H.toContinuousMap hfactor
  have hF (t : I) (b : Fin (n + 1) → I) : F (t, q b) = H (t, b) :=
    ContinuousMap.congr_fun (hQ.lift_comp H.toContinuousMap hfactor) (t, b)
  refine ⟨{ toContinuousMap := F, map_zero_left := ?_, map_one_left := ?_ }⟩
  · intro s
    obtain ⟨b, rfl⟩ := hq s
    exact (hF 0 b).trans (H.apply_zero b)
  · intro s
    obtain ⟨b, rfl⟩ := hq s
    exact (hF 1 b).trans (H.apply_one b)

/-- A sphere map into a path-connected space is freely nullhomotopic if
the matching homotopy group vanishes at the chosen basepoint. This is the
terminal sphere argument of MT Lemma 18.27, p. 434, in every positive dimension. -/
theorem sphere_homotopic_const_of_pi_trivial
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    (n : ℕ) (x : X) (hpi : Subsingleton (HomotopyGroup.Pi (n + 1) X x))
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    f.Homotopic (ContinuousMap.const _ x) := by
  obtain ⟨q, hq, hfiber⟩ := Poincare.Topology.exists_cube_sphere_quotient_of_card_eq
    (N := Fin (n + 1)) (ι := Fin (n + 2)) (by simp)
  exact homotopic_const_of_cube_quotient n q hq.surjective hfiber x hpi f
    (PathConnectedSpace.somePath _ _)

end PoincareMT.LoopSpace
