import PoincareConjecture.Proofs.M02.CubeSphere
import PoincareConjecture.Proofs.M02.CubePrescribedNullhomotopy

set_option autoImplicit false

open Set Metric Topology
open scoped unitInterval

namespace PoincareConjecture.Proofs.M58

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
  obtain ⟨H, hH⟩ := M02.exists_cube_nullhomotopy_with_prescribed_boundary
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

theorem sphere_homotopic_const_of_pi_trivial
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    (n : ℕ) (x : X) (hpi : Subsingleton (HomotopyGroup.Pi (n + 1) X x))
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    f.Homotopic (ContinuousMap.const _ x) := by
  obtain ⟨q, hq, hfiber⟩ := M02.exists_cube_sphere_quotient_of_card_eq
    (N := Fin (n + 1)) (ι := Fin (n + 2)) (by simp)
  exact homotopic_const_of_cube_quotient n q hq.surjective hfiber x hpi f
    (PathConnectedSpace.somePath _ _)

end PoincareConjecture.Proofs.M58
