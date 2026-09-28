import PoincareConjecture.Proofs.M02.Topology.SphereDiskExtension
import PoincareConjecture.Proofs.M02.Topology.HomotopyPostcomposition

set_option autoImplicit false

open Set Metric
open scoped Topology unitInterval

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable section

theorem exists_characteristic_disk_lift
    {S : Type u} [TopologicalSpace S]
    {Y : Type v} [TopologicalSpace Y]
    (n : Nat) (f : C(S, Y)) (s0 : S)
    (hsurj : Function.Surjective (homotopyGroupPostcomp n f s0))
    (p : C(closedBall (0 : Fin (n + 1) → Real) 1, Y))
    (hp : ∀ z : sphere (0 : Fin (n + 1) → Real) 1,
      p ⟨z.val, sphere_subset_closedBall z.property⟩ = f s0) :
    ∃ (g : C(closedBall (0 : Fin (n + 1) → Real) 1, S))
      (H : C(unitInterval × closedBall (0 : Fin (n + 1) → Real) 1, Y)),
      (∀ z : sphere (0 : Fin (n + 1) → Real) 1,
        g ⟨z.val, sphere_subset_closedBall z.property⟩ = s0) ∧
      (∀ z, H (0, z) = f (g z)) ∧
      (∀ z, H (1, z) = p z) ∧
      (∀ (t : unitInterval) (z : sphere (0 : Fin (n + 1) → Real) 1),
        H (t, ⟨z.val, sphere_subset_closedBall z.property⟩) = f s0) := by
  obtain ⟨e, he⟩ := exists_cube_ball_coordinates (n + 1)
  let a : GenLoop (Fin (n + 1)) Y (f s0) :=
    ⟨p.comp (e : C(_, _)), fun t ht => by
      have hz : (e t).val ∈ sphere (0 : Fin (n + 1) → Real) 1 :=
        mem_sphere_zero_iff_norm.mpr ((he t).mp ht)
      exact hp ⟨(e t).val, hz⟩⟩
  obtain ⟨b, hb⟩ := hsurj (Quotient.mk _ a)
  obtain ⟨b, rfl⟩ := Quotient.exists_rep b
  obtain ⟨J⟩ : GenLoop.Homotopic (genLoopPostcomp n f s0 b) a :=
    Quotient.exact hb
  let r : C(closedBall (0 : Fin (n + 1) → Real) 1, Fin (n + 1) → unitInterval) :=
    ⟨e.symm, e.symm.continuous⟩
  let g : C(closedBall (0 : Fin (n + 1) → Real) 1, S) := b.val.comp r
  let H : C(unitInterval × closedBall (0 : Fin (n + 1) → Real) 1, Y) :=
    J.toHomotopy.toContinuousMap.comp
      ⟨fun z => (z.1, r z.2), continuous_fst.prodMk (r.continuous.comp continuous_snd)⟩
  have hr (z : sphere (0 : Fin (n + 1) → Real) 1) :
      r ⟨z.val, sphere_subset_closedBall z.property⟩ ∈ Cube.boundary (Fin (n + 1)) := by
    apply (he _).mpr
    change ‖(e (e.symm _)).val‖ = 1
    rw [e.apply_symm_apply]
    exact mem_sphere_zero_iff_norm.mp z.property
  refine ⟨g, H, fun z => GenLoop.boundary b _ (hr z), ?_, ?_, ?_⟩
  · intro z
    exact J.apply_zero (r z)
  · intro z
    exact (J.apply_one (r z)).trans (congrArg p (e.apply_symm_apply z))
  · intro t z
    exact (J.eq_fst t (hr z)).trans
      (GenLoop.boundary (genLoopPostcomp n f s0 b) _ (hr z))

theorem homotopic_of_cube_quotient_postcomp_injective
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {Y : Type v} [TopologicalSpace Y]
    (n : Nat) (q : C((Fin (n + 1) → unitInterval), S))
    (hq : _root_.Topology.IsQuotientMap q)
    (hfiber : ∀ a b, q a = q b ↔ a = b ∨
      (a ∈ Cube.boundary (Fin (n + 1)) ∧ b ∈ Cube.boundary (Fin (n + 1))))
    (f : C(S, Y))
    (hinj : Function.Injective (homotopyGroupPostcomp n f (q (fun _ => 0))))
    (g : C(S, S)) (hg : g (q (fun _ => 0)) = q (fun _ => 0))
    (H : (f.comp g).Homotopy f)
    (hfix : ∀ t : unitInterval, H (t, q (fun _ => 0)) = f (q (fun _ => 0))) :
    g.Homotopic (ContinuousMap.id S) := by
  let zero : Fin (n + 1) → unitInterval := fun _ => 0
  have hz : zero ∈ Cube.boundary (Fin (n + 1)) := ⟨0, Or.inl rfl⟩
  have hqboundary (a : Fin (n + 1) → unitInterval)
      (ha : a ∈ Cube.boundary (Fin (n + 1))) : q a = q zero :=
    (hfiber a zero).mpr (Or.inr ⟨ha, hz⟩)
  let a : GenLoop (Fin (n + 1)) S (q zero) := ⟨q, hqboundary⟩
  let b : GenLoop (Fin (n + 1)) S (q zero) :=
    ⟨g.comp q, fun t ht => (congrArg g (hqboundary t ht)).trans hg⟩
  have hpost : GenLoop.Homotopic (genLoopPostcomp n f (q zero) b)
      (genLoopPostcomp n f (q zero) a) := by
    refine ⟨{ toHomotopy := H.compContinuousMap q, prop' := ?_ }⟩
    intro t z hz'
    change H (t, q z) = f (g (q z))
    rw [hqboundary z hz', hg]
    exact hfix t
  have heq : (Quotient.mk _ b : HomotopyGroup.Pi (n + 1) S (q zero)) =
      Quotient.mk _ a := hinj (Quotient.sound hpost)
  obtain ⟨J⟩ : GenLoop.Homotopic b a := Quotient.exact heq
  let Q : C(unitInterval × (Fin (n + 1) → unitInterval), unitInterval × S) :=
    ⟨fun z => (z.1, q z.2), continuous_fst.prodMk (q.continuous.comp continuous_snd)⟩
  have hQ : _root_.Topology.IsQuotientMap Q := by
    apply _root_.Topology.IsQuotientMap.of_surjective_continuous _ Q.continuous
    rintro ⟨t, s⟩
    obtain ⟨z, rfl⟩ := hq.surjective s
    exact ⟨(t, z), rfl⟩
  have hfactor : Function.FactorsThrough J.toHomotopy.toContinuousMap Q := by
    rintro ⟨t, a'⟩ ⟨t', b'⟩ h
    have ht : t = t' := congrArg Prod.fst h
    subst t'
    rcases (hfiber a' b').mp (congrArg Prod.snd h) with rfl | ⟨ha, hb⟩
    · rfl
    · exact (J.eq_fst t ha).trans ((GenLoop.boundary b a' ha).trans
        ((GenLoop.boundary b b' hb).symm.trans (J.eq_fst t hb).symm))
  let L := hQ.lift J.toHomotopy.toContinuousMap hfactor
  have hL (t : unitInterval) (z : Fin (n + 1) → unitInterval) : L (t, q z) = J (t, z) :=
    DFunLike.congr_fun (hQ.lift_comp J.toHomotopy.toContinuousMap hfactor) (t, z)
  refine ⟨{ toContinuousMap := L, map_zero_left := ?_, map_one_left := ?_ }⟩
  · intro s
    obtain ⟨z, rfl⟩ := hq.surjective s
    exact (hL 0 z).trans (J.apply_zero z)
  · intro s
    obtain ⟨z, rfl⟩ := hq.surjective s
    exact (hL 1 z).trans (J.apply_one z)

end

end PoincareConjecture.Proofs.M02.Topology
