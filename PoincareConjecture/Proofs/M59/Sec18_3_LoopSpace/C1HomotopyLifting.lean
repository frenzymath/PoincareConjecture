import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.CubeApproximation
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.UniformLoopHomotopy










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

universe u

namespace PoincareConjecture

variable {M : Type u} [MetricSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]




theorem m59_c1_homotopy_of_value_homotopy
    (hcompact : IsCompact (univ : Set M)) (n : Nat) (p : M)
    (F G : C((Fin n → I), C1FreeLoopSpace (M := M)))
    (H : C(I × ((Fin n → I) × LoopCircle), M))
    (h0 : ∀ v z, H (0, (v, z)) = F v z)
    (h1 : ∀ v z, H (1, (v, z)) = G v z) :
    ∃ K : F.Homotopy G, ∀ v,
      F v = constantC1Loop p → G v = constantC1Loop p →
      (∀ t z, H (t, (v, z)) = p) → ∀ t, K (t, v) = constantC1Loop p := by
  obtain ⟨epsilon, he, hnear⟩ := m59_exists_uniform_loop_homotopy_radius.{u, 0} hcompact
  let Hcube : C((Fin (n + 1) → I) × LoopCircle, M) :=
    H.comp ⟨fun q => (q.1 0, (fun i => q.1 i.succ, q.2)), by fun_prop⟩
  obtain ⟨A, hA, hAconst⟩ := m59_cube_loop_approximation (n + 1) Hcube p he
  let j : C(I × (Fin n → I), Fin (n + 1) → I) :=
    ⟨fun q => Fin.cons q.1 q.2, by
      apply continuous_pi
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact continuous_fst
      · exact (continuous_apply i).comp continuous_snd⟩
  let A0 : C((Fin n → I), C1FreeLoopSpace (M := M)) :=
    A.comp (j.comp ⟨fun v => (0, v), continuous_const.prodMk continuous_id⟩)
  let A1 : C((Fin n → I), C1FreeLoopSpace (M := M)) :=
    A.comp (j.comp ⟨fun v => (1, v), continuous_const.prodMk continuous_id⟩)
  have hA0 : ∀ v z, dist (A0 v z) (F v z) < epsilon := by
    intro v z
    have h := hA (j (0, v)) z
    change dist (A0 v z) (H (0, (v, z))) < epsilon at h
    rwa [h0] at h
  have hA1 : ∀ v z, dist (G v z) (A1 v z) < epsilon := by
    intro v z
    have h := hA (j (1, v)) z
    change dist (A1 v z) (H (1, (v, z))) < epsilon at h
    rw [h1] at h
    simpa only [dist_comm] using h
  obtain ⟨K0, hK0⟩ := hnear F A0 hA0
  obtain ⟨K1, hK1⟩ := hnear A1 G hA1
  let KA : A0.Homotopy A1 := {
    toContinuousMap := A.comp j
    map_zero_left := fun _ => rfl
    map_one_left := fun _ => rfl }
  refine ⟨K0.trans (KA.trans K1), ?_⟩
  intro v hF hG hH
  have hAC (t : I) : A (j (t, v)) = constantC1Loop p :=
    hAconst _ (fun z => hH t z)
  have hk0 (t : I) : K0 (t, v) = constantC1Loop p := hK0 t v p hF (hAC 0)
  have hk1 (t : I) : K1 (t, v) = constantC1Loop p := hK1 t v p (hAC 1) hG
  intro t
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hk0 _
  · rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact hAC _
    · exact hk1 _



theorem m59_genLoop_homotopic_of_value_homotopy
    (hcompact : IsCompact (univ : Set M)) (n : Nat) (p : M)
    (F G : GenLoop (Fin n) (C1FreeLoopSpace (M := M)) (constantC1Loop p))
    (H : C(I × ((Fin n → I) × LoopCircle), M))
    (h0 : ∀ v z, H (0, (v, z)) = F v z)
    (h1 : ∀ v z, H (1, (v, z)) = G v z)
    (hboundary : ∀ t v, v ∈ Cube.boundary (Fin n) → ∀ z, H (t, (v, z)) = p) :
    GenLoop.Homotopic F G := by
  obtain ⟨K, hK⟩ := m59_c1_homotopy_of_value_homotopy hcompact n p F.val G.val H h0 h1
  exact ⟨{ toHomotopy := K, prop' := fun t v hv =>
    (hK v (GenLoop.boundary F v hv) (GenLoop.boundary G v hv)
      (fun s z => hboundary s v hv z) t).trans (GenLoop.boundary F v hv).symm }⟩

end PoincareConjecture
