import PoincareConjecture.Proofs.M59.Mathlib.CoveringHomotopyGroups
import PoincareConjecture.Proofs.M59.Mathlib.CubicalMapNaturality

set_option autoImplicit false

open scoped Topology unitInterval
open Topology

namespace IsCoveringMap

open PoincareConjecture.Proofs.M02 PoincareConjecture.Proofs.M59

variable {E X S N : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace S] [T2Space S] [LocallyCompactSpace S]
  [Finite N] [Nontrivial N] {p : E → X}

omit [Finite N] in

theorem exists_circle_family_lift (hp : IsCoveringMap p)
    (q : CubeBoundaryQuotient (Fin 1) S) (c : E)
    (a : GenLoop N C(S, X) (ContinuousMap.const S (p c))) :
    ∃ A : GenLoop N C(S, E) (ContinuousMap.const S c),
      mapGenLoop (postcomposeMap S ⟨p, hp.continuous⟩) rfl A = a := by
  classical
  let : ContractibleSpace (N → I) := Cube.contractibleSpace N
  let : ContractibleSpace (Fin 1 → I) := Cube.contractibleSpace (Fin 1)
  let : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let z : N → I := fun _ => 0
  let w : Fin 1 → I := fun _ => 0
  have hz : z ∈ Cube.boundary N := ⟨Classical.choice inferInstance, Or.inl rfl⟩
  let f : C((N → I) × (Fin 1 → I), X) :=
    ⟨fun v => a v.1 (q.map v.2), by fun_prop⟩
  have hfzero : p c = f (z, w) :=
    (congrArg (fun g : C(S, X) => g (q.map w)) (GenLoop.boundary a z hz)).symm
  obtain ⟨F, hF, _⟩ := hp.existsUnique_continuousMap_lifts f (z, w) c hfzero
  have hproj (v : N → I) (s : Fin 1 → I) : p (F (v, s)) = a v (q.map s) :=
    congrFun hF.2 (v, s)
  let : PreconnectedSpace (Cube.boundary N) :=
    isPreconnected_iff_preconnectedSpace.mp
      (Cube.isPathConnected_boundary (N := N)).isConnected.isPreconnected
  have hboundary (v : N → I) (hv : v ∈ Cube.boundary N) (s : Fin 1 → I) :
      F (v, s) = c := by
    have he (b : Cube.boundary N × (Fin 1 → I)) : p (F (b.1, b.2)) = p c :=
      (hproj b.1 b.2).trans
        (congrArg (fun g : C(S, X) => g (q.map b.2))
          (GenLoop.boundary a b.1 b.1.2))
    exact (hp.const_of_comp
      (F.continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
      (fun b b' => (he b).trans (he b').symm)
      (⟨v, hv⟩, s) (⟨z, hz⟩, w)).trans hF.1
  have hfiber (v : N → I) (s t : Fin 1 → I) (hst : q.map s = q.map t) :
      F (v, s) = F (v, t) := by
    apply congrFun (hp.eq_of_comp_eq
      (F.continuous.comp (continuous_id.prodMk continuous_const))
      (F.continuous.comp (continuous_id.prodMk continuous_const)) ?_ z
      ((hboundary z hz s).trans (hboundary z hz t).symm)) v
    funext u
    exact (hproj u s).trans ((congrArg (a u) hst).trans (hproj u t).symm)
  let Q : C((N → I) × (Fin 1 → I), (N → I) × S) :=
    ⟨fun v => (v.1, q.map v.2), continuous_fst.prodMk (q.map.continuous.comp continuous_snd)⟩
  have hQ : IsQuotientMap Q := by
    apply IsQuotientMap.of_surjective_continuous _ Q.continuous
    rintro ⟨v, s⟩
    obtain ⟨t, rfl⟩ := q.surjective s
    exact ⟨(v, t), rfl⟩
  have hfactor : Function.FactorsThrough F Q := by
    rintro ⟨v, s⟩ ⟨u, t⟩ h
    have hvu : v = u := congrArg Prod.fst h
    subst u
    exact hfiber v s t (congrArg Prod.snd h)
  let G := hQ.lift F hfactor
  have hG (v : N → I) (s : Fin 1 → I) : G (v, q.map s) = F (v, s) :=
    ContinuousMap.congr_fun (hQ.lift_comp F hfactor) (v, s)
  let A : GenLoop N C(S, E) (ContinuousMap.const S c) :=
    ⟨⟨fun v => ⟨fun s => G (v, s), G.continuous.comp (continuous_const.prodMk continuous_id)⟩,
      ContinuousMap.continuous_of_continuous_uncurry _ G.continuous⟩,
      fun v hv => by
        ext s
        obtain ⟨t, rfl⟩ := q.surjective s
        exact (hG v t).trans (hboundary v hv t)⟩
  refine ⟨A, ?_⟩
  ext v s
  obtain ⟨t, rfl⟩ := q.surjective s
  exact (congrArg p (hG v t)).trans (hproj v t)

omit [Nontrivial N] [T2Space S] [Finite N] in

theorem exists_circle_homotopyAlong_lift [Nonempty N] (hp : IsCoveringMap p)
    (q : CubeBoundaryQuotient (Fin 1) S) (c : E)
    {a b : GenLoop N C(S, X) (ContinuousMap.const S (p c))}
    {l : Path (ContinuousMap.const S (p c)) (ContinuousMap.const S (p c))}
    (H : GenLoop.HomotopyAlong l a b)
    (A : GenLoop N C(S, E) (ContinuousMap.const S c))
    (hA : mapGenLoop (postcomposeMap S ⟨p, hp.continuous⟩) rfl A = a) :
    ∃ (c' : E) (hc' : p c' = p c)
      (B : GenLoop N C(S, E) (ContinuousMap.const S c'))
      (L : Path (ContinuousMap.const S c) (ContinuousMap.const S c')),
      Nonempty (GenLoop.HomotopyAlong L A B) ∧
        mapGenLoop (postcomposeMap S ⟨p, hp.continuous⟩)
          (postcomposeMap_const S ⟨p, hp.continuous⟩ hc') B = b ∧
        ∀ t s, p (L t s) = l t s := by
  classical
  let : ConnectedSpace S := q.surjective.connectedSpace q.map.continuous
  let z : N → I := fun _ => 0
  have hz : z ∈ Cube.boundary N := ⟨Classical.choice inferInstance, Or.inl rfl⟩
  let F : C((N → I) × S, E) := ⟨fun v => A v.1 v.2, by fun_prop⟩
  let h : C(I × ((N → I) × S), X) :=
    ⟨fun v => H.toHomotopy (v.1, v.2.1) v.2.2, by fun_prop⟩
  have hzero (v : (N → I) × S) : h (0, v) = p (F v) :=
    (congrArg (fun g : C(S, X) => g v.2) (H.toHomotopy.apply_zero v.1)).trans
      (congrArg (fun g : GenLoop N C(S, X) (ContinuousMap.const S (p c)) =>
        g v.1 v.2) hA).symm
  let K := hp.liftHomotopy h F hzero
  have hproj (t : I) (v : N → I) (s : S) :
      p (K (t, (v, s))) = H.toHomotopy (t, v) s :=
    congrFun (hp.liftHomotopy_lifts h F hzero) (t, (v, s))
  have hstart (v : N → I) (s : S) : K (0, (v, s)) = A v s :=
    hp.liftHomotopy_zero h F hzero (v, s)
  have hside (t : I) (v : N → I) (hv : v ∈ Cube.boundary N) (s : S) :
      K (t, (v, s)) = K (t, (z, s)) := by
    apply congrFun (hp.eq_of_comp_eq
      (K.continuous.comp (continuous_id.prodMk continuous_const))
      (K.continuous.comp (continuous_id.prodMk continuous_const)) ?_ 0 ?_) t
    · funext u
      exact (hproj u v s).trans
        ((congrArg (fun g : C(S, X) => g s) (H.boundary_path u ⟨v, hv⟩)).trans
          ((congrArg (fun g : C(S, X) => g s) (H.boundary_path u ⟨z, hz⟩)).symm.trans
            (hproj u z s).symm))
    · exact (hstart v s).trans
        ((congrArg (fun g : C(S, E) => g s) (GenLoop.boundary A v hv)).trans
          ((congrArg (fun g : C(S, E) => g s) (GenLoop.boundary A z hz)).symm.trans
            (hstart z s).symm))
  let c' := K (1, (z, q.pole))
  have hendproj (s : S) : p (K (1, (z, s))) = p c :=
    (hproj 1 z s).trans
      ((congrArg (fun g : C(S, X) => g s) (H.toHomotopy.apply_one z)).trans
        (congrArg (fun g : C(S, X) => g s) (GenLoop.boundary b z hz)))
  have hc' : p c' = p c := hendproj q.pole
  have hend (s : S) : K (1, (z, s)) = c' :=
    hp.const_of_comp
      (K.continuous.comp (continuous_const.prodMk
        (continuous_const.prodMk continuous_id)))
      (fun s t => (hendproj s).trans (hendproj t).symm) s q.pole
  let B : GenLoop N C(S, E) (ContinuousMap.const S c') :=
    ⟨⟨fun v => ⟨fun s => K (1, (v, s)), by fun_prop⟩,
      ContinuousMap.continuous_of_continuous_uncurry _ (by
        change Continuous (fun v : (N → I) × S => K (1, (v.1, v.2)))
        fun_prop)⟩,
      fun v hv => by ext s; exact (hside 1 v hv s).trans (hend s)⟩
  let L : Path (ContinuousMap.const S c) (ContinuousMap.const S c') :=
    { toFun := fun t => ⟨fun s => K (t, (z, s)), by fun_prop⟩
      continuous_toFun := ContinuousMap.continuous_of_continuous_uncurry _ (by
        change Continuous (fun v : I × S => K (v.1, (z, v.2)))
        fun_prop)
      source' := by
        ext s
        exact (hstart z s).trans
          (congrArg (fun g : C(S, E) => g s) (GenLoop.boundary A z hz))
      target' := by ext s; exact hend s }
  refine ⟨c', hc', B, L, ?_, ?_, ?_⟩
  · exact ⟨{
      toFun := fun v => ⟨fun s => K (v.1, (v.2, s)), by fun_prop⟩
      continuous_toFun := ContinuousMap.continuous_of_continuous_uncurry _ (by
        change Continuous (fun v : (I × (N → I)) × S => K (v.1.1, (v.1.2, v.2)))
        fun_prop)
      map_zero_left := by intro v; ext s; exact hstart v s
      map_one_left := by intro v; rfl
      boundary_path := by intro t v; ext s; exact hside t v v.2 s }⟩
  · ext v s
    exact (hproj 1 v s).trans
      (congrArg (fun g : C(S, X) => g s) (H.toHomotopy.apply_one v))
  · intro t s
    exact (hproj t z s).trans
      (congrArg (fun g : C(S, X) => g s) (H.boundary_path t ⟨z, hz⟩))

end IsCoveringMap
