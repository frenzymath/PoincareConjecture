import PoincareConjecture.Proofs.M59.Mathlib.GenLoopTopology

set_option autoImplicit false

open scoped Topology unitInterval

namespace GenLoop

variable {N P S X : Type*} [TopologicalSpace S] [LocallyCompactSpace S]
  [TopologicalSpace X] {x : X}

def transpose (F : GenLoop N C(S, X) (ContinuousMap.const S x)) : C(S, GenLoop N X x) where
  toFun z := ⟨⟨fun v => F v z, (continuous_eval_const z).comp F.val.continuous⟩,
    fun v hv => congrArg (fun f : C(S, X) => f z) (GenLoop.boundary F v hv)⟩
  continuous_toFun := (ContinuousMap.continuous_of_continuous_uncurry _ (by
    change Continuous (fun v : S × (N → I) => F v.2 v.1)
    fun_prop)).subtype_mk _

def untranspose (F : C(S, GenLoop N X x)) : GenLoop N C(S, X) (ContinuousMap.const S x) :=
  ⟨⟨fun v => ⟨fun z => F z v, by fun_prop⟩,
      ContinuousMap.continuous_of_continuous_uncurry _ (by
        change Continuous (fun v : (N → I) × S => F v.2 v.1)
        fun_prop)⟩,
    fun v hv => by ext z; exact GenLoop.boundary (F z) v hv⟩

theorem untranspose_transpose (F : GenLoop N C(S, X) (ContinuousMap.const S x)) :
    untranspose (transpose F) = F := by ext v z; rfl

theorem transpose_untranspose (F : C(S, GenLoop N X x)) :
    transpose (untranspose F) = F := by ext z v; rfl

theorem transpose_homotopic
    {F G : GenLoop N C(S, X) (ContinuousMap.const S x)} (h : Homotopic F G) :
    (transpose F).Homotopic (transpose G) := by
  obtain ⟨H⟩ := h
  exact ⟨{
    toFun := fun q => ⟨⟨fun v => H (q.1, v) q.2, by fun_prop⟩,
      fun v hv => (congrArg (fun f : C(S, X) => f q.2) (H.eq_fst q.1 hv)).trans
        (congrArg (fun f : C(S, X) => f q.2) (GenLoop.boundary F v hv))⟩
    continuous_toFun :=
      (ContinuousMap.continuous_of_continuous_uncurry _ (by
        change Continuous (fun v : (I × S) × (N → I) => H (v.1.1, v.2) v.1.2)
        fun_prop)).subtype_mk _
    map_zero_left := by intro z; ext v; exact congrArg (fun f : C(S, X) => f z) (H.apply_zero v)
    map_one_left := by intro z; ext v; exact congrArg (fun f : C(S, X) => f z) (H.apply_one v) }⟩

omit [LocallyCompactSpace S] in

theorem untranspose_homotopic {F G : C(S, GenLoop N X x)} (h : F.Homotopic G) :
    Homotopic (untranspose F) (untranspose G) := by
  obtain ⟨H⟩ := h
  exact ⟨{
    toFun := fun q => ⟨fun z => H (q.1, z) q.2, by fun_prop⟩
    continuous_toFun := ContinuousMap.continuous_of_continuous_uncurry _ (by
      change Continuous (fun v : (I × (N → I)) × S => H (v.1.1, v.2) v.1.2)
      fun_prop)
    map_zero_left := by
      intro v; ext z
      exact congrArg (fun g : GenLoop N X x => g v) (H.apply_zero z)
    map_one_left := by
      intro v; ext z
      exact congrArg (fun g : GenLoop N X x => g v) (H.apply_one z)
    prop' := by
      intro t v hv
      ext z
      exact (GenLoop.boundary (H (t, z)) v hv).trans (GenLoop.boundary (F z) v hv).symm }⟩

theorem homotopic_iff_transpose_homotopic
    {F G : GenLoop N C(S, X) (ContinuousMap.const S x)} :
    Homotopic F G ↔ (transpose F).Homotopic (transpose G) := by
  refine ⟨transpose_homotopic, fun h => ?_⟩
  simpa only [untranspose_transpose] using untranspose_homotopic h

def swapNested (F : GenLoop N (GenLoop P X x) const) : GenLoop P (GenLoop N X x) const :=
  (genLoopGenLoopEquiv x).symm (congr x (Equiv.sumComm N P) (genLoopGenLoopEquiv x F))

theorem swapNested_apply (F : GenLoop N (GenLoop P X x) const) (v : P → I) (w : N → I) :
    swapNested F v w = F w v := rfl

theorem swapNested_swapNested (F : GenLoop N (GenLoop P X x) const) :
    swapNested (swapNested F) = F := by ext v w; rfl

theorem continuous_swapNested : Continuous (swapNested (N := N) (P := P) (x := x)) :=
  (genLoopGenLoopEquiv x).symm.continuous.comp
    ((congr x (Equiv.sumComm N P)).continuous.comp (genLoopGenLoopEquiv x).continuous)

theorem swapNested_homotopic {F G : GenLoop N (GenLoop P X x) const} (h : Homotopic F G) :
    Homotopic (swapNested F) (swapNested G) := by
  obtain ⟨p⟩ := homotopic_iff_nonempty_path.mp h
  exact homotopic_iff_nonempty_path.mpr ⟨p.map continuous_swapNested⟩

end GenLoop
